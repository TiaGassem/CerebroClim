# 🧠 CerebroClim

**Heatwave & Cold-Wave Brain Risk Simulator**

Free, open-access simulator of how **heat waves, cold waves, ozone, PM2.5 pollution and climate change 2050** affect the **blood-brain barrier** and **M1 microglial neuroinflammation**. Android, iPhone and PC. EN / FR / AR.

| Choose how to use it | Link |
|---|---|
| 🌐 **Web app (full screen)** | https://cerebroclim.streamlit.app/ |
| 📲 **Installable app + QR code (website)** | https://tiagassem.github.io/CerebroClim/ |

**Keywords:** heatwave brain risk, heat wave health, cold wave health, blood-brain barrier, neuroinflammation, microglia M1, ozone, PM2.5, climate change 2050, heat stroke prevention, ERA5, Open-Meteo, computational neuroscience.

## Features
Past · Present · Future comparison (ERA5, 7-day forecast, 2050) · interactive map and two-region comparison · ODE model with shear, cohorts, ozone/PM2.5 and vascular frailty · 48-hour prevention protocols · alerts (e-mail, push, WhatsApp) · PDF report · lessons, awareness toolkit, guide assistant, sources.

## Run locally
```bash
pip install -r requirements.txt
streamlit run app.py
```
E-mail alerts: copy `.streamlit/secrets.toml.example` into Streamlit Secrets.

## Disclaimer
Research and educational tool. Phenomenological model, not fitted to patient data. Not a medical device, diagnosis or medical advice.

## License & citation
© 2026 Tasnim (TiaGassem). All rights reserved; see `LICENSE` (free personal/educational/non-commercial research use with attribution; no copying, redistribution or commercial use without written permission) and `CITATION.cff`.
