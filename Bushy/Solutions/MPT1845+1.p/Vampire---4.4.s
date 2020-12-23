%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t12_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:27 EDT 2019

% Result     : Theorem 1.09s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       : 1787 (5470 expanded)
%              Number of leaves         :  343 (2330 expanded)
%              Depth                    :   24
%              Number of atoms          : 7846 (19620 expanded)
%              Number of equality atoms :  567 (2455 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7831,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f379,f386,f393,f400,f407,f414,f421,f428,f435,f442,f449,f456,f463,f470,f477,f484,f491,f498,f505,f512,f519,f526,f533,f540,f547,f554,f561,f568,f575,f582,f589,f596,f603,f610,f617,f624,f631,f638,f645,f652,f659,f666,f673,f680,f687,f694,f701,f708,f715,f722,f729,f736,f743,f750,f757,f764,f771,f801,f826,f843,f883,f912,f945,f983,f1004,f1033,f1053,f1056,f1085,f1097,f1104,f1207,f1249,f1256,f1272,f1357,f1364,f1371,f1378,f1385,f1392,f1399,f1406,f1413,f1420,f1433,f1440,f1465,f1573,f1580,f1587,f1673,f1736,f1956,f2081,f2167,f2204,f2250,f2320,f2372,f2419,f2459,f2514,f2521,f2528,f2541,f2548,f2572,f2585,f2592,f2605,f2613,f2626,f2633,f2646,f2653,f2660,f2673,f2687,f2700,f2707,f2714,f2727,f2734,f2747,f2754,f2761,f2774,f2781,f2788,f2795,f2811,f2818,f2823,f2830,f2873,f2882,f2895,f2902,f3091,f3419,f3435,f3455,f3480,f3526,f3537,f3553,f3556,f3585,f3592,f3606,f3635,f3638,f3667,f3670,f3699,f3709,f3731,f3751,f3797,f3832,f3840,f3847,f3888,f3902,f3921,f3934,f3943,f3961,f3979,f4005,f4024,f4043,f4103,f4196,f4206,f4291,f4301,f4308,f4311,f4387,f4408,f4409,f4412,f4485,f4506,f4515,f4585,f4606,f4614,f4680,f4684,f4705,f4708,f4779,f4800,f4810,f4881,f4902,f4914,f4985,f5006,f5020,f5090,f5111,f5129,f5195,f5216,f5234,f5302,f5721,f5763,f5809,f5840,f5895,f6044,f6137,f6163,f6270,f6307,f6311,f6339,f6346,f6391,f6398,f6445,f6452,f6454,f6455,f6474,f6481,f6488,f6495,f6647,f6792,f6793,f6795,f6796,f6797,f6816,f6817,f6818,f6819,f6820,f6835,f6836,f6837,f6838,f6857,f6858,f6859,f6860,f6890,f6892,f6893,f6894,f6895,f7056,f7057,f7061,f7091,f7092,f7093,f7106,f7107,f7108,f7109,f7116,f7120,f7135,f7151,f7158,f7208,f7233,f7286,f7299,f7306,f7319,f7340,f7348,f7446,f7448,f7548,f7578,f7579,f7580,f7613,f7637,f7681,f7725,f7767,f7809,f7817,f7822,f7824,f7826,f7829])).

fof(f7829,plain,
    ( ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_140
    | ~ spl22_382
    | ~ spl22_440
    | ~ spl22_442
    | ~ spl22_476 ),
    inference(avatar_contradiction_clause,[],[f7828])).

fof(f7828,plain,
    ( $false
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140
    | ~ spl22_382
    | ~ spl22_440
    | ~ spl22_442
    | ~ spl22_476 ),
    inference(subsumption_resolution,[],[f7827,f6886])).

fof(f6886,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | ~ spl22_476 ),
    inference(avatar_component_clause,[],[f6885])).

fof(f6885,plain,
    ( spl22_476
  <=> r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_476])])).

fof(f7827,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140
    | ~ spl22_382
    | ~ spl22_440
    | ~ spl22_442 ),
    inference(subsumption_resolution,[],[f7820,f6335])).

fof(f6335,plain,
    ( r2_hidden(k3_xboole_0(sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | ~ spl22_442 ),
    inference(avatar_component_clause,[],[f6334])).

fof(f6334,plain,
    ( spl22_442
  <=> r2_hidden(k3_xboole_0(sK10(sK1),sK11(sK1)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_442])])).

fof(f7820,plain,
    ( ~ r2_hidden(k3_xboole_0(sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140
    | ~ spl22_382
    | ~ spl22_440 ),
    inference(forward_demodulation,[],[f7819,f7472])).

fof(f7472,plain,
    ( ! [X1] : k3_xboole_0(X1,sK11(sK1)) = k9_subset_1(u1_struct_0(sK0),X1,sK11(sK1))
    | ~ spl22_440 ),
    inference(resolution,[],[f6306,f294])).

fof(f294,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f196])).

fof(f196,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f169])).

fof(f169,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',redefinition_k9_subset_1)).

fof(f6306,plain,
    ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl22_440 ),
    inference(avatar_component_clause,[],[f6305])).

fof(f6305,plain,
    ( spl22_440
  <=> m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_440])])).

fof(f7819,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f1240,f4679])).

fof(f4679,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl22_382 ),
    inference(avatar_component_clause,[],[f4678])).

fof(f4678,plain,
    ( spl22_382
  <=> r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_382])])).

fof(f1240,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(forward_demodulation,[],[f1239,f1209])).

fof(f1209,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl22_140 ),
    inference(equality_resolution,[],[f1206])).

fof(f1206,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_pre_topc(sK1) = X1 )
    | ~ spl22_140 ),
    inference(avatar_component_clause,[],[f1205])).

fof(f1205,plain,
    ( spl22_140
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_pre_topc(sK1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_140])])).

fof(f1239,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(forward_demodulation,[],[f1223,f1209])).

fof(f1223,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(backward_demodulation,[],[f1209,f1189])).

fof(f1189,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1188,f1096])).

fof(f1096,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl22_136 ),
    inference(avatar_component_clause,[],[f1095])).

fof(f1095,plain,
    ( spl22_136
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_136])])).

fof(f1188,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK9(sK1)),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1187,f1096])).

fof(f1187,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK9(sK1)),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1186,f392])).

fof(f392,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ spl22_5 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl22_5
  <=> ~ v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_5])])).

fof(f1186,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK9(sK1)),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1132,f378])).

fof(f378,plain,
    ( l1_pre_topc(sK1)
    | ~ spl22_0 ),
    inference(avatar_component_clause,[],[f377])).

fof(f377,plain,
    ( spl22_0
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_0])])).

fof(f1132,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK9(sK1)),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f324,f1096])).

fof(f324,plain,(
    ! [X0] :
      ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK10(X0),sK11(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK9(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f213,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f212])).

fof(f212,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f180])).

fof(f180,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f72])).

fof(f72,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',d1_pre_topc)).

fof(f7826,plain,
    ( ~ spl22_440
    | ~ spl22_442
    | spl22_511 ),
    inference(avatar_contradiction_clause,[],[f7825])).

fof(f7825,plain,
    ( $false
    | ~ spl22_440
    | ~ spl22_442
    | ~ spl22_511 ),
    inference(subsumption_resolution,[],[f6335,f7617])).

fof(f7617,plain,
    ( ~ r2_hidden(k3_xboole_0(sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | ~ spl22_440
    | ~ spl22_511 ),
    inference(forward_demodulation,[],[f7445,f7472])).

fof(f7445,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | ~ spl22_511 ),
    inference(avatar_component_clause,[],[f7444])).

fof(f7444,plain,
    ( spl22_511
  <=> ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_511])])).

fof(f7824,plain,
    ( ~ spl22_444
    | spl22_449 ),
    inference(avatar_contradiction_clause,[],[f7823])).

fof(f7823,plain,
    ( $false
    | ~ spl22_444
    | ~ spl22_449 ),
    inference(subsumption_resolution,[],[f7413,f6441])).

fof(f6441,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_449 ),
    inference(avatar_component_clause,[],[f6440])).

fof(f6440,plain,
    ( spl22_449
  <=> ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_449])])).

fof(f7413,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_444 ),
    inference(resolution,[],[f6390,f307])).

fof(f307,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f205])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f74])).

fof(f74,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',dt_g1_pre_topc)).

fof(f6390,plain,
    ( m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl22_444 ),
    inference(avatar_component_clause,[],[f6389])).

fof(f6389,plain,
    ( spl22_444
  <=> m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_444])])).

fof(f7822,plain,
    ( ~ spl22_444
    | spl22_451 ),
    inference(avatar_contradiction_clause,[],[f7821])).

fof(f7821,plain,
    ( $false
    | ~ spl22_444
    | ~ spl22_451 ),
    inference(subsumption_resolution,[],[f7412,f6448])).

fof(f6448,plain,
    ( ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_451 ),
    inference(avatar_component_clause,[],[f6447])).

fof(f6447,plain,
    ( spl22_451
  <=> ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_451])])).

fof(f7412,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_444 ),
    inference(resolution,[],[f6390,f306])).

fof(f306,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f205])).

fof(f7817,plain,
    ( ~ spl22_2
    | ~ spl22_6
    | ~ spl22_428
    | ~ spl22_430
    | ~ spl22_440
    | spl22_443
    | ~ spl22_446 ),
    inference(avatar_contradiction_clause,[],[f7816])).

fof(f7816,plain,
    ( $false
    | ~ spl22_2
    | ~ spl22_6
    | ~ spl22_428
    | ~ spl22_430
    | ~ spl22_440
    | ~ spl22_443
    | ~ spl22_446 ),
    inference(subsumption_resolution,[],[f7815,f5894])).

fof(f5894,plain,
    ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | ~ spl22_428 ),
    inference(avatar_component_clause,[],[f5893])).

fof(f5893,plain,
    ( spl22_428
  <=> r2_hidden(sK10(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_428])])).

fof(f7815,plain,
    ( ~ r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | ~ spl22_2
    | ~ spl22_6
    | ~ spl22_430
    | ~ spl22_440
    | ~ spl22_443
    | ~ spl22_446 ),
    inference(subsumption_resolution,[],[f7810,f6397])).

fof(f6397,plain,
    ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl22_446 ),
    inference(avatar_component_clause,[],[f6396])).

fof(f6396,plain,
    ( spl22_446
  <=> m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_446])])).

fof(f7810,plain,
    ( ~ m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | ~ spl22_2
    | ~ spl22_6
    | ~ spl22_430
    | ~ spl22_440
    | ~ spl22_443 ),
    inference(resolution,[],[f7668,f6338])).

fof(f6338,plain,
    ( ~ r2_hidden(k3_xboole_0(sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | ~ spl22_443 ),
    inference(avatar_component_clause,[],[f6337])).

fof(f6337,plain,
    ( spl22_443
  <=> ~ r2_hidden(k3_xboole_0(sK10(sK1),sK11(sK1)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_443])])).

fof(f7668,plain,
    ( ! [X0] :
        ( r2_hidden(k3_xboole_0(X0,sK11(sK1)),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,u1_pre_topc(sK0)) )
    | ~ spl22_2
    | ~ spl22_6
    | ~ spl22_430
    | ~ spl22_440 ),
    inference(subsumption_resolution,[],[f7667,f385])).

fof(f385,plain,
    ( v2_pre_topc(sK0)
    | ~ spl22_2 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl22_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_2])])).

fof(f7667,plain,
    ( ! [X0] :
        ( r2_hidden(k3_xboole_0(X0,sK11(sK1)),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ v2_pre_topc(sK0) )
    | ~ spl22_6
    | ~ spl22_430
    | ~ spl22_440 ),
    inference(subsumption_resolution,[],[f7666,f399])).

fof(f399,plain,
    ( l1_pre_topc(sK0)
    | ~ spl22_6 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl22_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_6])])).

fof(f7666,plain,
    ( ! [X0] :
        ( r2_hidden(k3_xboole_0(X0,sK11(sK1)),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl22_430
    | ~ spl22_440 ),
    inference(subsumption_resolution,[],[f7665,f6043])).

fof(f6043,plain,
    ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | ~ spl22_430 ),
    inference(avatar_component_clause,[],[f6042])).

fof(f6042,plain,
    ( spl22_430
  <=> r2_hidden(sK11(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_430])])).

fof(f7665,plain,
    ( ! [X0] :
        ( r2_hidden(k3_xboole_0(X0,sK11(sK1)),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl22_440 ),
    inference(subsumption_resolution,[],[f7664,f6306])).

fof(f7664,plain,
    ( ! [X0] :
        ( r2_hidden(k3_xboole_0(X0,sK11(sK1)),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl22_440 ),
    inference(superposition,[],[f325,f7472])).

fof(f325,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ r2_hidden(X2,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f7809,plain,
    ( spl22_528
    | ~ spl22_531
    | ~ spl22_278
    | ~ spl22_406 ),
    inference(avatar_split_clause,[],[f5071,f5004,f2816,f7807,f7801])).

fof(f7801,plain,
    ( spl22_528
  <=> u1_struct_0(sK18) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_528])])).

fof(f7807,plain,
    ( spl22_531
  <=> sK17 != sK18 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_531])])).

fof(f2816,plain,
    ( spl22_278
  <=> g1_pre_topc(k1_xboole_0,u1_pre_topc(sK17)) = sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_278])])).

fof(f5004,plain,
    ( spl22_406
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != sK18
        | u1_struct_0(sK18) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_406])])).

fof(f5071,plain,
    ( sK17 != sK18
    | u1_struct_0(sK18) = k1_xboole_0
    | ~ spl22_278
    | ~ spl22_406 ),
    inference(superposition,[],[f5005,f2817])).

fof(f2817,plain,
    ( g1_pre_topc(k1_xboole_0,u1_pre_topc(sK17)) = sK17
    | ~ spl22_278 ),
    inference(avatar_component_clause,[],[f2816])).

fof(f5005,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK18
        | u1_struct_0(sK18) = X0 )
    | ~ spl22_406 ),
    inference(avatar_component_clause,[],[f5004])).

fof(f7767,plain,
    ( spl22_524
    | ~ spl22_527
    | ~ spl22_160
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_398 ),
    inference(avatar_split_clause,[],[f4955,f4894,f2786,f1404,f1397,f7765,f7759])).

fof(f7759,plain,
    ( spl22_524
  <=> u1_struct_0(sK8) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_524])])).

fof(f7765,plain,
    ( spl22_527
  <=> sK8 != sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_527])])).

fof(f1397,plain,
    ( spl22_160
  <=> g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_160])])).

fof(f1404,plain,
    ( spl22_162
  <=> g1_pre_topc(u1_struct_0(sK17),u1_pre_topc(sK17)) = sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_162])])).

fof(f2786,plain,
    ( spl22_274
  <=> v1_xboole_0(u1_struct_0(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_274])])).

fof(f4894,plain,
    ( spl22_398
  <=> m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_398])])).

fof(f4955,plain,
    ( sK8 != sK17
    | u1_struct_0(sK8) = k1_xboole_0
    | ~ spl22_160
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_398 ),
    inference(forward_demodulation,[],[f4940,f1398])).

fof(f1398,plain,
    ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) = sK8
    | ~ spl22_160 ),
    inference(avatar_component_clause,[],[f1397])).

fof(f4940,plain,
    ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != sK17
    | u1_struct_0(sK8) = k1_xboole_0
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_398 ),
    inference(resolution,[],[f4895,f2801])).

fof(f2801,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
        | g1_pre_topc(X2,X3) != sK17
        | k1_xboole_0 = X2 )
    | ~ spl22_162
    | ~ spl22_274 ),
    inference(backward_demodulation,[],[f2798,f1680])).

fof(f1680,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != sK17
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
        | u1_struct_0(sK17) = X2 )
    | ~ spl22_162 ),
    inference(superposition,[],[f297,f1405])).

fof(f1405,plain,
    ( g1_pre_topc(u1_struct_0(sK17),u1_pre_topc(sK17)) = sK17
    | ~ spl22_162 ),
    inference(avatar_component_clause,[],[f1404])).

fof(f297,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f199])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f106])).

fof(f106,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',free_g1_pre_topc)).

fof(f2798,plain,
    ( u1_struct_0(sK17) = k1_xboole_0
    | ~ spl22_274 ),
    inference(resolution,[],[f2787,f301])).

fof(f301,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f200])).

fof(f200,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f176])).

fof(f176,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',t6_boole)).

fof(f2787,plain,
    ( v1_xboole_0(u1_struct_0(sK17))
    | ~ spl22_274 ),
    inference(avatar_component_clause,[],[f2786])).

fof(f4895,plain,
    ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | ~ spl22_398 ),
    inference(avatar_component_clause,[],[f4894])).

fof(f7725,plain,
    ( spl22_520
    | ~ spl22_523
    | ~ spl22_158
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_392 ),
    inference(avatar_split_clause,[],[f4853,f4792,f2786,f1404,f1390,f7723,f7717])).

fof(f7717,plain,
    ( spl22_520
  <=> u1_struct_0(sK7) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_520])])).

fof(f7723,plain,
    ( spl22_523
  <=> sK7 != sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_523])])).

fof(f1390,plain,
    ( spl22_158
  <=> g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_158])])).

fof(f4792,plain,
    ( spl22_392
  <=> m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_392])])).

fof(f4853,plain,
    ( sK7 != sK17
    | u1_struct_0(sK7) = k1_xboole_0
    | ~ spl22_158
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_392 ),
    inference(forward_demodulation,[],[f4836,f1391])).

fof(f1391,plain,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7
    | ~ spl22_158 ),
    inference(avatar_component_clause,[],[f1390])).

fof(f4836,plain,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) != sK17
    | u1_struct_0(sK7) = k1_xboole_0
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_392 ),
    inference(resolution,[],[f4793,f2801])).

fof(f4793,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ spl22_392 ),
    inference(avatar_component_clause,[],[f4792])).

fof(f7681,plain,
    ( spl22_516
    | ~ spl22_519
    | ~ spl22_156
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_386 ),
    inference(avatar_split_clause,[],[f4753,f4697,f2786,f1404,f1383,f7679,f7673])).

fof(f7673,plain,
    ( spl22_516
  <=> u1_struct_0(sK6) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_516])])).

fof(f7679,plain,
    ( spl22_519
  <=> sK6 != sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_519])])).

fof(f1383,plain,
    ( spl22_156
  <=> g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_156])])).

fof(f4697,plain,
    ( spl22_386
  <=> m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_386])])).

fof(f4753,plain,
    ( sK6 != sK17
    | u1_struct_0(sK6) = k1_xboole_0
    | ~ spl22_156
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_386 ),
    inference(forward_demodulation,[],[f4734,f1384])).

fof(f1384,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK6
    | ~ spl22_156 ),
    inference(avatar_component_clause,[],[f1383])).

fof(f4734,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) != sK17
    | u1_struct_0(sK6) = k1_xboole_0
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_386 ),
    inference(resolution,[],[f4698,f2801])).

fof(f4698,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ spl22_386 ),
    inference(avatar_component_clause,[],[f4697])).

fof(f7637,plain,
    ( spl22_428
    | spl22_488
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(avatar_split_clause,[],[f7367,f4678,f1254,f1095,f391,f377,f7156,f5893])).

fof(f7156,plain,
    ( spl22_488
  <=> g1_pre_topc(u1_struct_0(sK0),sK9(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_488])])).

fof(f1254,plain,
    ( spl22_144
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_144])])).

fof(f7367,plain,
    ( g1_pre_topc(u1_struct_0(sK0),sK9(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1))))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(forward_demodulation,[],[f7366,f1096])).

fof(f7366,plain,
    ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK1),sK9(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f7365,f4679])).

fof(f7365,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK1),sK9(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f7364,f1096])).

fof(f7364,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK1),sK9(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f7363,f1255])).

fof(f1255,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl22_144 ),
    inference(avatar_component_clause,[],[f1254])).

fof(f7363,plain,
    ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | g1_pre_topc(u1_struct_0(sK1),sK9(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f7362,f392])).

fof(f7362,plain,
    ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | g1_pre_topc(u1_struct_0(sK1),sK9(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))))
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f6024,f378])).

fof(f6024,plain,
    ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | g1_pre_topc(u1_struct_0(sK1),sK9(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))))
    | ~ spl22_144 ),
    inference(superposition,[],[f2144,f1255])).

fof(f2144,plain,(
    ! [X0] :
      ( r2_hidden(sK10(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | g1_pre_topc(u1_struct_0(X0),sK9(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),sK9(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK9(X0)))) ) ),
    inference(subsumption_resolution,[],[f2142,f986])).

fof(f986,plain,(
    ! [X2] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK9(X2)))
      | ~ l1_pre_topc(X2)
      | r2_hidden(sK10(X2),u1_pre_topc(X2))
      | v2_pre_topc(X2)
      | ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X2)) ) ),
    inference(resolution,[],[f314,f307])).

fof(f314,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK10(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f2142,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(sK10(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK9(X0)))
      | g1_pre_topc(u1_struct_0(X0),sK9(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),sK9(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK9(X0)))) ) ),
    inference(resolution,[],[f987,f302])).

fof(f302,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f202])).

fof(f202,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f201])).

fof(f201,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',abstractness_v1_pre_topc)).

fof(f987,plain,(
    ! [X3] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X3),sK9(X3)))
      | ~ l1_pre_topc(X3)
      | r2_hidden(sK10(X3),u1_pre_topc(X3))
      | v2_pre_topc(X3)
      | ~ r2_hidden(u1_struct_0(X3),u1_pre_topc(X3)) ) ),
    inference(resolution,[],[f314,f306])).

fof(f7613,plain,
    ( spl22_478
    | spl22_514
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382
    | ~ spl22_486 ),
    inference(avatar_split_clause,[],[f7457,f7149,f4678,f1254,f1095,f391,f377,f7611,f7059])).

fof(f7059,plain,
    ( spl22_478
  <=> ! [X0] : k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_478])])).

fof(f7611,plain,
    ( spl22_514
  <=> ! [X1] : k3_xboole_0(X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK0),sK10(sK1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_514])])).

fof(f7149,plain,
    ( spl22_486
  <=> ! [X1] : k3_xboole_0(X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK0),X1,sK10(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_486])])).

fof(f7457,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK0),sK10(sK1),X1)
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382
    | ~ spl22_486 ),
    inference(backward_demodulation,[],[f7150,f6076])).

fof(f6076,plain,
    ( ! [X0,X1] :
        ( k9_subset_1(u1_struct_0(sK0),X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK0),sK10(sK1),X1)
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(forward_demodulation,[],[f6075,f1096])).

fof(f6075,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1))
        | k9_subset_1(u1_struct_0(sK1),X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK1),sK10(sK1),X1) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(forward_demodulation,[],[f6074,f1096])).

fof(f6074,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1))
        | k9_subset_1(u1_struct_0(sK1),X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK1),sK10(sK1),X1) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f6073,f4679])).

fof(f6073,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1))
        | k9_subset_1(u1_struct_0(sK1),X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK1),sK10(sK1),X1) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f6072,f1255])).

fof(f6072,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1))
        | k9_subset_1(u1_struct_0(sK1),X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK1),sK10(sK1),X1) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f6071,f392])).

fof(f6071,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1))
        | k9_subset_1(u1_struct_0(sK1),X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK1),sK10(sK1),X1) )
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f6066,f378])).

fof(f6066,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
        | ~ l1_pre_topc(sK1)
        | v2_pre_topc(sK1)
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1))
        | k9_subset_1(u1_struct_0(sK1),X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK1),sK10(sK1),X1) )
    | ~ spl22_136 ),
    inference(superposition,[],[f2423,f1096])).

fof(f2423,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
      | ~ l1_pre_topc(X6)
      | v2_pre_topc(X6)
      | k3_xboole_0(X7,sK9(X6)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(X6)),X7,sK9(X6))
      | k9_subset_1(u1_struct_0(X6),X8,sK10(X6)) = k9_subset_1(u1_struct_0(X6),sK10(X6),X8) ) ),
    inference(resolution,[],[f1021,f293])).

fof(f293,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f195])).

fof(f195,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f71])).

fof(f71,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',commutativity_k9_subset_1)).

fof(f1021,plain,(
    ! [X6,X7] :
      ( m1_subset_1(sK10(X6),k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_pre_topc(X6)
      | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
      | v2_pre_topc(X6)
      | k3_xboole_0(X7,sK9(X6)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(X6)),X7,sK9(X6)) ) ),
    inference(resolution,[],[f328,f294])).

fof(f328,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK10(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f7150,plain,
    ( ! [X1] : k3_xboole_0(X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK0),X1,sK10(sK1))
    | ~ spl22_486 ),
    inference(avatar_component_clause,[],[f7149])).

fof(f7580,plain,
    ( spl22_440
    | spl22_512
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(avatar_split_clause,[],[f7452,f4678,f1254,f1095,f391,f377,f7546,f6305])).

fof(f7546,plain,
    ( spl22_512
  <=> ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK9(sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_512])])).

fof(f7452,plain,
    ( ! [X0] :
        ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK9(sK1),X0)
        | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f2480,f4679])).

fof(f2480,plain,
    ( ! [X0] :
        ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK9(sK1),X0)
        | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2479,f1096])).

fof(f2479,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2478,f1096])).

fof(f2478,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
        | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2477,f1255])).

fof(f2477,plain,
    ( ! [X0] :
        ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2476,f392])).

fof(f2476,plain,
    ( ! [X0] :
        ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2472,f378])).

fof(f2472,plain,
    ( ! [X0] :
        ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK1)
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_136 ),
    inference(superposition,[],[f1009,f1096])).

fof(f1009,plain,(
    ! [X4,X5] :
      ( m1_subset_1(sK11(X4),k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4)
      | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
      | v2_pre_topc(X4)
      | k9_subset_1(k1_zfmisc_1(u1_struct_0(X4)),X5,sK9(X4)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(X4)),sK9(X4),X5) ) ),
    inference(resolution,[],[f313,f293])).

fof(f313,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK11(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f7579,plain,
    ( spl22_446
    | spl22_512
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(avatar_split_clause,[],[f7451,f4678,f1254,f1095,f391,f377,f7546,f6396])).

fof(f7451,plain,
    ( ! [X0] :
        ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK9(sK1),X0)
        | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f2495,f4679])).

fof(f2495,plain,
    ( ! [X0] :
        ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK9(sK1),X0)
        | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2494,f1096])).

fof(f2494,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2493,f1096])).

fof(f2493,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
        | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2492,f1255])).

fof(f2492,plain,
    ( ! [X0] :
        ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2491,f392])).

fof(f2491,plain,
    ( ! [X0] :
        ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2487,f378])).

fof(f2487,plain,
    ( ! [X0] :
        ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK1)
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_136 ),
    inference(superposition,[],[f1020,f1096])).

fof(f1020,plain,(
    ! [X4,X5] :
      ( m1_subset_1(sK10(X4),k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4)
      | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
      | v2_pre_topc(X4)
      | k9_subset_1(k1_zfmisc_1(u1_struct_0(X4)),X5,sK9(X4)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(X4)),sK9(X4),X5) ) ),
    inference(resolution,[],[f328,f293])).

fof(f7578,plain,
    ( spl22_428
    | spl22_512
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(avatar_split_clause,[],[f7454,f4678,f1254,f1095,f391,f377,f7546,f5893])).

fof(f7454,plain,
    ( ! [X0] :
        ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK9(sK1),X0)
        | r2_hidden(sK10(sK1),u1_pre_topc(sK0)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f2458,f4679])).

fof(f2458,plain,
    ( ! [X0] :
        ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK9(sK1),X0)
        | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | r2_hidden(sK10(sK1),u1_pre_topc(sK0)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2457,f1096])).

fof(f2457,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | r2_hidden(sK10(sK1),u1_pre_topc(sK0))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2456,f1096])).

fof(f2456,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
        | r2_hidden(sK10(sK1),u1_pre_topc(sK0))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2455,f1255])).

fof(f2455,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2454,f392])).

fof(f2454,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2453,f378])).

fof(f2453,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK1)
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_144 ),
    inference(superposition,[],[f988,f1255])).

fof(f988,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK10(X4),u1_pre_topc(X4))
      | ~ l1_pre_topc(X4)
      | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
      | v2_pre_topc(X4)
      | k9_subset_1(k1_zfmisc_1(u1_struct_0(X4)),X5,sK9(X4)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(X4)),sK9(X4),X5) ) ),
    inference(resolution,[],[f314,f293])).

fof(f7548,plain,
    ( spl22_430
    | spl22_512
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(avatar_split_clause,[],[f7453,f4678,f1254,f1095,f391,f377,f7546,f6042])).

fof(f7453,plain,
    ( ! [X0] :
        ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK9(sK1),X0)
        | r2_hidden(sK11(sK1),u1_pre_topc(sK0)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f2465,f4679])).

fof(f2465,plain,
    ( ! [X0] :
        ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK9(sK1),X0)
        | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | r2_hidden(sK11(sK1),u1_pre_topc(sK0)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2464,f1096])).

fof(f2464,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2463,f1096])).

fof(f2463,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
        | r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2462,f1255])).

fof(f2462,plain,
    ( ! [X0] :
        ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2461,f392])).

fof(f2461,plain,
    ( ! [X0] :
        ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2460,f378])).

fof(f2460,plain,
    ( ! [X0] :
        ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK1)
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK9(sK1),X0) )
    | ~ spl22_144 ),
    inference(superposition,[],[f995,f1255])).

fof(f995,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK11(X4),u1_pre_topc(X4))
      | ~ l1_pre_topc(X4)
      | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
      | v2_pre_topc(X4)
      | k9_subset_1(k1_zfmisc_1(u1_struct_0(X4)),X5,sK9(X4)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(X4)),sK9(X4),X5) ) ),
    inference(resolution,[],[f315,f293])).

fof(f315,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK11(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f7448,plain,
    ( ~ spl22_427
    | ~ spl22_445
    | ~ spl22_2
    | ~ spl22_6
    | spl22_477 ),
    inference(avatar_split_clause,[],[f7388,f6888,f398,f384,f6386,f5884])).

fof(f5884,plain,
    ( spl22_427
  <=> ~ r1_tarski(sK9(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_427])])).

fof(f6386,plain,
    ( spl22_445
  <=> ~ m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_445])])).

fof(f6888,plain,
    ( spl22_477
  <=> ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_477])])).

fof(f7388,plain,
    ( ~ m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ spl22_2
    | ~ spl22_6
    | ~ spl22_477 ),
    inference(subsumption_resolution,[],[f7387,f385])).

fof(f7387,plain,
    ( ~ m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ spl22_6
    | ~ spl22_477 ),
    inference(subsumption_resolution,[],[f6891,f399])).

fof(f6891,plain,
    ( ~ m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl22_477 ),
    inference(resolution,[],[f6889,f329])).

fof(f329,plain,(
    ! [X0,X3] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X3,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f6889,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | ~ spl22_477 ),
    inference(avatar_component_clause,[],[f6888])).

fof(f7446,plain,
    ( ~ spl22_511
    | spl22_426
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_140
    | ~ spl22_382 ),
    inference(avatar_split_clause,[],[f7382,f4678,f1205,f1095,f391,f377,f5887,f7444])).

fof(f5887,plain,
    ( spl22_426
  <=> r1_tarski(sK9(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_426])])).

fof(f7382,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f1233,f4679])).

fof(f1233,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(forward_demodulation,[],[f1232,f1209])).

fof(f1232,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(forward_demodulation,[],[f1219,f1209])).

fof(f1219,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(backward_demodulation,[],[f1209,f1175])).

fof(f1175,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK1))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1174,f1096])).

fof(f1174,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1173,f392])).

fof(f1173,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1128,f378])).

fof(f1128,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f320,f1096])).

fof(f320,plain,(
    ! [X0] :
      ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK10(X0),sK11(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | r1_tarski(sK9(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f7348,plain,
    ( ~ spl22_0
    | ~ spl22_2
    | spl22_5
    | ~ spl22_6
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382
    | spl22_427
    | ~ spl22_428
    | ~ spl22_430
    | ~ spl22_440
    | spl22_443
    | ~ spl22_446 ),
    inference(avatar_contradiction_clause,[],[f7347])).

fof(f7347,plain,
    ( $false
    | ~ spl22_0
    | ~ spl22_2
    | ~ spl22_5
    | ~ spl22_6
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382
    | ~ spl22_427
    | ~ spl22_428
    | ~ spl22_430
    | ~ spl22_440
    | ~ spl22_443
    | ~ spl22_446 ),
    inference(subsumption_resolution,[],[f7346,f5894])).

fof(f7346,plain,
    ( ~ r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_2
    | ~ spl22_5
    | ~ spl22_6
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382
    | ~ spl22_427
    | ~ spl22_430
    | ~ spl22_440
    | ~ spl22_443
    | ~ spl22_446 ),
    inference(subsumption_resolution,[],[f7341,f6397])).

fof(f7341,plain,
    ( ~ m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_2
    | ~ spl22_5
    | ~ spl22_6
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382
    | ~ spl22_427
    | ~ spl22_430
    | ~ spl22_440
    | ~ spl22_443 ),
    inference(resolution,[],[f6384,f6338])).

fof(f6384,plain,
    ( ! [X0] :
        ( r2_hidden(k3_xboole_0(X0,sK11(sK1)),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,u1_pre_topc(sK0)) )
    | ~ spl22_0
    | ~ spl22_2
    | ~ spl22_5
    | ~ spl22_6
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382
    | ~ spl22_427
    | ~ spl22_430
    | ~ spl22_440 ),
    inference(subsumption_resolution,[],[f6383,f385])).

fof(f6383,plain,
    ( ! [X0] :
        ( r2_hidden(k3_xboole_0(X0,sK11(sK1)),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ v2_pre_topc(sK0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_6
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382
    | ~ spl22_427
    | ~ spl22_430
    | ~ spl22_440 ),
    inference(subsumption_resolution,[],[f6382,f399])).

fof(f6382,plain,
    ( ! [X0] :
        ( r2_hidden(k3_xboole_0(X0,sK11(sK1)),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382
    | ~ spl22_427
    | ~ spl22_430
    | ~ spl22_440 ),
    inference(subsumption_resolution,[],[f6381,f6043])).

fof(f6381,plain,
    ( ! [X0] :
        ( r2_hidden(k3_xboole_0(X0,sK11(sK1)),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382
    | ~ spl22_427
    | ~ spl22_440 ),
    inference(subsumption_resolution,[],[f6380,f6306])).

fof(f6380,plain,
    ( ! [X0] :
        ( r2_hidden(k3_xboole_0(X0,sK11(sK1)),u1_pre_topc(sK0))
        | ~ m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382
    | ~ spl22_427
    | ~ spl22_440 ),
    inference(superposition,[],[f325,f6329])).

fof(f6329,plain,
    ( ! [X0] : k3_xboole_0(X0,sK11(sK1)) = k9_subset_1(u1_struct_0(sK0),sK11(sK1),X0)
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382
    | ~ spl22_427
    | ~ spl22_440 ),
    inference(subsumption_resolution,[],[f6328,f5885])).

fof(f5885,plain,
    ( ~ r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ spl22_427 ),
    inference(avatar_component_clause,[],[f5884])).

fof(f6328,plain,
    ( ! [X0] :
        ( k3_xboole_0(X0,sK11(sK1)) = k9_subset_1(u1_struct_0(sK0),sK11(sK1),X0)
        | r1_tarski(sK9(sK1),u1_pre_topc(sK0)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382
    | ~ spl22_440 ),
    inference(subsumption_resolution,[],[f6319,f4679])).

fof(f6319,plain,
    ( ! [X0] :
        ( k3_xboole_0(X0,sK11(sK1)) = k9_subset_1(u1_struct_0(sK0),sK11(sK1),X0)
        | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | r1_tarski(sK9(sK1),u1_pre_topc(sK0)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_440 ),
    inference(backward_demodulation,[],[f6317,f2391])).

fof(f2391,plain,
    ( ! [X0] :
        ( k9_subset_1(u1_struct_0(sK0),X0,sK11(sK1)) = k9_subset_1(u1_struct_0(sK0),sK11(sK1),X0)
        | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | r1_tarski(sK9(sK1),u1_pre_topc(sK0)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2390,f1096])).

fof(f2390,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
        | k9_subset_1(u1_struct_0(sK1),X0,sK11(sK1)) = k9_subset_1(u1_struct_0(sK1),sK11(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2389,f1096])).

fof(f2389,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
        | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
        | k9_subset_1(u1_struct_0(sK1),X0,sK11(sK1)) = k9_subset_1(u1_struct_0(sK1),sK11(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2388,f1255])).

fof(f2388,plain,
    ( ! [X0] :
        ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | k9_subset_1(u1_struct_0(sK1),X0,sK11(sK1)) = k9_subset_1(u1_struct_0(sK1),sK11(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2387,f392])).

fof(f2387,plain,
    ( ! [X0] :
        ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k9_subset_1(u1_struct_0(sK1),X0,sK11(sK1)) = k9_subset_1(u1_struct_0(sK1),sK11(sK1),X0) )
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2386,f378])).

fof(f2386,plain,
    ( ! [X0] :
        ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | ~ l1_pre_topc(sK1)
        | v2_pre_topc(sK1)
        | k9_subset_1(u1_struct_0(sK1),X0,sK11(sK1)) = k9_subset_1(u1_struct_0(sK1),sK11(sK1),X0) )
    | ~ spl22_144 ),
    inference(superposition,[],[f962,f1255])).

fof(f962,plain,(
    ! [X4,X3] :
      ( r1_tarski(sK9(X3),u1_pre_topc(X3))
      | ~ r2_hidden(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ l1_pre_topc(X3)
      | v2_pre_topc(X3)
      | k9_subset_1(u1_struct_0(X3),X4,sK11(X3)) = k9_subset_1(u1_struct_0(X3),sK11(X3),X4) ) ),
    inference(resolution,[],[f317,f293])).

fof(f317,plain,(
    ! [X0] :
      ( m1_subset_1(sK11(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | r1_tarski(sK9(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f6317,plain,
    ( ! [X1] : k3_xboole_0(X1,sK11(sK1)) = k9_subset_1(u1_struct_0(sK0),X1,sK11(sK1))
    | ~ spl22_440 ),
    inference(resolution,[],[f6306,f294])).

fof(f7340,plain,
    ( spl22_506
    | ~ spl22_509
    | ~ spl22_152
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_378 ),
    inference(avatar_split_clause,[],[f4661,f4598,f2786,f1404,f1369,f7338,f7332])).

fof(f7332,plain,
    ( spl22_506
  <=> u1_struct_0(sK5) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_506])])).

fof(f7338,plain,
    ( spl22_509
  <=> sK5 != sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_509])])).

fof(f1369,plain,
    ( spl22_152
  <=> g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_152])])).

fof(f4598,plain,
    ( spl22_378
  <=> m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_378])])).

fof(f4661,plain,
    ( sK5 != sK17
    | u1_struct_0(sK5) = k1_xboole_0
    | ~ spl22_152
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_378 ),
    inference(forward_demodulation,[],[f4640,f1370])).

fof(f1370,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK5
    | ~ spl22_152 ),
    inference(avatar_component_clause,[],[f1369])).

fof(f4640,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != sK17
    | u1_struct_0(sK5) = k1_xboole_0
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_378 ),
    inference(resolution,[],[f4599,f2801])).

fof(f4599,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ spl22_378 ),
    inference(avatar_component_clause,[],[f4598])).

fof(f7319,plain,
    ( spl22_502
    | ~ spl22_505
    | ~ spl22_150
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_372 ),
    inference(avatar_split_clause,[],[f4564,f4498,f2786,f1404,f1362,f7317,f7311])).

fof(f7311,plain,
    ( spl22_502
  <=> u1_struct_0(sK4) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_502])])).

fof(f7317,plain,
    ( spl22_505
  <=> sK4 != sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_505])])).

fof(f1362,plain,
    ( spl22_150
  <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_150])])).

fof(f4498,plain,
    ( spl22_372
  <=> m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_372])])).

fof(f4564,plain,
    ( sK4 != sK17
    | u1_struct_0(sK4) = k1_xboole_0
    | ~ spl22_150
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_372 ),
    inference(forward_demodulation,[],[f4541,f1363])).

fof(f1363,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4
    | ~ spl22_150 ),
    inference(avatar_component_clause,[],[f1362])).

fof(f4541,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != sK17
    | u1_struct_0(sK4) = k1_xboole_0
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_372 ),
    inference(resolution,[],[f4499,f2801])).

fof(f4499,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ spl22_372 ),
    inference(avatar_component_clause,[],[f4498])).

fof(f7306,plain,
    ( ~ spl22_483
    | spl22_500
    | spl22_121
    | ~ spl22_292 ),
    inference(avatar_split_clause,[],[f3241,f2900,f841,f7304,f7104])).

fof(f7104,plain,
    ( spl22_483
  <=> ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_483])])).

fof(f7304,plain,
    ( spl22_500
  <=> m1_subset_1(sK13(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_500])])).

fof(f841,plain,
    ( spl22_121
  <=> ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_121])])).

fof(f2900,plain,
    ( spl22_292
  <=> u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_292])])).

fof(f3241,plain,
    ( m1_subset_1(sK13(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_121
    | ~ spl22_292 ),
    inference(subsumption_resolution,[],[f3118,f842])).

fof(f842,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_121 ),
    inference(avatar_component_clause,[],[f841])).

fof(f3118,plain,
    ( m1_subset_1(sK13(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_292 ),
    inference(superposition,[],[f340,f2901])).

fof(f2901,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_292 ),
    inference(avatar_component_clause,[],[f2900])).

fof(f340,plain,(
    ! [X0] :
      ( m1_subset_1(sK13(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f227])).

fof(f227,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f226])).

fof(f226,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f145])).

fof(f145,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',rc4_struct_0)).

fof(f7299,plain,
    ( spl22_496
    | ~ spl22_499
    | ~ spl22_148
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_366 ),
    inference(avatar_split_clause,[],[f4463,f4400,f2786,f1404,f1355,f7297,f7291])).

fof(f7291,plain,
    ( spl22_496
  <=> u1_struct_0(sK3) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_496])])).

fof(f7297,plain,
    ( spl22_499
  <=> sK3 != sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_499])])).

fof(f1355,plain,
    ( spl22_148
  <=> g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_148])])).

fof(f4400,plain,
    ( spl22_366
  <=> m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_366])])).

fof(f4463,plain,
    ( sK3 != sK17
    | u1_struct_0(sK3) = k1_xboole_0
    | ~ spl22_148
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_366 ),
    inference(forward_demodulation,[],[f4438,f1356])).

fof(f1356,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
    | ~ spl22_148 ),
    inference(avatar_component_clause,[],[f1355])).

fof(f4438,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != sK17
    | u1_struct_0(sK3) = k1_xboole_0
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_366 ),
    inference(resolution,[],[f4401,f2801])).

fof(f4401,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ spl22_366 ),
    inference(avatar_component_clause,[],[f4400])).

fof(f7286,plain,
    ( spl22_492
    | ~ spl22_495
    | ~ spl22_146
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_358 ),
    inference(avatar_split_clause,[],[f4364,f4293,f2786,f1404,f1270,f7284,f7278])).

fof(f7278,plain,
    ( spl22_492
  <=> u1_struct_0(sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_492])])).

fof(f7284,plain,
    ( spl22_495
  <=> sK2 != sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_495])])).

fof(f1270,plain,
    ( spl22_146
  <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_146])])).

fof(f4293,plain,
    ( spl22_358
  <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_358])])).

fof(f4364,plain,
    ( sK2 != sK17
    | u1_struct_0(sK2) = k1_xboole_0
    | ~ spl22_146
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_358 ),
    inference(forward_demodulation,[],[f4337,f1271])).

fof(f1271,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2
    | ~ spl22_146 ),
    inference(avatar_component_clause,[],[f1270])).

fof(f4337,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK17
    | u1_struct_0(sK2) = k1_xboole_0
    | ~ spl22_162
    | ~ spl22_274
    | ~ spl22_358 ),
    inference(resolution,[],[f4294,f2801])).

fof(f4294,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl22_358 ),
    inference(avatar_component_clause,[],[f4293])).

fof(f7233,plain,
    ( ~ spl22_483
    | spl22_490
    | spl22_121
    | ~ spl22_292 ),
    inference(avatar_split_clause,[],[f3240,f2900,f841,f7231,f7104])).

fof(f7231,plain,
    ( spl22_490
  <=> m1_subset_1(sK12(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_490])])).

fof(f3240,plain,
    ( m1_subset_1(sK12(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_121
    | ~ spl22_292 ),
    inference(subsumption_resolution,[],[f3117,f842])).

fof(f3117,plain,
    ( m1_subset_1(sK12(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_292 ),
    inference(superposition,[],[f337,f2901])).

fof(f337,plain,(
    ! [X0] :
      ( m1_subset_1(sK12(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f225])).

fof(f225,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f224])).

fof(f224,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f123])).

fof(f123,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',rc20_struct_0)).

fof(f7208,plain,
    ( spl22_480
    | ~ spl22_483
    | ~ spl22_187
    | ~ spl22_292 ),
    inference(avatar_split_clause,[],[f3127,f2900,f1954,f7104,f7095])).

fof(f7095,plain,
    ( spl22_480
  <=> v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_480])])).

fof(f1954,plain,
    ( spl22_187
  <=> ~ v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_187])])).

fof(f3127,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_292 ),
    inference(superposition,[],[f357,f2901])).

fof(f357,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f241])).

fof(f241,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f240])).

fof(f240,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f99])).

fof(f99,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',fc6_struct_0)).

fof(f7158,plain,
    ( spl22_430
    | spl22_488
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(avatar_split_clause,[],[f6033,f4678,f1254,f1095,f391,f377,f7156,f6042])).

fof(f6033,plain,
    ( g1_pre_topc(u1_struct_0(sK0),sK9(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1))))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(forward_demodulation,[],[f6032,f1096])).

fof(f6032,plain,
    ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK1),sK9(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f6031,f4679])).

fof(f6031,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK1),sK9(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f6030,f1096])).

fof(f6030,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK1),sK9(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f6029,f1255])).

fof(f6029,plain,
    ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | g1_pre_topc(u1_struct_0(sK1),sK9(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f6028,f392])).

fof(f6028,plain,
    ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | g1_pre_topc(u1_struct_0(sK1),sK9(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))))
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f6026,f378])).

fof(f6026,plain,
    ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | g1_pre_topc(u1_struct_0(sK1),sK9(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1))))
    | ~ spl22_144 ),
    inference(superposition,[],[f2161,f1255])).

fof(f2161,plain,(
    ! [X0] :
      ( r2_hidden(sK11(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | g1_pre_topc(u1_struct_0(X0),sK9(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),sK9(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK9(X0)))) ) ),
    inference(subsumption_resolution,[],[f2159,f993])).

fof(f993,plain,(
    ! [X2] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK9(X2)))
      | ~ l1_pre_topc(X2)
      | r2_hidden(sK11(X2),u1_pre_topc(X2))
      | v2_pre_topc(X2)
      | ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X2)) ) ),
    inference(resolution,[],[f315,f307])).

fof(f2159,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(sK11(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK9(X0)))
      | g1_pre_topc(u1_struct_0(X0),sK9(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),sK9(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK9(X0)))) ) ),
    inference(resolution,[],[f994,f302])).

fof(f994,plain,(
    ! [X3] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X3),sK9(X3)))
      | ~ l1_pre_topc(X3)
      | r2_hidden(sK11(X3),u1_pre_topc(X3))
      | v2_pre_topc(X3)
      | ~ r2_hidden(u1_struct_0(X3),u1_pre_topc(X3)) ) ),
    inference(resolution,[],[f315,f306])).

fof(f7151,plain,
    ( spl22_478
    | spl22_486
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(avatar_split_clause,[],[f5950,f4678,f1254,f1095,f391,f377,f7149,f7059])).

fof(f5950,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK0),X1,sK10(sK1))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(forward_demodulation,[],[f5949,f1096])).

fof(f5949,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1))
        | k3_xboole_0(X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK1),X1,sK10(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(forward_demodulation,[],[f5948,f1096])).

fof(f5948,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1))
        | k3_xboole_0(X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK1),X1,sK10(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f5947,f4679])).

fof(f5947,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1))
        | k3_xboole_0(X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK1),X1,sK10(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f5946,f1255])).

fof(f5946,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1))
        | k3_xboole_0(X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK1),X1,sK10(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f5945,f392])).

fof(f5945,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1))
        | k3_xboole_0(X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK1),X1,sK10(sK1)) )
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f5940,f378])).

fof(f5940,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
        | ~ l1_pre_topc(sK1)
        | v2_pre_topc(sK1)
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1))
        | k3_xboole_0(X1,sK10(sK1)) = k9_subset_1(u1_struct_0(sK1),X1,sK10(sK1)) )
    | ~ spl22_136 ),
    inference(superposition,[],[f2424,f1096])).

fof(f2424,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
      | ~ l1_pre_topc(X9)
      | v2_pre_topc(X9)
      | k3_xboole_0(X10,sK9(X9)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(X9)),X10,sK9(X9))
      | k3_xboole_0(X11,sK10(X9)) = k9_subset_1(u1_struct_0(X9),X11,sK10(X9)) ) ),
    inference(resolution,[],[f1021,f294])).

fof(f7135,plain,
    ( ~ spl22_114
    | spl22_483 ),
    inference(avatar_contradiction_clause,[],[f7134])).

fof(f7134,plain,
    ( $false
    | ~ spl22_114
    | ~ spl22_483 ),
    inference(subsumption_resolution,[],[f7133,f800])).

fof(f800,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_114 ),
    inference(avatar_component_clause,[],[f799])).

fof(f799,plain,
    ( spl22_114
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_114])])).

fof(f7133,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_483 ),
    inference(resolution,[],[f7105,f372])).

fof(f372,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f242])).

fof(f242,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f81])).

fof(f81,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',dt_l1_pre_topc)).

fof(f7105,plain,
    ( ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_483 ),
    inference(avatar_component_clause,[],[f7104])).

fof(f7120,plain,
    ( spl22_478
    | spl22_484
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(avatar_split_clause,[],[f5931,f4678,f1254,f1095,f391,f377,f7118,f7059])).

fof(f7118,plain,
    ( spl22_484
  <=> ! [X1] : k3_xboole_0(X1,sK11(sK1)) = k9_subset_1(u1_struct_0(sK0),X1,sK11(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_484])])).

fof(f5931,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X1,sK11(sK1)) = k9_subset_1(u1_struct_0(sK0),X1,sK11(sK1))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(forward_demodulation,[],[f5930,f1096])).

fof(f5930,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1))
        | k3_xboole_0(X1,sK11(sK1)) = k9_subset_1(u1_struct_0(sK1),X1,sK11(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(forward_demodulation,[],[f5929,f1096])).

fof(f5929,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1))
        | k3_xboole_0(X1,sK11(sK1)) = k9_subset_1(u1_struct_0(sK1),X1,sK11(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f5928,f4679])).

fof(f5928,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1))
        | k3_xboole_0(X1,sK11(sK1)) = k9_subset_1(u1_struct_0(sK1),X1,sK11(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f5927,f1255])).

fof(f5927,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1))
        | k3_xboole_0(X1,sK11(sK1)) = k9_subset_1(u1_struct_0(sK1),X1,sK11(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f5926,f392])).

fof(f5926,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1))
        | k3_xboole_0(X1,sK11(sK1)) = k9_subset_1(u1_struct_0(sK1),X1,sK11(sK1)) )
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f5921,f378])).

fof(f5921,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
        | ~ l1_pre_topc(sK1)
        | v2_pre_topc(sK1)
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1))
        | k3_xboole_0(X1,sK11(sK1)) = k9_subset_1(u1_struct_0(sK1),X1,sK11(sK1)) )
    | ~ spl22_136 ),
    inference(superposition,[],[f2402,f1096])).

fof(f2402,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
      | ~ l1_pre_topc(X9)
      | v2_pre_topc(X9)
      | k3_xboole_0(X10,sK9(X9)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(X9)),X10,sK9(X9))
      | k3_xboole_0(X11,sK11(X9)) = k9_subset_1(u1_struct_0(X9),X11,sK11(X9)) ) ),
    inference(resolution,[],[f1010,f294])).

fof(f1010,plain,(
    ! [X6,X7] :
      ( m1_subset_1(sK11(X6),k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_pre_topc(X6)
      | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
      | v2_pre_topc(X6)
      | k3_xboole_0(X7,sK9(X6)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(X6)),X7,sK9(X6)) ) ),
    inference(resolution,[],[f313,f294])).

fof(f7116,plain,
    ( ~ spl22_467
    | spl22_464
    | spl22_184
    | spl22_426
    | ~ spl22_383
    | spl22_462
    | ~ spl22_0
    | spl22_5
    | spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f3768,f1254,f1095,f832,f391,f377,f6802,f4675,f5887,f1948,f6808,f6814])).

fof(f6814,plain,
    ( spl22_467
  <=> ~ v1_zfmisc_1(sK11(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_467])])).

fof(f6808,plain,
    ( spl22_464
  <=> v1_xboole_0(sK11(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_464])])).

fof(f1948,plain,
    ( spl22_184
  <=> v7_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_184])])).

fof(f4675,plain,
    ( spl22_383
  <=> ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_383])])).

fof(f6802,plain,
    ( spl22_462
  <=> v1_subset_1(sK11(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_462])])).

fof(f832,plain,
    ( spl22_119
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_119])])).

fof(f3768,plain,
    ( v1_subset_1(sK11(sK1),u1_struct_0(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | v7_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3767,f1096])).

fof(f3767,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | v7_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3766,f1096])).

fof(f3766,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | v7_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3765,f1255])).

fof(f3765,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v7_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2437,f833])).

fof(f833,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl22_119 ),
    inference(avatar_component_clause,[],[f832])).

fof(f2437,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2436,f392])).

fof(f2436,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2435,f378])).

fof(f2435,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1)
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_144 ),
    inference(superposition,[],[f965,f1255])).

fof(f965,plain,(
    ! [X0] :
      ( r1_tarski(sK9(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK11(X0))
      | v1_subset_1(sK11(X0),u1_struct_0(X0))
      | ~ v1_zfmisc_1(sK11(X0)) ) ),
    inference(subsumption_resolution,[],[f959,f372])).

fof(f959,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | r1_tarski(sK9(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK11(X0))
      | v1_subset_1(sK11(X0),u1_struct_0(X0))
      | ~ v1_zfmisc_1(sK11(X0)) ) ),
    inference(resolution,[],[f317,f355])).

fof(f355,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | v1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_zfmisc_1(X1) ) ),
    inference(cnf_transformation,[],[f237])).

fof(f237,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
          | v1_subset_1(X1,u1_struct_0(X0))
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f236])).

fof(f236,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
          | v1_subset_1(X1,u1_struct_0(X0))
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f69])).

fof(f69,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) )
           => ( ~ v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',cc9_tex_2)).

fof(f7109,plain,
    ( spl22_466
    | spl22_464
    | ~ spl22_185
    | spl22_426
    | ~ spl22_383
    | spl22_462
    | ~ spl22_0
    | spl22_5
    | spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f3764,f1254,f1095,f832,f391,f377,f6802,f4675,f5887,f1945,f6808,f6811])).

fof(f6811,plain,
    ( spl22_466
  <=> v1_zfmisc_1(sK11(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_466])])).

fof(f1945,plain,
    ( spl22_185
  <=> ~ v7_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_185])])).

fof(f3764,plain,
    ( v1_subset_1(sK11(sK1),u1_struct_0(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3763,f1096])).

fof(f3763,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3762,f1096])).

fof(f3762,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3761,f1255])).

fof(f3761,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f3496,f833])).

fof(f3496,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f3495,f392])).

fof(f3495,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2443,f378])).

fof(f2443,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1)
    | ~ v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | v1_zfmisc_1(sK11(sK1))
    | ~ spl22_144 ),
    inference(superposition,[],[f966,f1255])).

fof(f966,plain,(
    ! [X1] :
      ( r1_tarski(sK9(X1),u1_pre_topc(X1))
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | v2_pre_topc(X1)
      | ~ v7_struct_0(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(sK11(X1))
      | v1_subset_1(sK11(X1),u1_struct_0(X1))
      | v1_zfmisc_1(sK11(X1)) ) ),
    inference(subsumption_resolution,[],[f960,f372])).

fof(f960,plain,(
    ! [X1] :
      ( ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
      | r1_tarski(sK9(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | v2_pre_topc(X1)
      | ~ v7_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(sK11(X1))
      | v1_subset_1(sK11(X1),u1_struct_0(X1))
      | v1_zfmisc_1(sK11(X1)) ) ),
    inference(resolution,[],[f317,f335])).

fof(f335,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | v1_subset_1(X1,u1_struct_0(X0))
      | v1_zfmisc_1(X1) ) ),
    inference(cnf_transformation,[],[f221])).

fof(f221,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
          | v1_subset_1(X1,u1_struct_0(X0))
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f220])).

fof(f220,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
          | v1_subset_1(X1,u1_struct_0(X0))
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f63])).

fof(f63,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) )
           => ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',cc7_tex_2)).

fof(f7108,plain,
    ( ~ spl22_471
    | spl22_472
    | spl22_184
    | spl22_426
    | ~ spl22_383
    | spl22_474
    | ~ spl22_0
    | spl22_5
    | spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f3760,f1254,f1095,f832,f391,f377,f6855,f4675,f5887,f1948,f6849,f6843])).

fof(f6843,plain,
    ( spl22_471
  <=> ~ v1_zfmisc_1(sK10(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_471])])).

fof(f6849,plain,
    ( spl22_472
  <=> v1_xboole_0(sK10(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_472])])).

fof(f6855,plain,
    ( spl22_474
  <=> v1_subset_1(sK10(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_474])])).

fof(f3760,plain,
    ( v1_subset_1(sK10(sK1),u1_struct_0(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | v7_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3759,f1096])).

fof(f3759,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | v7_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3758,f1096])).

fof(f3758,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | v7_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3757,f1255])).

fof(f3757,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v7_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2446,f833])).

fof(f2446,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2445,f392])).

fof(f2445,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2444,f378])).

fof(f2444,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1)
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_144 ),
    inference(superposition,[],[f974,f1255])).

fof(f974,plain,(
    ! [X0] :
      ( r1_tarski(sK9(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK10(X0))
      | v1_subset_1(sK10(X0),u1_struct_0(X0))
      | ~ v1_zfmisc_1(sK10(X0)) ) ),
    inference(subsumption_resolution,[],[f968,f372])).

fof(f968,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | r1_tarski(sK9(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK10(X0))
      | v1_subset_1(sK10(X0),u1_struct_0(X0))
      | ~ v1_zfmisc_1(sK10(X0)) ) ),
    inference(resolution,[],[f327,f355])).

fof(f327,plain,(
    ! [X0] :
      ( m1_subset_1(sK10(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | r1_tarski(sK9(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f7107,plain,
    ( spl22_470
    | spl22_472
    | ~ spl22_185
    | spl22_426
    | ~ spl22_383
    | spl22_474
    | ~ spl22_0
    | spl22_5
    | spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f3756,f1254,f1095,f832,f391,f377,f6855,f4675,f5887,f1945,f6849,f6840])).

fof(f6840,plain,
    ( spl22_470
  <=> v1_zfmisc_1(sK10(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_470])])).

fof(f3756,plain,
    ( v1_subset_1(sK10(sK1),u1_struct_0(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3755,f1096])).

fof(f3755,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3754,f1096])).

fof(f3754,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3753,f1255])).

fof(f3753,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f3504,f833])).

fof(f3504,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f3503,f392])).

fof(f3503,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2452,f378])).

fof(f2452,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1)
    | ~ v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | v1_zfmisc_1(sK10(sK1))
    | ~ spl22_144 ),
    inference(superposition,[],[f975,f1255])).

fof(f975,plain,(
    ! [X1] :
      ( r1_tarski(sK9(X1),u1_pre_topc(X1))
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | v2_pre_topc(X1)
      | ~ v7_struct_0(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(sK10(X1))
      | v1_subset_1(sK10(X1),u1_struct_0(X1))
      | v1_zfmisc_1(sK10(X1)) ) ),
    inference(subsumption_resolution,[],[f969,f372])).

fof(f969,plain,(
    ! [X1] :
      ( ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
      | r1_tarski(sK9(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | v2_pre_topc(X1)
      | ~ v7_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(sK10(X1))
      | v1_subset_1(sK10(X1),u1_struct_0(X1))
      | v1_zfmisc_1(sK10(X1)) ) ),
    inference(resolution,[],[f327,f335])).

fof(f7106,plain,
    ( ~ spl22_481
    | ~ spl22_483
    | spl22_186
    | ~ spl22_292 ),
    inference(avatar_split_clause,[],[f3114,f2900,f1951,f7104,f7098])).

fof(f7098,plain,
    ( spl22_481
  <=> ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_481])])).

fof(f1951,plain,
    ( spl22_186
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_186])])).

fof(f3114,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_292 ),
    inference(superposition,[],[f334,f2901])).

fof(f334,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f219])).

fof(f219,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f218])).

fof(f218,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f102])).

fof(f102,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',fc7_struct_0)).

fof(f7093,plain,
    ( spl22_446
    | ~ spl22_383
    | spl22_478
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f2434,f1254,f1095,f391,f377,f7059,f4675,f6396])).

fof(f2434,plain,
    ( ! [X0] :
        ( k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1))
        | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2433,f1096])).

fof(f2433,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2432,f1096])).

fof(f2432,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
        | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2431,f1255])).

fof(f2431,plain,
    ( ! [X0] :
        ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2430,f392])).

fof(f2430,plain,
    ( ! [X0] :
        ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2426,f378])).

fof(f2426,plain,
    ( ! [X0] :
        ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK1)
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_136 ),
    inference(superposition,[],[f1021,f1096])).

fof(f7092,plain,
    ( spl22_440
    | ~ spl22_383
    | spl22_478
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f2412,f1254,f1095,f391,f377,f7059,f4675,f6305])).

fof(f2412,plain,
    ( ! [X0] :
        ( k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1))
        | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2411,f1096])).

fof(f2411,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2410,f1096])).

fof(f2410,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
        | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2409,f1255])).

fof(f2409,plain,
    ( ! [X0] :
        ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2408,f392])).

fof(f2408,plain,
    ( ! [X0] :
        ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2404,f378])).

fof(f2404,plain,
    ( ! [X0] :
        ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK1)
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_136 ),
    inference(superposition,[],[f1010,f1096])).

fof(f7091,plain,
    ( spl22_430
    | ~ spl22_383
    | spl22_478
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f2385,f1254,f1095,f391,f377,f7059,f4675,f6042])).

fof(f2385,plain,
    ( ! [X0] :
        ( k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1))
        | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | r2_hidden(sK11(sK1),u1_pre_topc(sK0)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2384,f1096])).

fof(f2384,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2383,f1096])).

fof(f2383,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
        | r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2382,f1255])).

fof(f2382,plain,
    ( ! [X0] :
        ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2381,f392])).

fof(f2381,plain,
    ( ! [X0] :
        ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2380,f378])).

fof(f2380,plain,
    ( ! [X0] :
        ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK1)
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_144 ),
    inference(superposition,[],[f996,f1255])).

fof(f996,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK11(X6),u1_pre_topc(X6))
      | ~ l1_pre_topc(X6)
      | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
      | v2_pre_topc(X6)
      | k3_xboole_0(X7,sK9(X6)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(X6)),X7,sK9(X6)) ) ),
    inference(resolution,[],[f315,f294])).

fof(f7061,plain,
    ( spl22_428
    | ~ spl22_383
    | spl22_478
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f2379,f1254,f1095,f391,f377,f7059,f4675,f5893])).

fof(f2379,plain,
    ( ! [X0] :
        ( k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK9(sK1))
        | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | r2_hidden(sK10(sK1),u1_pre_topc(sK0)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2378,f1096])).

fof(f2378,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | r2_hidden(sK10(sK1),u1_pre_topc(sK0))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2377,f1096])).

fof(f2377,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
        | r2_hidden(sK10(sK1),u1_pre_topc(sK0))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2376,f1255])).

fof(f2376,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2375,f392])).

fof(f2375,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2374,f378])).

fof(f2374,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK1)
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_pre_topc(sK1)
        | k3_xboole_0(X0,sK9(sK1)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X0,sK9(sK1)) )
    | ~ spl22_144 ),
    inference(superposition,[],[f989,f1255])).

fof(f989,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK10(X6),u1_pre_topc(X6))
      | ~ l1_pre_topc(X6)
      | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
      | v2_pre_topc(X6)
      | k3_xboole_0(X7,sK9(X6)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(X6)),X7,sK9(X6)) ) ),
    inference(resolution,[],[f314,f294])).

fof(f7057,plain,
    ( spl22_464
    | ~ spl22_185
    | spl22_426
    | ~ spl22_383
    | ~ spl22_463
    | ~ spl22_0
    | spl22_5
    | spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f3776,f1254,f1095,f832,f391,f377,f6799,f4675,f5887,f1945,f6808])).

fof(f6799,plain,
    ( spl22_463
  <=> ~ v1_subset_1(sK11(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_463])])).

fof(f3776,plain,
    ( ~ v1_subset_1(sK11(sK1),u1_struct_0(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3775,f1096])).

fof(f3775,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | ~ v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3774,f1096])).

fof(f3774,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | ~ v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3773,f1255])).

fof(f3773,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | ~ v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f3482,f833])).

fof(f3482,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | ~ v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f3481,f392])).

fof(f3481,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | ~ v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2365,f378])).

fof(f2365,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1)
    | ~ v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | ~ v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ spl22_144 ),
    inference(superposition,[],[f967,f1255])).

fof(f967,plain,(
    ! [X2] :
      ( r1_tarski(sK9(X2),u1_pre_topc(X2))
      | ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ l1_pre_topc(X2)
      | v2_pre_topc(X2)
      | ~ v7_struct_0(X2)
      | v2_struct_0(X2)
      | v1_xboole_0(sK11(X2))
      | ~ v1_subset_1(sK11(X2),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f961,f372])).

fof(f961,plain,(
    ! [X2] :
      ( ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X2))
      | r1_tarski(sK9(X2),u1_pre_topc(X2))
      | ~ l1_pre_topc(X2)
      | v2_pre_topc(X2)
      | ~ v7_struct_0(X2)
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2)
      | v1_xboole_0(sK11(X2))
      | ~ v1_subset_1(sK11(X2),u1_struct_0(X2)) ) ),
    inference(resolution,[],[f317,f336])).

fof(f336,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f223])).

fof(f223,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f222])).

fof(f222,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f57,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ v1_xboole_0(X1)
           => ( ~ v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',cc6_tex_2)).

fof(f7056,plain,
    ( spl22_472
    | ~ spl22_185
    | spl22_426
    | ~ spl22_383
    | ~ spl22_475
    | ~ spl22_0
    | spl22_5
    | spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f3772,f1254,f1095,f832,f391,f377,f6852,f4675,f5887,f1945,f6849])).

fof(f6852,plain,
    ( spl22_475
  <=> ~ v1_subset_1(sK10(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_475])])).

fof(f3772,plain,
    ( ~ v1_subset_1(sK10(sK1),u1_struct_0(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3771,f1096])).

fof(f3771,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | ~ v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3770,f1096])).

fof(f3770,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | ~ v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f3769,f1255])).

fof(f3769,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | ~ v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f3489,f833])).

fof(f3489,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | ~ v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f3488,f392])).

fof(f3488,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | ~ v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f2373,f378])).

fof(f2373,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1)
    | ~ v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | ~ v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ spl22_144 ),
    inference(superposition,[],[f976,f1255])).

fof(f976,plain,(
    ! [X2] :
      ( r1_tarski(sK9(X2),u1_pre_topc(X2))
      | ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ l1_pre_topc(X2)
      | v2_pre_topc(X2)
      | ~ v7_struct_0(X2)
      | v2_struct_0(X2)
      | v1_xboole_0(sK10(X2))
      | ~ v1_subset_1(sK10(X2),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f970,f372])).

fof(f970,plain,(
    ! [X2] :
      ( ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X2))
      | r1_tarski(sK9(X2),u1_pre_topc(X2))
      | ~ l1_pre_topc(X2)
      | v2_pre_topc(X2)
      | ~ v7_struct_0(X2)
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2)
      | v1_xboole_0(sK10(X2))
      | ~ v1_subset_1(sK10(X2),u1_struct_0(X2)) ) ),
    inference(resolution,[],[f327,f336])).

fof(f6895,plain,
    ( spl22_446
    | ~ spl22_477
    | ~ spl22_383
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(avatar_split_clause,[],[f1241,f1205,f1095,f391,f377,f4675,f6888,f6396])).

fof(f1241,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(forward_demodulation,[],[f1224,f1209])).

fof(f1224,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(backward_demodulation,[],[f1209,f1193])).

fof(f1193,plain,
    ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1192,f1096])).

fof(f1192,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1191,f1096])).

fof(f1191,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1190,f392])).

fof(f1190,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1)
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1134,f378])).

fof(f1134,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f326,f1096])).

fof(f326,plain,(
    ! [X0] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK9(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK10(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f6894,plain,
    ( spl22_440
    | ~ spl22_477
    | ~ spl22_383
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(avatar_split_clause,[],[f1234,f1205,f1095,f391,f377,f4675,f6888,f6305])).

fof(f1234,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(forward_demodulation,[],[f1220,f1209])).

fof(f1220,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(backward_demodulation,[],[f1209,f1179])).

fof(f1179,plain,
    ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1178,f1096])).

fof(f1178,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1177,f1096])).

fof(f1177,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1176,f392])).

fof(f1176,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1)
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1129,f378])).

fof(f1129,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f321,f1096])).

fof(f321,plain,(
    ! [X0] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK9(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK11(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f6893,plain,
    ( spl22_474
    | spl22_472
    | ~ spl22_471
    | ~ spl22_432
    | ~ spl22_446 ),
    inference(avatar_split_clause,[],[f6399,f6396,f6161,f6843,f6849,f6855])).

fof(f6161,plain,
    ( spl22_432
  <=> ! [X5] :
        ( v1_subset_1(X5,u1_struct_0(sK0))
        | ~ v1_zfmisc_1(X5)
        | v1_xboole_0(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_432])])).

fof(f6399,plain,
    ( ~ v1_zfmisc_1(sK10(sK1))
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK0))
    | ~ spl22_432
    | ~ spl22_446 ),
    inference(resolution,[],[f6397,f6162])).

fof(f6162,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_zfmisc_1(X5)
        | v1_xboole_0(X5)
        | v1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl22_432 ),
    inference(avatar_component_clause,[],[f6161])).

fof(f6892,plain,
    ( ~ spl22_477
    | ~ spl22_383
    | spl22_430
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(avatar_split_clause,[],[f1238,f1205,f1095,f391,f377,f6042,f4675,f6888])).

fof(f1238,plain,
    ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(forward_demodulation,[],[f1237,f1209])).

fof(f1237,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(forward_demodulation,[],[f1222,f1209])).

fof(f1222,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(backward_demodulation,[],[f1209,f1185])).

fof(f1185,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1184,f1096])).

fof(f1184,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1183,f392])).

fof(f1183,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1131,f378])).

fof(f1131,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f323,f1096])).

fof(f323,plain,(
    ! [X0] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK9(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK11(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f6890,plain,
    ( ~ spl22_477
    | ~ spl22_383
    | spl22_428
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(avatar_split_clause,[],[f1236,f1205,f1095,f391,f377,f5893,f4675,f6888])).

fof(f1236,plain,
    ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(forward_demodulation,[],[f1235,f1209])).

fof(f1235,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(forward_demodulation,[],[f1221,f1209])).

fof(f1221,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(backward_demodulation,[],[f1209,f1182])).

fof(f1182,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1181,f1096])).

fof(f1181,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1180,f392])).

fof(f1180,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1130,f378])).

fof(f1130,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK9(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f322,f1096])).

fof(f322,plain,(
    ! [X0] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK9(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK10(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f6860,plain,
    ( spl22_444
    | spl22_446
    | ~ spl22_383
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(avatar_split_clause,[],[f1226,f1205,f1095,f391,f377,f4675,f6396,f6389])).

fof(f1226,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(backward_demodulation,[],[f1209,f1200])).

fof(f1200,plain,
    ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1199,f1096])).

fof(f1199,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1198,f1096])).

fof(f1198,plain,
    ( m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1197,f392])).

fof(f1197,plain,
    ( m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1)
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1136,f378])).

fof(f1136,plain,
    ( m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f328,f1096])).

fof(f6859,plain,
    ( spl22_444
    | spl22_440
    | ~ spl22_383
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(avatar_split_clause,[],[f1214,f1205,f1095,f391,f377,f4675,f6305,f6389])).

fof(f1214,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(backward_demodulation,[],[f1209,f1159])).

fof(f1159,plain,
    ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1158,f1096])).

fof(f1158,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1157,f1096])).

fof(f1157,plain,
    ( m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1156,f392])).

fof(f1156,plain,
    ( m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1)
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1123,f378])).

fof(f1123,plain,
    ( m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f313,f1096])).

fof(f6858,plain,
    ( ~ spl22_471
    | spl22_472
    | spl22_450
    | spl22_474
    | ~ spl22_0
    | spl22_5
    | spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | spl22_185
    | ~ spl22_382 ),
    inference(avatar_split_clause,[],[f5882,f4678,f1945,f1254,f1095,f832,f391,f377,f6855,f6450,f6849,f6843])).

fof(f6450,plain,
    ( spl22_450
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_450])])).

fof(f5882,plain,
    ( v1_subset_1(sK10(sK1),u1_struct_0(sK0))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(sK10(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_185
    | ~ spl22_382 ),
    inference(forward_demodulation,[],[f5881,f1096])).

fof(f5881,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_185
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f5880,f4679])).

fof(f5880,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_185 ),
    inference(forward_demodulation,[],[f5879,f1096])).

fof(f5879,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_185 ),
    inference(forward_demodulation,[],[f5878,f1255])).

fof(f5878,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_185 ),
    inference(subsumption_resolution,[],[f5877,f833])).

fof(f5877,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_185 ),
    inference(subsumption_resolution,[],[f5876,f1946])).

fof(f1946,plain,
    ( ~ v7_struct_0(sK1)
    | ~ spl22_185 ),
    inference(avatar_component_clause,[],[f1945])).

fof(f5876,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f5875,f378])).

fof(f5875,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f5872,f392])).

fof(f5872,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_136 ),
    inference(superposition,[],[f2227,f1096])).

fof(f2227,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK9(X0)))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK10(X0))
      | v1_subset_1(sK10(X0),u1_struct_0(X0))
      | ~ v1_zfmisc_1(sK10(X0)) ) ),
    inference(subsumption_resolution,[],[f2220,f372])).

fof(f2220,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK9(X0)))
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK10(X0))
      | v1_subset_1(sK10(X0),u1_struct_0(X0))
      | ~ v1_zfmisc_1(sK10(X0)) ) ),
    inference(resolution,[],[f1019,f355])).

fof(f1019,plain,(
    ! [X3] :
      ( m1_subset_1(sK10(X3),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | ~ r2_hidden(u1_struct_0(X3),u1_pre_topc(X3))
      | v2_pre_topc(X3)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X3),sK9(X3))) ) ),
    inference(resolution,[],[f328,f306])).

fof(f6857,plain,
    ( ~ spl22_471
    | spl22_472
    | spl22_448
    | spl22_474
    | ~ spl22_0
    | spl22_5
    | spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | spl22_185
    | ~ spl22_382 ),
    inference(avatar_split_clause,[],[f5856,f4678,f1945,f1254,f1095,f832,f391,f377,f6855,f6443,f6849,f6843])).

fof(f6443,plain,
    ( spl22_448
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_448])])).

fof(f5856,plain,
    ( v1_subset_1(sK10(sK1),u1_struct_0(sK0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(sK10(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_185
    | ~ spl22_382 ),
    inference(forward_demodulation,[],[f5855,f1096])).

fof(f5855,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_185
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f5854,f4679])).

fof(f5854,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_185 ),
    inference(forward_demodulation,[],[f5853,f1096])).

fof(f5853,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_185 ),
    inference(forward_demodulation,[],[f5852,f1255])).

fof(f5852,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_185 ),
    inference(subsumption_resolution,[],[f5851,f833])).

fof(f5851,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_185 ),
    inference(subsumption_resolution,[],[f5850,f1946])).

fof(f5850,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f5849,f378])).

fof(f5849,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f5847,f392])).

fof(f5847,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK10(sK1))
    | v1_subset_1(sK10(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK10(sK1))
    | ~ spl22_136 ),
    inference(superposition,[],[f2212,f1096])).

fof(f2212,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK9(X0)))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK10(X0))
      | v1_subset_1(sK10(X0),u1_struct_0(X0))
      | ~ v1_zfmisc_1(sK10(X0)) ) ),
    inference(subsumption_resolution,[],[f2205,f372])).

fof(f2205,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK9(X0)))
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK10(X0))
      | v1_subset_1(sK10(X0),u1_struct_0(X0))
      | ~ v1_zfmisc_1(sK10(X0)) ) ),
    inference(resolution,[],[f1018,f355])).

fof(f1018,plain,(
    ! [X2] :
      ( m1_subset_1(sK10(X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X2))
      | v2_pre_topc(X2)
      | l1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK9(X2))) ) ),
    inference(resolution,[],[f328,f307])).

fof(f6838,plain,
    ( ~ spl22_467
    | spl22_464
    | spl22_450
    | spl22_462
    | ~ spl22_0
    | spl22_5
    | spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | spl22_185
    | ~ spl22_382 ),
    inference(avatar_split_clause,[],[f5835,f4678,f1945,f1254,f1095,f832,f391,f377,f6802,f6450,f6808,f6814])).

fof(f5835,plain,
    ( v1_subset_1(sK11(sK1),u1_struct_0(sK0))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(sK11(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_185
    | ~ spl22_382 ),
    inference(forward_demodulation,[],[f5834,f1096])).

fof(f5834,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_185
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f5833,f4679])).

fof(f5833,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_185 ),
    inference(forward_demodulation,[],[f5832,f1096])).

fof(f5832,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_185 ),
    inference(forward_demodulation,[],[f5831,f1255])).

fof(f5831,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_185 ),
    inference(subsumption_resolution,[],[f5830,f833])).

fof(f5830,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_185 ),
    inference(subsumption_resolution,[],[f5829,f1946])).

fof(f5829,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f5828,f378])).

fof(f5828,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f5825,f392])).

fof(f5825,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_136 ),
    inference(superposition,[],[f2196,f1096])).

fof(f2196,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK9(X0)))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK11(X0))
      | v1_subset_1(sK11(X0),u1_struct_0(X0))
      | ~ v1_zfmisc_1(sK11(X0)) ) ),
    inference(subsumption_resolution,[],[f2189,f372])).

fof(f2189,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK9(X0)))
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK11(X0))
      | v1_subset_1(sK11(X0),u1_struct_0(X0))
      | ~ v1_zfmisc_1(sK11(X0)) ) ),
    inference(resolution,[],[f1008,f355])).

fof(f1008,plain,(
    ! [X3] :
      ( m1_subset_1(sK11(X3),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | ~ r2_hidden(u1_struct_0(X3),u1_pre_topc(X3))
      | v2_pre_topc(X3)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X3),sK9(X3))) ) ),
    inference(resolution,[],[f313,f306])).

fof(f6837,plain,
    ( ~ spl22_467
    | spl22_464
    | spl22_448
    | spl22_462
    | ~ spl22_0
    | spl22_5
    | spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | spl22_185
    | ~ spl22_382 ),
    inference(avatar_split_clause,[],[f5808,f4678,f1945,f1254,f1095,f832,f391,f377,f6802,f6443,f6808,f6814])).

fof(f5808,plain,
    ( v1_subset_1(sK11(sK1),u1_struct_0(sK0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(sK11(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_185
    | ~ spl22_382 ),
    inference(forward_demodulation,[],[f5807,f1096])).

fof(f5807,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_185
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f5806,f4679])).

fof(f5806,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_185 ),
    inference(forward_demodulation,[],[f5805,f1096])).

fof(f5805,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_185 ),
    inference(forward_demodulation,[],[f5804,f1255])).

fof(f5804,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_185 ),
    inference(subsumption_resolution,[],[f5803,f833])).

fof(f5803,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_185 ),
    inference(subsumption_resolution,[],[f5802,f1946])).

fof(f5802,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f5801,f378])).

fof(f5801,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f5799,f392])).

fof(f5799,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK1))
    | ~ v1_zfmisc_1(sK11(sK1))
    | ~ spl22_136 ),
    inference(superposition,[],[f2181,f1096])).

fof(f2181,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK9(X0)))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK11(X0))
      | v1_subset_1(sK11(X0),u1_struct_0(X0))
      | ~ v1_zfmisc_1(sK11(X0)) ) ),
    inference(subsumption_resolution,[],[f2174,f372])).

fof(f2174,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),sK9(X0)))
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK11(X0))
      | v1_subset_1(sK11(X0),u1_struct_0(X0))
      | ~ v1_zfmisc_1(sK11(X0)) ) ),
    inference(resolution,[],[f1007,f355])).

fof(f1007,plain,(
    ! [X2] :
      ( m1_subset_1(sK11(X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X2))
      | v2_pre_topc(X2)
      | l1_pre_topc(g1_pre_topc(u1_struct_0(X2),sK9(X2))) ) ),
    inference(resolution,[],[f313,f307])).

fof(f6836,plain,
    ( spl22_430
    | spl22_468
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(avatar_split_clause,[],[f5601,f4678,f1254,f1095,f391,f377,f6833,f6042])).

fof(f6833,plain,
    ( spl22_468
  <=> ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))),X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_468])])).

fof(f5601,plain,
    ( ! [X0] :
        ( k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))),X0,X0) = X0
        | r2_hidden(sK11(sK1),u1_pre_topc(sK0)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(forward_demodulation,[],[f5600,f1096])).

fof(f5600,plain,
    ( ! [X0] :
        ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))),X0,X0) = X0 )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f5599,f4679])).

fof(f5599,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))),X0,X0) = X0 )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f5598,f1096])).

fof(f5598,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
        | r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))),X0,X0) = X0 )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f5597,f1255])).

fof(f5597,plain,
    ( ! [X0] :
        ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))),X0,X0) = X0 )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f5596,f392])).

fof(f5596,plain,
    ( ! [X0] :
        ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | v2_pre_topc(sK1)
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))),X0,X0) = X0 )
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f5594,f378])).

fof(f5594,plain,
    ( ! [X0] :
        ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK1)
        | v2_pre_topc(sK1)
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))),X0,X0) = X0 )
    | ~ spl22_144 ),
    inference(superposition,[],[f2152,f1255])).

fof(f2152,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK11(X4),u1_pre_topc(X4))
      | ~ l1_pre_topc(X4)
      | v2_pre_topc(X4)
      | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
      | k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X4),sK9(X4)))),X5,X5) = X5 ) ),
    inference(resolution,[],[f993,f819])).

fof(f819,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X1) = X1 ) ),
    inference(resolution,[],[f295,f331])).

fof(f331,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f214])).

fof(f214,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f85])).

fof(f85,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',dt_u1_pre_topc)).

fof(f295,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f197])).

fof(f197,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f108])).

fof(f108,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',idempotence_k9_subset_1)).

fof(f6835,plain,
    ( spl22_428
    | spl22_468
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(avatar_split_clause,[],[f5574,f4678,f1254,f1095,f391,f377,f6833,f5893])).

fof(f5574,plain,
    ( ! [X0] :
        ( k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))),X0,X0) = X0
        | r2_hidden(sK10(sK1),u1_pre_topc(sK0)) )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(forward_demodulation,[],[f5573,f1096])).

fof(f5573,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))),X0,X0) = X0 )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_382 ),
    inference(subsumption_resolution,[],[f5572,f4679])).

fof(f5572,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
        | r2_hidden(sK10(sK1),u1_pre_topc(sK0))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))),X0,X0) = X0 )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f5571,f1096])).

fof(f5571,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
        | r2_hidden(sK10(sK1),u1_pre_topc(sK0))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))),X0,X0) = X0 )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f5570,f1255])).

fof(f5570,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))),X0,X0) = X0 )
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f5569,f392])).

fof(f5569,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
        | v2_pre_topc(sK1)
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))),X0,X0) = X0 )
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f5567,f378])).

fof(f5567,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK1)
        | v2_pre_topc(sK1)
        | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
        | k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))),X0,X0) = X0 )
    | ~ spl22_144 ),
    inference(superposition,[],[f2114,f1255])).

fof(f2114,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK10(X4),u1_pre_topc(X4))
      | ~ l1_pre_topc(X4)
      | v2_pre_topc(X4)
      | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
      | k9_subset_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X4),sK9(X4)))),X5,X5) = X5 ) ),
    inference(resolution,[],[f986,f819])).

fof(f6820,plain,
    ( ~ spl22_459
    | spl22_446
    | ~ spl22_383
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | spl22_171 ),
    inference(avatar_split_clause,[],[f2352,f1428,f1254,f1095,f391,f377,f4675,f6396,f6479])).

fof(f6479,plain,
    ( spl22_459
  <=> ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_459])])).

fof(f1428,plain,
    ( spl22_171
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_171])])).

fof(f2352,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_171 ),
    inference(forward_demodulation,[],[f2351,f1096])).

fof(f2351,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_171 ),
    inference(forward_demodulation,[],[f2350,f1255])).

fof(f2350,plain,
    ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_171 ),
    inference(subsumption_resolution,[],[f2349,f1429])).

fof(f1429,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl22_171 ),
    inference(avatar_component_clause,[],[f1428])).

fof(f2349,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f2348,f1096])).

fof(f2348,plain,
    ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f2347,f1096])).

fof(f2347,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2346,f392])).

fof(f2346,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2345,f378])).

fof(f2345,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ l1_pre_topc(sK1)
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_136 ),
    inference(superposition,[],[f1017,f1096])).

fof(f1017,plain,(
    ! [X1] :
      ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X1),sK9(X1)))
      | ~ l1_pre_topc(X1)
      | m1_subset_1(sK10(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | v2_pre_topc(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(resolution,[],[f328,f304])).

fof(f304,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0)
      | ~ v2_struct_0(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f204])).

fof(f204,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(g1_pre_topc(X0,X1))
        & ~ v2_struct_0(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f203])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(g1_pre_topc(X0,X1))
        & ~ v2_struct_0(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f104])).

fof(f104,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & ~ v1_xboole_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(X0,X1))
        & ~ v2_struct_0(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',fc9_pre_topc)).

fof(f6819,plain,
    ( ~ spl22_459
    | spl22_440
    | ~ spl22_383
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | spl22_171 ),
    inference(avatar_split_clause,[],[f2329,f1428,f1254,f1095,f391,f377,f4675,f6305,f6479])).

fof(f2329,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_171 ),
    inference(forward_demodulation,[],[f2328,f1096])).

fof(f2328,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_171 ),
    inference(forward_demodulation,[],[f2327,f1255])).

fof(f2327,plain,
    ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_171 ),
    inference(subsumption_resolution,[],[f2326,f1429])).

fof(f2326,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f2325,f1096])).

fof(f2325,plain,
    ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f2324,f1096])).

fof(f2324,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2323,f392])).

fof(f2323,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2322,f378])).

fof(f2322,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ l1_pre_topc(sK1)
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_136 ),
    inference(superposition,[],[f1006,f1096])).

fof(f1006,plain,(
    ! [X1] :
      ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X1),sK9(X1)))
      | ~ l1_pre_topc(X1)
      | m1_subset_1(sK11(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | v2_pre_topc(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(resolution,[],[f313,f304])).

fof(f6818,plain,
    ( spl22_446
    | ~ spl22_383
    | spl22_450
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f2234,f1254,f1095,f391,f377,f6450,f4675,f6396])).

fof(f2234,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2233,f1096])).

fof(f2233,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2232,f1096])).

fof(f2232,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2231,f1255])).

fof(f2231,plain,
    ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2230,f392])).

fof(f2230,plain,
    ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2226,f378])).

fof(f2226,plain,
    ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_136 ),
    inference(superposition,[],[f1019,f1096])).

fof(f6817,plain,
    ( spl22_446
    | ~ spl22_383
    | spl22_448
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f2219,f1254,f1095,f391,f377,f6443,f4675,f6396])).

fof(f2219,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2218,f1096])).

fof(f2218,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2217,f1096])).

fof(f2217,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2216,f1255])).

fof(f2216,plain,
    ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2215,f392])).

fof(f2215,plain,
    ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2211,f378])).

fof(f2211,plain,
    ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_136 ),
    inference(superposition,[],[f1018,f1096])).

fof(f6816,plain,
    ( spl22_462
    | spl22_464
    | ~ spl22_467
    | ~ spl22_432
    | ~ spl22_440 ),
    inference(avatar_split_clause,[],[f6312,f6305,f6161,f6814,f6808,f6802])).

fof(f6312,plain,
    ( ~ v1_zfmisc_1(sK11(sK1))
    | v1_xboole_0(sK11(sK1))
    | v1_subset_1(sK11(sK1),u1_struct_0(sK0))
    | ~ spl22_432
    | ~ spl22_440 ),
    inference(resolution,[],[f6306,f6162])).

fof(f6797,plain,
    ( spl22_440
    | ~ spl22_383
    | spl22_450
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f2203,f1254,f1095,f391,f377,f6450,f4675,f6305])).

fof(f2203,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2202,f1096])).

fof(f2202,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2201,f1096])).

fof(f2201,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2200,f1255])).

fof(f2200,plain,
    ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2199,f392])).

fof(f2199,plain,
    ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2195,f378])).

fof(f2195,plain,
    ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_136 ),
    inference(superposition,[],[f1008,f1096])).

fof(f6796,plain,
    ( spl22_440
    | ~ spl22_383
    | spl22_448
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f2188,f1254,f1095,f391,f377,f6443,f4675,f6305])).

fof(f2188,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2187,f1096])).

fof(f2187,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2186,f1096])).

fof(f2186,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2185,f1255])).

fof(f2185,plain,
    ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2184,f392])).

fof(f2184,plain,
    ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2180,f378])).

fof(f2180,plain,
    ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),sK9(sK1)))
    | ~ spl22_136 ),
    inference(superposition,[],[f1007,f1096])).

fof(f6795,plain,
    ( spl22_118
    | spl22_184
    | spl22_432
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1596,f1422,f1095,f6161,f1948,f835])).

fof(f835,plain,
    ( spl22_118
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_118])])).

fof(f1422,plain,
    ( spl22_168
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_168])])).

fof(f1596,plain,
    ( ! [X5] :
        ( v1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | v7_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(X5)
        | ~ v1_zfmisc_1(X5) )
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(forward_demodulation,[],[f1595,f1096])).

fof(f1595,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | v7_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(X5)
        | v1_subset_1(X5,u1_struct_0(sK1))
        | ~ v1_zfmisc_1(X5) )
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1153,f1423])).

fof(f1423,plain,
    ( l1_struct_0(sK1)
    | ~ spl22_168 ),
    inference(avatar_component_clause,[],[f1422])).

fof(f1153,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | v7_struct_0(sK1)
        | ~ l1_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(X5)
        | v1_subset_1(X5,u1_struct_0(sK1))
        | ~ v1_zfmisc_1(X5) )
    | ~ spl22_136 ),
    inference(superposition,[],[f355,f1096])).

fof(f6793,plain,
    ( spl22_444
    | ~ spl22_383
    | spl22_430
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(avatar_split_clause,[],[f1229,f1205,f1095,f391,f377,f6042,f4675,f6389])).

fof(f1229,plain,
    ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(forward_demodulation,[],[f1216,f1209])).

fof(f1216,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(backward_demodulation,[],[f1209,f1165])).

fof(f1165,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1164,f1096])).

fof(f1164,plain,
    ( m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1163,f392])).

fof(f1163,plain,
    ( m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1125,f378])).

fof(f1125,plain,
    ( m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f315,f1096])).

fof(f6792,plain,
    ( spl22_444
    | ~ spl22_383
    | spl22_428
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(avatar_split_clause,[],[f1228,f1205,f1095,f391,f377,f5893,f4675,f6389])).

fof(f1228,plain,
    ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(forward_demodulation,[],[f1215,f1209])).

fof(f1215,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(backward_demodulation,[],[f1209,f1162])).

fof(f1162,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1161,f1096])).

fof(f1161,plain,
    ( m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1160,f392])).

fof(f1160,plain,
    ( m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1124,f378])).

fof(f1124,plain,
    ( m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f314,f1096])).

fof(f6647,plain,
    ( ~ spl22_84
    | spl22_353
    | ~ spl22_460 ),
    inference(avatar_contradiction_clause,[],[f6646])).

fof(f6646,plain,
    ( $false
    | ~ spl22_84
    | ~ spl22_353
    | ~ spl22_460 ),
    inference(subsumption_resolution,[],[f6645,f672])).

fof(f672,plain,
    ( l1_pre_topc(sK17)
    | ~ spl22_84 ),
    inference(avatar_component_clause,[],[f671])).

fof(f671,plain,
    ( spl22_84
  <=> l1_pre_topc(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_84])])).

fof(f6645,plain,
    ( ~ l1_pre_topc(sK17)
    | ~ spl22_353
    | ~ spl22_460 ),
    inference(subsumption_resolution,[],[f6516,f4202])).

fof(f4202,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK17),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl22_353 ),
    inference(avatar_component_clause,[],[f4201])).

fof(f4201,plain,
    ( spl22_353
  <=> ~ m1_subset_1(u1_pre_topc(sK17),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_353])])).

fof(f6516,plain,
    ( m1_subset_1(u1_pre_topc(sK17),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_pre_topc(sK17)
    | ~ spl22_460 ),
    inference(superposition,[],[f331,f6494])).

fof(f6494,plain,
    ( u1_struct_0(sK17) = k1_xboole_0
    | ~ spl22_460 ),
    inference(avatar_component_clause,[],[f6493])).

fof(f6493,plain,
    ( spl22_460
  <=> u1_struct_0(sK17) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_460])])).

fof(f6495,plain,
    ( spl22_460
    | ~ spl22_274 ),
    inference(avatar_split_clause,[],[f2798,f2786,f6493])).

fof(f6488,plain,
    ( ~ spl22_459
    | spl22_430
    | ~ spl22_383
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | spl22_171 ),
    inference(avatar_split_clause,[],[f2299,f1428,f1254,f1095,f391,f377,f4675,f6042,f6479])).

fof(f2299,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_171 ),
    inference(forward_demodulation,[],[f2298,f1096])).

fof(f2298,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_171 ),
    inference(forward_demodulation,[],[f2297,f1255])).

fof(f2297,plain,
    ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_171 ),
    inference(subsumption_resolution,[],[f2296,f1429])).

fof(f2296,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2295,f1096])).

fof(f2295,plain,
    ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2294,f1255])).

fof(f2294,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2293,f392])).

fof(f2293,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2292,f378])).

fof(f2292,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_136 ),
    inference(superposition,[],[f992,f1096])).

fof(f992,plain,(
    ! [X1] :
      ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X1),sK9(X1)))
      | ~ l1_pre_topc(X1)
      | r2_hidden(sK11(X1),u1_pre_topc(X1))
      | v2_pre_topc(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(resolution,[],[f315,f304])).

fof(f6481,plain,
    ( ~ spl22_459
    | spl22_428
    | ~ spl22_383
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | spl22_171 ),
    inference(avatar_split_clause,[],[f2277,f1428,f1254,f1095,f391,f377,f4675,f5893,f6479])).

fof(f2277,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_171 ),
    inference(forward_demodulation,[],[f2276,f1096])).

fof(f2276,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_171 ),
    inference(forward_demodulation,[],[f2275,f1255])).

fof(f2275,plain,
    ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144
    | ~ spl22_171 ),
    inference(subsumption_resolution,[],[f2274,f1429])).

fof(f2274,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2273,f1096])).

fof(f2273,plain,
    ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2272,f1255])).

fof(f2272,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2271,f392])).

fof(f2271,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2270,f378])).

fof(f2270,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_136 ),
    inference(superposition,[],[f985,f1096])).

fof(f985,plain,(
    ! [X1] :
      ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X1),sK9(X1)))
      | ~ l1_pre_topc(X1)
      | r2_hidden(sK10(X1),u1_pre_topc(X1))
      | v2_pre_topc(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(resolution,[],[f314,f304])).

fof(f6474,plain,
    ( spl22_452
    | spl22_454
    | ~ spl22_457
    | spl22_181
    | ~ spl22_182
    | ~ spl22_432 ),
    inference(avatar_split_clause,[],[f6233,f6161,f1668,f1665,f6472,f6466,f6460])).

fof(f6460,plain,
    ( spl22_452
  <=> v1_subset_1(sK13(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_452])])).

fof(f6466,plain,
    ( spl22_454
  <=> v1_xboole_0(sK13(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_454])])).

fof(f6472,plain,
    ( spl22_457
  <=> ~ v1_zfmisc_1(sK13(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_457])])).

fof(f1665,plain,
    ( spl22_181
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_181])])).

fof(f1668,plain,
    ( spl22_182
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_182])])).

fof(f6233,plain,
    ( ~ v1_zfmisc_1(sK13(sK0))
    | v1_xboole_0(sK13(sK0))
    | v1_subset_1(sK13(sK0),u1_struct_0(sK0))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_432 ),
    inference(subsumption_resolution,[],[f6232,f1666])).

fof(f1666,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl22_181 ),
    inference(avatar_component_clause,[],[f1665])).

fof(f6232,plain,
    ( ~ v1_zfmisc_1(sK13(sK0))
    | v1_xboole_0(sK13(sK0))
    | v1_subset_1(sK13(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl22_182
    | ~ spl22_432 ),
    inference(subsumption_resolution,[],[f6222,f1669])).

fof(f1669,plain,
    ( l1_struct_0(sK0)
    | ~ spl22_182 ),
    inference(avatar_component_clause,[],[f1668])).

fof(f6222,plain,
    ( ~ v1_zfmisc_1(sK13(sK0))
    | v1_xboole_0(sK13(sK0))
    | v1_subset_1(sK13(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl22_432 ),
    inference(resolution,[],[f6162,f340])).

fof(f6455,plain,
    ( spl22_450
    | spl22_430
    | ~ spl22_383
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f2166,f1254,f1095,f391,f377,f4675,f6042,f6450])).

fof(f2166,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2165,f1096])).

fof(f2165,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2164,f1255])).

fof(f2164,plain,
    ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2163,f1255])).

fof(f2163,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2162,f392])).

fof(f2162,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2160,f378])).

fof(f2160,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_136 ),
    inference(superposition,[],[f994,f1096])).

fof(f6454,plain,
    ( spl22_448
    | spl22_430
    | ~ spl22_383
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f2158,f1254,f1095,f391,f377,f4675,f6042,f6443])).

fof(f2158,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2157,f1096])).

fof(f2157,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2156,f1255])).

fof(f2156,plain,
    ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2155,f1255])).

fof(f2155,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2154,f392])).

fof(f2154,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2153,f378])).

fof(f2153,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_136 ),
    inference(superposition,[],[f993,f1096])).

fof(f6452,plain,
    ( spl22_450
    | spl22_428
    | ~ spl22_383
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f2149,f1254,f1095,f391,f377,f4675,f5893,f6450])).

fof(f2149,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2148,f1096])).

fof(f2148,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2147,f1255])).

fof(f2147,plain,
    ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2146,f1255])).

fof(f2146,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2145,f392])).

fof(f2145,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2143,f378])).

fof(f2143,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_136 ),
    inference(superposition,[],[f987,f1096])).

fof(f6445,plain,
    ( spl22_448
    | spl22_428
    | ~ spl22_383
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f2120,f1254,f1095,f391,f377,f4675,f5893,f6443])).

fof(f2120,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2119,f1096])).

fof(f2119,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2118,f1255])).

fof(f2118,plain,
    ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f2117,f1255])).

fof(f2117,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2116,f392])).

fof(f2116,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f2115,f378])).

fof(f2115,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK9(sK1)))
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_136 ),
    inference(superposition,[],[f986,f1096])).

fof(f6398,plain,
    ( spl22_446
    | ~ spl22_383
    | spl22_426
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(avatar_split_clause,[],[f1242,f1205,f1095,f391,f377,f5887,f4675,f6396])).

fof(f1242,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(forward_demodulation,[],[f1225,f1209])).

fof(f1225,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(backward_demodulation,[],[f1209,f1196])).

fof(f1196,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1195,f1096])).

fof(f1195,plain,
    ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1194,f392])).

fof(f1194,plain,
    ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1135,f378])).

fof(f1135,plain,
    ( m1_subset_1(sK10(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f327,f1096])).

fof(f6391,plain,
    ( spl22_444
    | ~ spl22_443
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_140
    | ~ spl22_382
    | ~ spl22_440 ),
    inference(avatar_split_clause,[],[f6330,f6305,f4678,f1205,f1095,f391,f377,f6337,f6389])).

fof(f6330,plain,
    ( ~ r2_hidden(k3_xboole_0(sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140
    | ~ spl22_382
    | ~ spl22_440 ),
    inference(subsumption_resolution,[],[f6325,f4679])).

fof(f6325,plain,
    ( ~ r2_hidden(k3_xboole_0(sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140
    | ~ spl22_440 ),
    inference(backward_demodulation,[],[f6317,f1230])).

fof(f1230,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(forward_demodulation,[],[f1217,f1209])).

fof(f1217,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(backward_demodulation,[],[f1209,f1169])).

fof(f1169,plain,
    ( m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1168,f1096])).

fof(f1168,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK1))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1167,f1096])).

fof(f1167,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1166,f392])).

fof(f1166,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | v2_pre_topc(sK1)
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1126,f378])).

fof(f1126,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK10(sK1),sK11(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_subset_1(sK9(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f316,f1096])).

fof(f316,plain,(
    ! [X0] :
      ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK10(X0),sK11(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | m1_subset_1(sK9(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f6346,plain,
    ( spl22_181
    | ~ spl22_182
    | ~ spl22_436 ),
    inference(avatar_contradiction_clause,[],[f6345])).

fof(f6345,plain,
    ( $false
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_436 ),
    inference(subsumption_resolution,[],[f6344,f1666])).

fof(f6344,plain,
    ( v2_struct_0(sK0)
    | ~ spl22_182
    | ~ spl22_436 ),
    inference(subsumption_resolution,[],[f6340,f1669])).

fof(f6340,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl22_436 ),
    inference(resolution,[],[f6263,f338])).

fof(f338,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK12(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f225])).

fof(f6263,plain,
    ( v1_xboole_0(sK12(sK0))
    | ~ spl22_436 ),
    inference(avatar_component_clause,[],[f6262])).

fof(f6262,plain,
    ( spl22_436
  <=> v1_xboole_0(sK12(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_436])])).

fof(f6339,plain,
    ( ~ spl22_443
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_140
    | ~ spl22_382
    | spl22_427
    | ~ spl22_440 ),
    inference(avatar_split_clause,[],[f6332,f6305,f5884,f4678,f1205,f1095,f391,f377,f6337])).

fof(f6332,plain,
    ( ~ r2_hidden(k3_xboole_0(sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140
    | ~ spl22_382
    | ~ spl22_427
    | ~ spl22_440 ),
    inference(subsumption_resolution,[],[f6331,f4679])).

fof(f6331,plain,
    ( ~ r2_hidden(k3_xboole_0(sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140
    | ~ spl22_427
    | ~ spl22_440 ),
    inference(subsumption_resolution,[],[f6326,f5885])).

fof(f6326,plain,
    ( ~ r2_hidden(k3_xboole_0(sK10(sK1),sK11(sK1)),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140
    | ~ spl22_440 ),
    inference(backward_demodulation,[],[f6317,f1233])).

fof(f6311,plain,
    ( spl22_181
    | ~ spl22_182
    | spl22_439 ),
    inference(avatar_contradiction_clause,[],[f6310])).

fof(f6310,plain,
    ( $false
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_439 ),
    inference(subsumption_resolution,[],[f6309,f1666])).

fof(f6309,plain,
    ( v2_struct_0(sK0)
    | ~ spl22_182
    | ~ spl22_439 ),
    inference(subsumption_resolution,[],[f6308,f1669])).

fof(f6308,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl22_439 ),
    inference(resolution,[],[f6269,f339])).

fof(f339,plain,(
    ! [X0] :
      ( v1_zfmisc_1(sK12(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f225])).

fof(f6269,plain,
    ( ~ v1_zfmisc_1(sK12(sK0))
    | ~ spl22_439 ),
    inference(avatar_component_clause,[],[f6268])).

fof(f6268,plain,
    ( spl22_439
  <=> ~ v1_zfmisc_1(sK12(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_439])])).

fof(f6307,plain,
    ( spl22_440
    | ~ spl22_383
    | spl22_426
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(avatar_split_clause,[],[f1231,f1205,f1095,f391,f377,f5887,f4675,f6305])).

fof(f1231,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(forward_demodulation,[],[f1218,f1209])).

fof(f1218,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_140 ),
    inference(backward_demodulation,[],[f1209,f1172])).

fof(f1172,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(forward_demodulation,[],[f1171,f1096])).

fof(f1171,plain,
    ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1170,f392])).

fof(f1170,plain,
    ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ spl22_0
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1127,f378])).

fof(f1127,plain,
    ( m1_subset_1(sK11(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f317,f1096])).

fof(f6270,plain,
    ( spl22_434
    | spl22_436
    | ~ spl22_439
    | spl22_181
    | ~ spl22_182
    | ~ spl22_432 ),
    inference(avatar_split_clause,[],[f6231,f6161,f1668,f1665,f6268,f6262,f6256])).

fof(f6256,plain,
    ( spl22_434
  <=> v1_subset_1(sK12(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_434])])).

fof(f6231,plain,
    ( ~ v1_zfmisc_1(sK12(sK0))
    | v1_xboole_0(sK12(sK0))
    | v1_subset_1(sK12(sK0),u1_struct_0(sK0))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_432 ),
    inference(subsumption_resolution,[],[f6230,f1666])).

fof(f6230,plain,
    ( ~ v1_zfmisc_1(sK12(sK0))
    | v1_xboole_0(sK12(sK0))
    | v1_subset_1(sK12(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl22_182
    | ~ spl22_432 ),
    inference(subsumption_resolution,[],[f6220,f1669])).

fof(f6220,plain,
    ( ~ v1_zfmisc_1(sK12(sK0))
    | v1_xboole_0(sK12(sK0))
    | v1_subset_1(sK12(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl22_432 ),
    inference(resolution,[],[f6162,f337])).

fof(f6163,plain,
    ( spl22_184
    | spl22_432
    | spl22_119
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1906,f1422,f1095,f832,f6161,f1948])).

fof(f1906,plain,
    ( ! [X5] :
        ( v1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | v7_struct_0(sK1)
        | v1_xboole_0(X5)
        | ~ v1_zfmisc_1(X5) )
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(forward_demodulation,[],[f1905,f1096])).

fof(f1905,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | v7_struct_0(sK1)
        | v1_xboole_0(X5)
        | v1_subset_1(X5,u1_struct_0(sK1))
        | ~ v1_zfmisc_1(X5) )
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1904,f833])).

fof(f1904,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | v7_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(X5)
        | v1_subset_1(X5,u1_struct_0(sK1))
        | ~ v1_zfmisc_1(X5) )
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1813,f1423])).

fof(f1813,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | v7_struct_0(sK1)
        | ~ l1_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(X5)
        | v1_subset_1(X5,u1_struct_0(sK1))
        | ~ v1_zfmisc_1(X5) )
    | ~ spl22_136 ),
    inference(superposition,[],[f355,f1096])).

fof(f6137,plain,
    ( spl22_118
    | ~ spl22_185
    | spl22_424
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1607,f1422,f1095,f5761,f1945,f835])).

fof(f5761,plain,
    ( spl22_424
  <=> ! [X4] :
        ( ~ v1_subset_1(X4,u1_struct_0(sK0))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_424])])).

fof(f1607,plain,
    ( ! [X4] :
        ( ~ v1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(X4) )
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(forward_demodulation,[],[f1606,f1096])).

fof(f1606,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(X4)
        | ~ v1_subset_1(X4,u1_struct_0(sK1)) )
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1143,f1423])).

fof(f1143,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | ~ l1_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(X4)
        | ~ v1_subset_1(X4,u1_struct_0(sK1)) )
    | ~ spl22_136 ),
    inference(superposition,[],[f336,f1096])).

fof(f6044,plain,
    ( spl22_426
    | ~ spl22_383
    | spl22_430
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f1308,f1254,f1095,f391,f377,f6042,f4675,f5887])).

fof(f1308,plain,
    ( r2_hidden(sK11(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f1307,f1255])).

fof(f1307,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f1306,f1096])).

fof(f1306,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f1305,f1255])).

fof(f1305,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f1304,f392])).

fof(f1304,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f1280,f378])).

fof(f1280,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK11(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ spl22_144 ),
    inference(superposition,[],[f319,f1255])).

fof(f319,plain,(
    ! [X0] :
      ( r1_tarski(sK9(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK11(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f5895,plain,
    ( spl22_426
    | ~ spl22_383
    | spl22_428
    | ~ spl22_0
    | spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f1303,f1254,f1095,f391,f377,f5893,f4675,f5887])).

fof(f1303,plain,
    ( r2_hidden(sK10(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f1302,f1255])).

fof(f1302,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_136
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f1301,f1096])).

fof(f1301,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(forward_demodulation,[],[f1300,f1255])).

fof(f1300,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | ~ spl22_0
    | ~ spl22_5
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f1299,f392])).

fof(f1299,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f1279,f378])).

fof(f1279,plain,
    ( r1_tarski(sK9(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | r2_hidden(sK10(sK1),u1_pre_topc(sK1))
    | v2_pre_topc(sK1)
    | ~ spl22_144 ),
    inference(superposition,[],[f318,f1255])).

fof(f318,plain,(
    ! [X0] :
      ( r1_tarski(sK9(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK10(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f5840,plain,
    ( ~ spl22_325
    | spl22_192
    | spl22_326
    | spl22_188
    | spl22_181
    | ~ spl22_182
    | ~ spl22_238 ),
    inference(avatar_split_clause,[],[f3784,f2658,f1668,f1665,f2076,f3749,f2367,f3740])).

fof(f3740,plain,
    ( spl22_325
  <=> ~ v1_zfmisc_1(sK12(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_325])])).

fof(f2367,plain,
    ( spl22_192
  <=> v1_subset_1(sK12(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_192])])).

fof(f3749,plain,
    ( spl22_326
  <=> v1_xboole_0(sK12(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_326])])).

fof(f2076,plain,
    ( spl22_188
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_188])])).

fof(f2658,plain,
    ( spl22_238
  <=> m1_subset_1(sK12(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_238])])).

fof(f3784,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK12(sK1))
    | v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK12(sK1))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_238 ),
    inference(subsumption_resolution,[],[f3783,f1666])).

fof(f3783,plain,
    ( v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK12(sK1))
    | v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK12(sK1))
    | ~ spl22_182
    | ~ spl22_238 ),
    inference(subsumption_resolution,[],[f2674,f1669])).

fof(f2674,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK12(sK1))
    | v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK12(sK1))
    | ~ spl22_238 ),
    inference(resolution,[],[f2659,f355])).

fof(f2659,plain,
    ( m1_subset_1(sK12(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl22_238 ),
    inference(avatar_component_clause,[],[f2658])).

fof(f5809,plain,
    ( spl22_324
    | spl22_192
    | spl22_326
    | ~ spl22_189
    | spl22_181
    | ~ spl22_182
    | ~ spl22_238 ),
    inference(avatar_split_clause,[],[f3782,f2658,f1668,f1665,f2079,f3749,f2367,f3743])).

fof(f3743,plain,
    ( spl22_324
  <=> v1_zfmisc_1(sK12(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_324])])).

fof(f2079,plain,
    ( spl22_189
  <=> ~ v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_189])])).

fof(f3782,plain,
    ( ~ v7_struct_0(sK0)
    | v1_xboole_0(sK12(sK1))
    | v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(sK12(sK1))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_238 ),
    inference(subsumption_resolution,[],[f3781,f1666])).

fof(f3781,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK12(sK1))
    | v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(sK12(sK1))
    | ~ spl22_182
    | ~ spl22_238 ),
    inference(subsumption_resolution,[],[f2675,f1669])).

fof(f2675,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK12(sK1))
    | v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(sK12(sK1))
    | ~ spl22_238 ),
    inference(resolution,[],[f2659,f335])).

fof(f5763,plain,
    ( ~ spl22_185
    | spl22_424
    | spl22_119
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1903,f1422,f1095,f832,f5761,f1945])).

fof(f1903,plain,
    ( ! [X4] :
        ( ~ v1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | v1_xboole_0(X4) )
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(forward_demodulation,[],[f1902,f1096])).

fof(f1902,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | v1_xboole_0(X4)
        | ~ v1_subset_1(X4,u1_struct_0(sK1)) )
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1901,f833])).

fof(f1901,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(X4)
        | ~ v1_subset_1(X4,u1_struct_0(sK1)) )
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1803,f1423])).

fof(f1803,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | ~ l1_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(X4)
        | ~ v1_subset_1(X4,u1_struct_0(sK1)) )
    | ~ spl22_136 ),
    inference(superposition,[],[f336,f1096])).

fof(f5721,plain,
    ( spl22_118
    | ~ spl22_185
    | spl22_422
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1610,f1422,f1095,f5719,f1945,f835])).

fof(f5719,plain,
    ( spl22_422
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_zfmisc_1(X3)
        | v1_xboole_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_422])])).

fof(f1610,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(X3)
        | v1_zfmisc_1(X3) )
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1609,f1607])).

fof(f1609,plain,
    ( ! [X3] :
        ( v1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(X3)
        | v1_zfmisc_1(X3) )
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(forward_demodulation,[],[f1608,f1096])).

fof(f1608,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(X3)
        | v1_subset_1(X3,u1_struct_0(sK1))
        | v1_zfmisc_1(X3) )
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1142,f1423])).

fof(f1142,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | ~ l1_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(X3)
        | v1_subset_1(X3,u1_struct_0(sK1))
        | v1_zfmisc_1(X3) )
    | ~ spl22_136 ),
    inference(superposition,[],[f335,f1096])).

fof(f5302,plain,
    ( ~ spl22_417
    | spl22_420
    | ~ spl22_172 ),
    inference(avatar_split_clause,[],[f1714,f1438,f5300,f5211])).

fof(f5211,plain,
    ( spl22_417
  <=> ~ m1_subset_1(u1_pre_topc(sK20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK20)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_417])])).

fof(f5300,plain,
    ( spl22_420
  <=> ! [X5,X4] :
        ( g1_pre_topc(X4,X5) != sK20
        | u1_pre_topc(sK20) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_420])])).

fof(f1438,plain,
    ( spl22_172
  <=> g1_pre_topc(u1_struct_0(sK20),u1_pre_topc(sK20)) = sK20 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_172])])).

fof(f1714,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(X4,X5) != sK20
        | ~ m1_subset_1(u1_pre_topc(sK20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK20))))
        | u1_pre_topc(sK20) = X5 )
    | ~ spl22_172 ),
    inference(superposition,[],[f298,f1439])).

fof(f1439,plain,
    ( g1_pre_topc(u1_struct_0(sK20),u1_pre_topc(sK20)) = sK20
    | ~ spl22_172 ),
    inference(avatar_component_clause,[],[f1438])).

fof(f298,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f199])).

fof(f5234,plain,
    ( ~ spl22_102
    | spl22_417 ),
    inference(avatar_contradiction_clause,[],[f5233])).

fof(f5233,plain,
    ( $false
    | ~ spl22_102
    | ~ spl22_417 ),
    inference(subsumption_resolution,[],[f5232,f735])).

fof(f735,plain,
    ( l1_pre_topc(sK20)
    | ~ spl22_102 ),
    inference(avatar_component_clause,[],[f734])).

fof(f734,plain,
    ( spl22_102
  <=> l1_pre_topc(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_102])])).

fof(f5232,plain,
    ( ~ l1_pre_topc(sK20)
    | ~ spl22_417 ),
    inference(resolution,[],[f5212,f331])).

fof(f5212,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK20))))
    | ~ spl22_417 ),
    inference(avatar_component_clause,[],[f5211])).

fof(f5216,plain,
    ( ~ spl22_417
    | spl22_418
    | ~ spl22_172 ),
    inference(avatar_split_clause,[],[f1712,f1438,f5214,f5211])).

fof(f5214,plain,
    ( spl22_418
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != sK20
        | u1_struct_0(sK20) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_418])])).

fof(f1712,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK20
        | ~ m1_subset_1(u1_pre_topc(sK20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK20))))
        | u1_struct_0(sK20) = X0 )
    | ~ spl22_172 ),
    inference(superposition,[],[f297,f1439])).

fof(f5195,plain,
    ( ~ spl22_411
    | spl22_414
    | ~ spl22_166 ),
    inference(avatar_split_clause,[],[f1703,f1418,f5193,f5106])).

fof(f5106,plain,
    ( spl22_411
  <=> ~ m1_subset_1(u1_pre_topc(sK19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK19)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_411])])).

fof(f5193,plain,
    ( spl22_414
  <=> ! [X5,X4] :
        ( g1_pre_topc(X4,X5) != sK19
        | u1_pre_topc(sK19) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_414])])).

fof(f1418,plain,
    ( spl22_166
  <=> g1_pre_topc(u1_struct_0(sK19),u1_pre_topc(sK19)) = sK19 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_166])])).

fof(f1703,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(X4,X5) != sK19
        | ~ m1_subset_1(u1_pre_topc(sK19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK19))))
        | u1_pre_topc(sK19) = X5 )
    | ~ spl22_166 ),
    inference(superposition,[],[f298,f1419])).

fof(f1419,plain,
    ( g1_pre_topc(u1_struct_0(sK19),u1_pre_topc(sK19)) = sK19
    | ~ spl22_166 ),
    inference(avatar_component_clause,[],[f1418])).

fof(f5129,plain,
    ( ~ spl22_94
    | spl22_411 ),
    inference(avatar_contradiction_clause,[],[f5128])).

fof(f5128,plain,
    ( $false
    | ~ spl22_94
    | ~ spl22_411 ),
    inference(subsumption_resolution,[],[f5127,f707])).

fof(f707,plain,
    ( l1_pre_topc(sK19)
    | ~ spl22_94 ),
    inference(avatar_component_clause,[],[f706])).

fof(f706,plain,
    ( spl22_94
  <=> l1_pre_topc(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_94])])).

fof(f5127,plain,
    ( ~ l1_pre_topc(sK19)
    | ~ spl22_411 ),
    inference(resolution,[],[f5107,f331])).

fof(f5107,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK19))))
    | ~ spl22_411 ),
    inference(avatar_component_clause,[],[f5106])).

fof(f5111,plain,
    ( ~ spl22_411
    | spl22_412
    | ~ spl22_166 ),
    inference(avatar_split_clause,[],[f1701,f1418,f5109,f5106])).

fof(f5109,plain,
    ( spl22_412
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != sK19
        | u1_struct_0(sK19) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_412])])).

fof(f1701,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK19
        | ~ m1_subset_1(u1_pre_topc(sK19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK19))))
        | u1_struct_0(sK19) = X0 )
    | ~ spl22_166 ),
    inference(superposition,[],[f297,f1419])).

fof(f5090,plain,
    ( ~ spl22_405
    | spl22_408
    | ~ spl22_164 ),
    inference(avatar_split_clause,[],[f1692,f1411,f5088,f5001])).

fof(f5001,plain,
    ( spl22_405
  <=> ~ m1_subset_1(u1_pre_topc(sK18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK18)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_405])])).

fof(f5088,plain,
    ( spl22_408
  <=> ! [X5,X4] :
        ( g1_pre_topc(X4,X5) != sK18
        | u1_pre_topc(sK18) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_408])])).

fof(f1411,plain,
    ( spl22_164
  <=> g1_pre_topc(u1_struct_0(sK18),u1_pre_topc(sK18)) = sK18 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_164])])).

fof(f1692,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(X4,X5) != sK18
        | ~ m1_subset_1(u1_pre_topc(sK18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK18))))
        | u1_pre_topc(sK18) = X5 )
    | ~ spl22_164 ),
    inference(superposition,[],[f298,f1412])).

fof(f1412,plain,
    ( g1_pre_topc(u1_struct_0(sK18),u1_pre_topc(sK18)) = sK18
    | ~ spl22_164 ),
    inference(avatar_component_clause,[],[f1411])).

fof(f5020,plain,
    ( ~ spl22_90
    | spl22_405 ),
    inference(avatar_contradiction_clause,[],[f5019])).

fof(f5019,plain,
    ( $false
    | ~ spl22_90
    | ~ spl22_405 ),
    inference(subsumption_resolution,[],[f5018,f693])).

fof(f693,plain,
    ( l1_pre_topc(sK18)
    | ~ spl22_90 ),
    inference(avatar_component_clause,[],[f692])).

fof(f692,plain,
    ( spl22_90
  <=> l1_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_90])])).

fof(f5018,plain,
    ( ~ l1_pre_topc(sK18)
    | ~ spl22_405 ),
    inference(resolution,[],[f5002,f331])).

fof(f5002,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK18))))
    | ~ spl22_405 ),
    inference(avatar_component_clause,[],[f5001])).

fof(f5006,plain,
    ( ~ spl22_405
    | spl22_406
    | ~ spl22_164 ),
    inference(avatar_split_clause,[],[f1690,f1411,f5004,f5001])).

fof(f1690,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK18
        | ~ m1_subset_1(u1_pre_topc(sK18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK18))))
        | u1_struct_0(sK18) = X0 )
    | ~ spl22_164 ),
    inference(superposition,[],[f297,f1412])).

fof(f4985,plain,
    ( ~ spl22_399
    | spl22_402
    | ~ spl22_160 ),
    inference(avatar_split_clause,[],[f1657,f1397,f4983,f4897])).

fof(f4897,plain,
    ( spl22_399
  <=> ~ m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_399])])).

fof(f4983,plain,
    ( spl22_402
  <=> ! [X5,X4] :
        ( g1_pre_topc(X4,X5) != sK8
        | u1_pre_topc(sK8) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_402])])).

fof(f1657,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(X4,X5) != sK8
        | ~ m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
        | u1_pre_topc(sK8) = X5 )
    | ~ spl22_160 ),
    inference(superposition,[],[f298,f1398])).

fof(f4914,plain,
    ( ~ spl22_74
    | spl22_399 ),
    inference(avatar_contradiction_clause,[],[f4913])).

fof(f4913,plain,
    ( $false
    | ~ spl22_74
    | ~ spl22_399 ),
    inference(subsumption_resolution,[],[f4912,f637])).

fof(f637,plain,
    ( l1_pre_topc(sK8)
    | ~ spl22_74 ),
    inference(avatar_component_clause,[],[f636])).

fof(f636,plain,
    ( spl22_74
  <=> l1_pre_topc(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_74])])).

fof(f4912,plain,
    ( ~ l1_pre_topc(sK8)
    | ~ spl22_399 ),
    inference(resolution,[],[f4898,f331])).

fof(f4898,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
    | ~ spl22_399 ),
    inference(avatar_component_clause,[],[f4897])).

fof(f4902,plain,
    ( ~ spl22_399
    | spl22_400
    | ~ spl22_160 ),
    inference(avatar_split_clause,[],[f1655,f1397,f4900,f4897])).

fof(f4900,plain,
    ( spl22_400
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != sK8
        | u1_struct_0(sK8) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_400])])).

fof(f1655,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK8
        | ~ m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8))))
        | u1_struct_0(sK8) = X0 )
    | ~ spl22_160 ),
    inference(superposition,[],[f297,f1398])).

fof(f4881,plain,
    ( ~ spl22_393
    | spl22_396
    | ~ spl22_158 ),
    inference(avatar_split_clause,[],[f1646,f1390,f4879,f4795])).

fof(f4795,plain,
    ( spl22_393
  <=> ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_393])])).

fof(f4879,plain,
    ( spl22_396
  <=> ! [X5,X4] :
        ( g1_pre_topc(X4,X5) != sK7
        | u1_pre_topc(sK7) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_396])])).

fof(f1646,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(X4,X5) != sK7
        | ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
        | u1_pre_topc(sK7) = X5 )
    | ~ spl22_158 ),
    inference(superposition,[],[f298,f1391])).

fof(f4810,plain,
    ( ~ spl22_64
    | spl22_393 ),
    inference(avatar_contradiction_clause,[],[f4809])).

fof(f4809,plain,
    ( $false
    | ~ spl22_64
    | ~ spl22_393 ),
    inference(subsumption_resolution,[],[f4808,f602])).

fof(f602,plain,
    ( l1_pre_topc(sK7)
    | ~ spl22_64 ),
    inference(avatar_component_clause,[],[f601])).

fof(f601,plain,
    ( spl22_64
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_64])])).

fof(f4808,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ spl22_393 ),
    inference(resolution,[],[f4796,f331])).

fof(f4796,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ spl22_393 ),
    inference(avatar_component_clause,[],[f4795])).

fof(f4800,plain,
    ( ~ spl22_393
    | spl22_394
    | ~ spl22_158 ),
    inference(avatar_split_clause,[],[f1644,f1390,f4798,f4795])).

fof(f4798,plain,
    ( spl22_394
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != sK7
        | u1_struct_0(sK7) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_394])])).

fof(f1644,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK7
        | ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
        | u1_struct_0(sK7) = X0 )
    | ~ spl22_158 ),
    inference(superposition,[],[f297,f1391])).

fof(f4779,plain,
    ( ~ spl22_387
    | spl22_390
    | ~ spl22_156 ),
    inference(avatar_split_clause,[],[f1495,f1383,f4777,f4700])).

fof(f4700,plain,
    ( spl22_387
  <=> ~ m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_387])])).

fof(f4777,plain,
    ( spl22_390
  <=> ! [X5,X4] :
        ( g1_pre_topc(X4,X5) != sK6
        | u1_pre_topc(sK6) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_390])])).

fof(f1495,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(X4,X5) != sK6
        | ~ m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
        | u1_pre_topc(sK6) = X5 )
    | ~ spl22_156 ),
    inference(superposition,[],[f298,f1384])).

fof(f4708,plain,
    ( ~ spl22_56
    | spl22_387 ),
    inference(avatar_contradiction_clause,[],[f4707])).

fof(f4707,plain,
    ( $false
    | ~ spl22_56
    | ~ spl22_387 ),
    inference(subsumption_resolution,[],[f4706,f574])).

fof(f574,plain,
    ( l1_pre_topc(sK6)
    | ~ spl22_56 ),
    inference(avatar_component_clause,[],[f573])).

fof(f573,plain,
    ( spl22_56
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_56])])).

fof(f4706,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ spl22_387 ),
    inference(resolution,[],[f4701,f331])).

fof(f4701,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ spl22_387 ),
    inference(avatar_component_clause,[],[f4700])).

fof(f4705,plain,
    ( ~ spl22_387
    | spl22_388
    | ~ spl22_156 ),
    inference(avatar_split_clause,[],[f1493,f1383,f4703,f4700])).

fof(f4703,plain,
    ( spl22_388
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != sK6
        | u1_struct_0(sK6) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_388])])).

fof(f1493,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK6
        | ~ m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
        | u1_struct_0(sK6) = X0 )
    | ~ spl22_156 ),
    inference(superposition,[],[f297,f1384])).

fof(f4684,plain,
    ( ~ spl22_379
    | spl22_384
    | ~ spl22_152 ),
    inference(avatar_split_clause,[],[f1484,f1369,f4682,f4601])).

fof(f4601,plain,
    ( spl22_379
  <=> ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_379])])).

fof(f4682,plain,
    ( spl22_384
  <=> ! [X5,X4] :
        ( g1_pre_topc(X4,X5) != sK5
        | u1_pre_topc(sK5) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_384])])).

fof(f1484,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(X4,X5) != sK5
        | ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
        | u1_pre_topc(sK5) = X5 )
    | ~ spl22_152 ),
    inference(superposition,[],[f298,f1370])).

fof(f4680,plain,
    ( ~ spl22_297
    | spl22_382
    | ~ spl22_114
    | ~ spl22_286
    | ~ spl22_292 ),
    inference(avatar_split_clause,[],[f3009,f2900,f2880,f799,f4678,f3411])).

fof(f3411,plain,
    ( spl22_297
  <=> ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_297])])).

fof(f2880,plain,
    ( spl22_286
  <=> u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_286])])).

fof(f3009,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_114
    | ~ spl22_286
    | ~ spl22_292 ),
    inference(forward_demodulation,[],[f3008,f2901])).

fof(f3008,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_114
    | ~ spl22_286 ),
    inference(subsumption_resolution,[],[f2922,f800])).

fof(f2922,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_286 ),
    inference(superposition,[],[f330,f2881])).

fof(f2881,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_286 ),
    inference(avatar_component_clause,[],[f2880])).

fof(f330,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f213])).

fof(f4614,plain,
    ( ~ spl22_44
    | spl22_379 ),
    inference(avatar_contradiction_clause,[],[f4613])).

fof(f4613,plain,
    ( $false
    | ~ spl22_44
    | ~ spl22_379 ),
    inference(subsumption_resolution,[],[f4612,f532])).

fof(f532,plain,
    ( l1_pre_topc(sK5)
    | ~ spl22_44 ),
    inference(avatar_component_clause,[],[f531])).

fof(f531,plain,
    ( spl22_44
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_44])])).

fof(f4612,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ spl22_379 ),
    inference(resolution,[],[f4602,f331])).

fof(f4602,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ spl22_379 ),
    inference(avatar_component_clause,[],[f4601])).

fof(f4606,plain,
    ( ~ spl22_379
    | spl22_380
    | ~ spl22_152 ),
    inference(avatar_split_clause,[],[f1482,f1369,f4604,f4601])).

fof(f4604,plain,
    ( spl22_380
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != sK5
        | u1_struct_0(sK5) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_380])])).

fof(f1482,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK5
        | ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
        | u1_struct_0(sK5) = X0 )
    | ~ spl22_152 ),
    inference(superposition,[],[f297,f1370])).

fof(f4585,plain,
    ( ~ spl22_373
    | spl22_376
    | ~ spl22_150 ),
    inference(avatar_split_clause,[],[f1473,f1362,f4583,f4501])).

fof(f4501,plain,
    ( spl22_373
  <=> ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_373])])).

fof(f4583,plain,
    ( spl22_376
  <=> ! [X5,X4] :
        ( g1_pre_topc(X4,X5) != sK4
        | u1_pre_topc(sK4) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_376])])).

fof(f1473,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(X4,X5) != sK4
        | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
        | u1_pre_topc(sK4) = X5 )
    | ~ spl22_150 ),
    inference(superposition,[],[f298,f1363])).

fof(f4515,plain,
    ( ~ spl22_32
    | spl22_373 ),
    inference(avatar_contradiction_clause,[],[f4514])).

fof(f4514,plain,
    ( $false
    | ~ spl22_32
    | ~ spl22_373 ),
    inference(subsumption_resolution,[],[f4513,f490])).

fof(f490,plain,
    ( l1_pre_topc(sK4)
    | ~ spl22_32 ),
    inference(avatar_component_clause,[],[f489])).

fof(f489,plain,
    ( spl22_32
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_32])])).

fof(f4513,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ spl22_373 ),
    inference(resolution,[],[f4502,f331])).

fof(f4502,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ spl22_373 ),
    inference(avatar_component_clause,[],[f4501])).

fof(f4506,plain,
    ( ~ spl22_373
    | spl22_374
    | ~ spl22_150 ),
    inference(avatar_split_clause,[],[f1471,f1362,f4504,f4501])).

fof(f4504,plain,
    ( spl22_374
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != sK4
        | u1_struct_0(sK4) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_374])])).

fof(f1471,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK4
        | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
        | u1_struct_0(sK4) = X0 )
    | ~ spl22_150 ),
    inference(superposition,[],[f297,f1363])).

fof(f4485,plain,
    ( ~ spl22_367
    | spl22_370
    | ~ spl22_148 ),
    inference(avatar_split_clause,[],[f1459,f1355,f4483,f4403])).

fof(f4403,plain,
    ( spl22_367
  <=> ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_367])])).

fof(f4483,plain,
    ( spl22_370
  <=> ! [X5,X4] :
        ( g1_pre_topc(X4,X5) != sK3
        | u1_pre_topc(sK3) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_370])])).

fof(f1459,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(X4,X5) != sK3
        | ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
        | u1_pre_topc(sK3) = X5 )
    | ~ spl22_148 ),
    inference(superposition,[],[f298,f1356])).

fof(f4412,plain,
    ( ~ spl22_20
    | spl22_367 ),
    inference(avatar_contradiction_clause,[],[f4411])).

fof(f4411,plain,
    ( $false
    | ~ spl22_20
    | ~ spl22_367 ),
    inference(subsumption_resolution,[],[f4410,f448])).

fof(f448,plain,
    ( l1_pre_topc(sK3)
    | ~ spl22_20 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl22_20
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_20])])).

fof(f4410,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl22_367 ),
    inference(resolution,[],[f4404,f331])).

fof(f4404,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ spl22_367 ),
    inference(avatar_component_clause,[],[f4403])).

fof(f4409,plain,
    ( ~ spl22_193
    | spl22_326
    | ~ spl22_189
    | spl22_181
    | ~ spl22_182
    | ~ spl22_238 ),
    inference(avatar_split_clause,[],[f3786,f2658,f1668,f1665,f2079,f3749,f2370])).

fof(f2370,plain,
    ( spl22_193
  <=> ~ v1_subset_1(sK12(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_193])])).

fof(f3786,plain,
    ( ~ v7_struct_0(sK0)
    | v1_xboole_0(sK12(sK1))
    | ~ v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_238 ),
    inference(subsumption_resolution,[],[f3785,f1666])).

fof(f3785,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK12(sK1))
    | ~ v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | ~ spl22_182
    | ~ spl22_238 ),
    inference(subsumption_resolution,[],[f2676,f1669])).

fof(f2676,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK12(sK1))
    | ~ v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | ~ spl22_238 ),
    inference(resolution,[],[f2659,f336])).

fof(f4408,plain,
    ( ~ spl22_367
    | spl22_368
    | ~ spl22_148 ),
    inference(avatar_split_clause,[],[f1457,f1355,f4406,f4403])).

fof(f4406,plain,
    ( spl22_368
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != sK3
        | u1_struct_0(sK3) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_368])])).

fof(f1457,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK3
        | ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
        | u1_struct_0(sK3) = X0 )
    | ~ spl22_148 ),
    inference(superposition,[],[f297,f1356])).

fof(f4387,plain,
    ( ~ spl22_359
    | spl22_364
    | ~ spl22_146 ),
    inference(avatar_split_clause,[],[f1448,f1270,f4385,f4296])).

fof(f4296,plain,
    ( spl22_359
  <=> ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_359])])).

fof(f4385,plain,
    ( spl22_364
  <=> ! [X5,X4] :
        ( g1_pre_topc(X4,X5) != sK2
        | u1_pre_topc(sK2) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_364])])).

fof(f1448,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(X4,X5) != sK2
        | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | u1_pre_topc(sK2) = X5 )
    | ~ spl22_146 ),
    inference(superposition,[],[f298,f1271])).

fof(f4311,plain,
    ( ~ spl22_8
    | spl22_359 ),
    inference(avatar_contradiction_clause,[],[f4310])).

fof(f4310,plain,
    ( $false
    | ~ spl22_8
    | ~ spl22_359 ),
    inference(subsumption_resolution,[],[f4309,f406])).

fof(f406,plain,
    ( l1_pre_topc(sK2)
    | ~ spl22_8 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl22_8
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_8])])).

fof(f4309,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl22_359 ),
    inference(resolution,[],[f4297,f331])).

fof(f4297,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl22_359 ),
    inference(avatar_component_clause,[],[f4296])).

fof(f4308,plain,
    ( spl22_118
    | spl22_184
    | spl22_362
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1602,f1422,f1095,f4306,f1948,f835])).

fof(f4306,plain,
    ( spl22_362
  <=> m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_362])])).

fof(f1602,plain,
    ( m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1147,f1423])).

fof(f1147,plain,
    ( m1_subset_1(sK14(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f343,f1096])).

fof(f343,plain,(
    ! [X0] :
      ( m1_subset_1(sK14(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f231])).

fof(f231,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f230])).

fof(f230,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f156])).

fof(f156,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',rc6_tex_2)).

fof(f4301,plain,
    ( ~ spl22_359
    | spl22_360
    | ~ spl22_146 ),
    inference(avatar_split_clause,[],[f1446,f1270,f4299,f4296])).

fof(f4299,plain,
    ( spl22_360
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != sK2
        | u1_struct_0(sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_360])])).

fof(f1446,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK2
        | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | u1_struct_0(sK2) = X0 )
    | ~ spl22_146 ),
    inference(superposition,[],[f297,f1271])).

fof(f4291,plain,
    ( spl22_356
    | ~ spl22_353
    | ~ spl22_162
    | ~ spl22_274 ),
    inference(avatar_split_clause,[],[f2802,f2786,f1404,f4201,f4289])).

fof(f4289,plain,
    ( spl22_356
  <=> ! [X5,X4] :
        ( g1_pre_topc(X4,X5) != sK17
        | u1_pre_topc(sK17) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_356])])).

fof(f2802,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(u1_pre_topc(sK17),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
        | g1_pre_topc(X4,X5) != sK17
        | u1_pre_topc(sK17) = X5 )
    | ~ spl22_162
    | ~ spl22_274 ),
    inference(backward_demodulation,[],[f2798,f1681])).

fof(f1681,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(X4,X5) != sK17
        | ~ m1_subset_1(u1_pre_topc(sK17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK17))))
        | u1_pre_topc(sK17) = X5 )
    | ~ spl22_162 ),
    inference(superposition,[],[f298,f1405])).

fof(f4206,plain,
    ( ~ spl22_353
    | spl22_354
    | ~ spl22_162
    | ~ spl22_274 ),
    inference(avatar_split_clause,[],[f2809,f2786,f1404,f4204,f4201])).

fof(f4204,plain,
    ( spl22_354
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | g1_pre_topc(X0,X1) != sK17 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_354])])).

fof(f2809,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(u1_pre_topc(sK17),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
        | g1_pre_topc(X0,X1) != sK17 )
    | ~ spl22_162
    | ~ spl22_274 ),
    inference(forward_demodulation,[],[f2800,f2798])).

fof(f2800,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(u1_pre_topc(sK17),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
        | g1_pre_topc(X0,X1) != sK17
        | u1_struct_0(sK17) = X0 )
    | ~ spl22_162
    | ~ spl22_274 ),
    inference(backward_demodulation,[],[f2798,f1679])).

fof(f1679,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != sK17
        | ~ m1_subset_1(u1_pre_topc(sK17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK17))))
        | u1_struct_0(sK17) = X0 )
    | ~ spl22_162 ),
    inference(superposition,[],[f297,f1405])).

fof(f4196,plain,
    ( spl22_118
    | spl22_184
    | spl22_350
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1600,f1422,f1095,f4194,f1948,f835])).

fof(f4194,plain,
    ( spl22_350
  <=> m1_subset_1(sK15(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_350])])).

fof(f1600,plain,
    ( m1_subset_1(sK15(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1149,f1423])).

fof(f1149,plain,
    ( m1_subset_1(sK15(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f347,f1096])).

fof(f347,plain,(
    ! [X0] :
      ( m1_subset_1(sK15(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f233])).

fof(f233,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f232])).

fof(f232,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',rc4_tex_2)).

fof(f4103,plain,
    ( ~ spl22_347
    | spl22_348
    | spl22_181
    | ~ spl22_182
    | spl22_189
    | spl22_253
    | ~ spl22_300 ),
    inference(avatar_split_clause,[],[f4071,f3453,f2712,f2079,f1668,f1665,f4101,f4095])).

fof(f4095,plain,
    ( spl22_347
  <=> ~ v1_zfmisc_1(sK16(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_347])])).

fof(f4101,plain,
    ( spl22_348
  <=> v1_xboole_0(sK16(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_348])])).

fof(f2712,plain,
    ( spl22_253
  <=> ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_253])])).

fof(f3453,plain,
    ( spl22_300
  <=> m1_subset_1(sK16(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_300])])).

fof(f4071,plain,
    ( v1_xboole_0(sK16(sK1))
    | ~ v1_zfmisc_1(sK16(sK1))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_189
    | ~ spl22_253
    | ~ spl22_300 ),
    inference(subsumption_resolution,[],[f4070,f2713])).

fof(f2713,plain,
    ( ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ spl22_253 ),
    inference(avatar_component_clause,[],[f2712])).

fof(f4070,plain,
    ( v1_xboole_0(sK16(sK1))
    | v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK16(sK1))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_189
    | ~ spl22_300 ),
    inference(subsumption_resolution,[],[f4069,f1666])).

fof(f4069,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(sK16(sK1))
    | v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK16(sK1))
    | ~ spl22_182
    | ~ spl22_189
    | ~ spl22_300 ),
    inference(subsumption_resolution,[],[f4068,f1669])).

fof(f4068,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK16(sK1))
    | v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK16(sK1))
    | ~ spl22_189
    | ~ spl22_300 ),
    inference(subsumption_resolution,[],[f4062,f2080])).

fof(f2080,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl22_189 ),
    inference(avatar_component_clause,[],[f2079])).

fof(f4062,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK16(sK1))
    | v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK16(sK1))
    | ~ spl22_300 ),
    inference(resolution,[],[f3454,f355])).

fof(f3454,plain,
    ( m1_subset_1(sK16(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl22_300 ),
    inference(avatar_component_clause,[],[f3453])).

fof(f4043,plain,
    ( spl22_214
    | ~ spl22_189
    | spl22_181
    | ~ spl22_182
    | spl22_195
    | ~ spl22_200
    | spl22_217 ),
    inference(avatar_split_clause,[],[f3790,f2580,f2519,f2417,f1668,f1665,f2079,f2574])).

fof(f2574,plain,
    ( spl22_214
  <=> v1_zfmisc_1(sK13(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_214])])).

fof(f2417,plain,
    ( spl22_195
  <=> ~ v1_subset_1(sK13(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_195])])).

fof(f2519,plain,
    ( spl22_200
  <=> m1_subset_1(sK13(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_200])])).

fof(f2580,plain,
    ( spl22_217
  <=> ~ v1_xboole_0(sK13(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_217])])).

fof(f3790,plain,
    ( ~ v7_struct_0(sK0)
    | v1_zfmisc_1(sK13(sK1))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_195
    | ~ spl22_200
    | ~ spl22_217 ),
    inference(subsumption_resolution,[],[f3789,f2418])).

fof(f2418,plain,
    ( ~ v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | ~ spl22_195 ),
    inference(avatar_component_clause,[],[f2417])).

fof(f3789,plain,
    ( ~ v7_struct_0(sK0)
    | v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(sK13(sK1))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_200
    | ~ spl22_217 ),
    inference(subsumption_resolution,[],[f3788,f2581])).

fof(f2581,plain,
    ( ~ v1_xboole_0(sK13(sK1))
    | ~ spl22_217 ),
    inference(avatar_component_clause,[],[f2580])).

fof(f3788,plain,
    ( ~ v7_struct_0(sK0)
    | v1_xboole_0(sK13(sK1))
    | v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(sK13(sK1))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_200 ),
    inference(subsumption_resolution,[],[f3787,f1666])).

fof(f3787,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK13(sK1))
    | v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(sK13(sK1))
    | ~ spl22_182
    | ~ spl22_200 ),
    inference(subsumption_resolution,[],[f3701,f1669])).

fof(f3701,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK13(sK1))
    | v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(sK13(sK1))
    | ~ spl22_200 ),
    inference(resolution,[],[f2520,f335])).

fof(f2520,plain,
    ( m1_subset_1(sK13(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl22_200 ),
    inference(avatar_component_clause,[],[f2519])).

fof(f4024,plain,
    ( ~ spl22_215
    | spl22_188
    | spl22_181
    | ~ spl22_182
    | spl22_195
    | ~ spl22_200
    | spl22_217 ),
    inference(avatar_split_clause,[],[f3780,f2580,f2519,f2417,f1668,f1665,f2076,f2577])).

fof(f2577,plain,
    ( spl22_215
  <=> ~ v1_zfmisc_1(sK13(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_215])])).

fof(f3780,plain,
    ( v7_struct_0(sK0)
    | ~ v1_zfmisc_1(sK13(sK1))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_195
    | ~ spl22_200
    | ~ spl22_217 ),
    inference(subsumption_resolution,[],[f3779,f2418])).

fof(f3779,plain,
    ( v7_struct_0(sK0)
    | v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK13(sK1))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_200
    | ~ spl22_217 ),
    inference(subsumption_resolution,[],[f3778,f2581])).

fof(f3778,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK13(sK1))
    | v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK13(sK1))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_200 ),
    inference(subsumption_resolution,[],[f3777,f1666])).

fof(f3777,plain,
    ( v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK13(sK1))
    | v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK13(sK1))
    | ~ spl22_182
    | ~ spl22_200 ),
    inference(subsumption_resolution,[],[f2549,f1669])).

fof(f2549,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK13(sK1))
    | v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK13(sK1))
    | ~ spl22_200 ),
    inference(resolution,[],[f2520,f355])).

fof(f4005,plain,
    ( ~ spl22_215
    | spl22_184
    | spl22_119
    | ~ spl22_136
    | ~ spl22_168
    | spl22_195 ),
    inference(avatar_split_clause,[],[f3752,f2417,f1422,f1095,f832,f1948,f2577])).

fof(f3752,plain,
    ( v7_struct_0(sK1)
    | ~ v1_zfmisc_1(sK13(sK1))
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_168
    | ~ spl22_195 ),
    inference(subsumption_resolution,[],[f1943,f2418])).

fof(f1943,plain,
    ( v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ v1_zfmisc_1(sK13(sK1))
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1942,f833])).

fof(f1942,plain,
    ( v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ v1_zfmisc_1(sK13(sK1))
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1940,f1423])).

fof(f1940,plain,
    ( v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ v1_zfmisc_1(sK13(sK1))
    | ~ spl22_136 ),
    inference(superposition,[],[f958,f1096])).

fof(f958,plain,(
    ! [X1] :
      ( v1_subset_1(sK13(X1),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | v7_struct_0(X1)
      | ~ v1_zfmisc_1(sK13(X1)) ) ),
    inference(subsumption_resolution,[],[f954,f341])).

fof(f341,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK13(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f227])).

fof(f954,plain,(
    ! [X1] :
      ( v7_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(sK13(X1))
      | v1_subset_1(sK13(X1),u1_struct_0(X1))
      | ~ v1_zfmisc_1(sK13(X1)) ) ),
    inference(duplicate_literal_removal,[],[f947])).

fof(f947,plain,(
    ! [X1] :
      ( v7_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(sK13(X1))
      | v1_subset_1(sK13(X1),u1_struct_0(X1))
      | ~ v1_zfmisc_1(sK13(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f355,f340])).

fof(f3979,plain,
    ( spl22_344
    | ~ spl22_321
    | spl22_105
    | spl22_107 ),
    inference(avatar_split_clause,[],[f2010,f748,f741,f3697,f3977])).

fof(f3977,plain,
    ( spl22_344
  <=> ! [X5] : k3_xboole_0(X5,sK16(sK20)) = k9_subset_1(u1_struct_0(sK20),X5,sK16(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_344])])).

fof(f3697,plain,
    ( spl22_321
  <=> ~ l1_struct_0(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_321])])).

fof(f741,plain,
    ( spl22_105
  <=> ~ v2_struct_0(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_105])])).

fof(f748,plain,
    ( spl22_107
  <=> ~ v7_struct_0(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_107])])).

fof(f2010,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(sK20)
        | k3_xboole_0(X5,sK16(sK20)) = k9_subset_1(u1_struct_0(sK20),X5,sK16(sK20)) )
    | ~ spl22_105
    | ~ spl22_107 ),
    inference(subsumption_resolution,[],[f2002,f742])).

fof(f742,plain,
    ( ~ v2_struct_0(sK20)
    | ~ spl22_105 ),
    inference(avatar_component_clause,[],[f741])).

fof(f2002,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(sK20)
        | v2_struct_0(sK20)
        | k3_xboole_0(X5,sK16(sK20)) = k9_subset_1(u1_struct_0(sK20),X5,sK16(sK20)) )
    | ~ spl22_107 ),
    inference(resolution,[],[f899,f749])).

fof(f749,plain,
    ( ~ v7_struct_0(sK20)
    | ~ spl22_107 ),
    inference(avatar_component_clause,[],[f748])).

fof(f899,plain,(
    ! [X0,X1] :
      ( v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k3_xboole_0(X1,sK16(X0)) = k9_subset_1(u1_struct_0(X0),X1,sK16(X0)) ) ),
    inference(resolution,[],[f351,f294])).

fof(f351,plain,(
    ! [X0] :
      ( m1_subset_1(sK16(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f235])).

fof(f235,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f234])).

fof(f234,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f151])).

fof(f151,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',rc5_tex_2)).

fof(f3961,plain,
    ( spl22_342
    | ~ spl22_317
    | spl22_77
    | spl22_79 ),
    inference(avatar_split_clause,[],[f2009,f650,f643,f3665,f3959])).

fof(f3959,plain,
    ( spl22_342
  <=> ! [X4] : k3_xboole_0(X4,sK16(sK8)) = k9_subset_1(u1_struct_0(sK8),X4,sK16(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_342])])).

fof(f3665,plain,
    ( spl22_317
  <=> ~ l1_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_317])])).

fof(f643,plain,
    ( spl22_77
  <=> ~ v2_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_77])])).

fof(f650,plain,
    ( spl22_79
  <=> ~ v7_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_79])])).

fof(f2009,plain,
    ( ! [X4] :
        ( ~ l1_struct_0(sK8)
        | k3_xboole_0(X4,sK16(sK8)) = k9_subset_1(u1_struct_0(sK8),X4,sK16(sK8)) )
    | ~ spl22_77
    | ~ spl22_79 ),
    inference(subsumption_resolution,[],[f2001,f644])).

fof(f644,plain,
    ( ~ v2_struct_0(sK8)
    | ~ spl22_77 ),
    inference(avatar_component_clause,[],[f643])).

fof(f2001,plain,
    ( ! [X4] :
        ( ~ l1_struct_0(sK8)
        | v2_struct_0(sK8)
        | k3_xboole_0(X4,sK16(sK8)) = k9_subset_1(u1_struct_0(sK8),X4,sK16(sK8)) )
    | ~ spl22_79 ),
    inference(resolution,[],[f899,f651])).

fof(f651,plain,
    ( ~ v7_struct_0(sK8)
    | ~ spl22_79 ),
    inference(avatar_component_clause,[],[f650])).

fof(f3943,plain,
    ( spl22_340
    | ~ spl22_313
    | spl22_47
    | spl22_125 ),
    inference(avatar_split_clause,[],[f2008,f981,f538,f3633,f3941])).

fof(f3941,plain,
    ( spl22_340
  <=> ! [X3] : k3_xboole_0(X3,sK16(sK5)) = k9_subset_1(u1_struct_0(sK5),X3,sK16(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_340])])).

fof(f3633,plain,
    ( spl22_313
  <=> ~ l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_313])])).

fof(f538,plain,
    ( spl22_47
  <=> ~ v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_47])])).

fof(f981,plain,
    ( spl22_125
  <=> ~ v7_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_125])])).

fof(f2008,plain,
    ( ! [X3] :
        ( ~ l1_struct_0(sK5)
        | k3_xboole_0(X3,sK16(sK5)) = k9_subset_1(u1_struct_0(sK5),X3,sK16(sK5)) )
    | ~ spl22_47
    | ~ spl22_125 ),
    inference(subsumption_resolution,[],[f2000,f539])).

fof(f539,plain,
    ( ~ v2_struct_0(sK5)
    | ~ spl22_47 ),
    inference(avatar_component_clause,[],[f538])).

fof(f2000,plain,
    ( ! [X3] :
        ( ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | k3_xboole_0(X3,sK16(sK5)) = k9_subset_1(u1_struct_0(sK5),X3,sK16(sK5)) )
    | ~ spl22_125 ),
    inference(resolution,[],[f899,f982])).

fof(f982,plain,
    ( ~ v7_struct_0(sK5)
    | ~ spl22_125 ),
    inference(avatar_component_clause,[],[f981])).

fof(f3934,plain,
    ( spl22_119
    | ~ spl22_168
    | spl22_325 ),
    inference(avatar_contradiction_clause,[],[f3933])).

fof(f3933,plain,
    ( $false
    | ~ spl22_119
    | ~ spl22_168
    | ~ spl22_325 ),
    inference(subsumption_resolution,[],[f3932,f833])).

fof(f3932,plain,
    ( v2_struct_0(sK1)
    | ~ spl22_168
    | ~ spl22_325 ),
    inference(subsumption_resolution,[],[f3931,f1423])).

fof(f3931,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_325 ),
    inference(resolution,[],[f3741,f339])).

fof(f3741,plain,
    ( ~ v1_zfmisc_1(sK12(sK1))
    | ~ spl22_325 ),
    inference(avatar_component_clause,[],[f3740])).

fof(f3921,plain,
    ( spl22_338
    | ~ spl22_309
    | spl22_35
    | spl22_127 ),
    inference(avatar_split_clause,[],[f2007,f1002,f496,f3583,f3919])).

fof(f3919,plain,
    ( spl22_338
  <=> ! [X2] : k3_xboole_0(X2,sK16(sK4)) = k9_subset_1(u1_struct_0(sK4),X2,sK16(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_338])])).

fof(f3583,plain,
    ( spl22_309
  <=> ~ l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_309])])).

fof(f496,plain,
    ( spl22_35
  <=> ~ v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_35])])).

fof(f1002,plain,
    ( spl22_127
  <=> ~ v7_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_127])])).

fof(f2007,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(sK4)
        | k3_xboole_0(X2,sK16(sK4)) = k9_subset_1(u1_struct_0(sK4),X2,sK16(sK4)) )
    | ~ spl22_35
    | ~ spl22_127 ),
    inference(subsumption_resolution,[],[f1999,f497])).

fof(f497,plain,
    ( ~ v2_struct_0(sK4)
    | ~ spl22_35 ),
    inference(avatar_component_clause,[],[f496])).

fof(f1999,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(sK4)
        | v2_struct_0(sK4)
        | k3_xboole_0(X2,sK16(sK4)) = k9_subset_1(u1_struct_0(sK4),X2,sK16(sK4)) )
    | ~ spl22_127 ),
    inference(resolution,[],[f899,f1003])).

fof(f1003,plain,
    ( ~ v7_struct_0(sK4)
    | ~ spl22_127 ),
    inference(avatar_component_clause,[],[f1002])).

fof(f3902,plain,
    ( spl22_336
    | ~ spl22_305
    | spl22_23
    | spl22_117 ),
    inference(avatar_split_clause,[],[f2006,f824,f454,f3551,f3900])).

fof(f3900,plain,
    ( spl22_336
  <=> ! [X1] : k3_xboole_0(X1,sK16(sK3)) = k9_subset_1(u1_struct_0(sK3),X1,sK16(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_336])])).

fof(f3551,plain,
    ( spl22_305
  <=> ~ l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_305])])).

fof(f454,plain,
    ( spl22_23
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_23])])).

fof(f824,plain,
    ( spl22_117
  <=> ~ v7_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_117])])).

fof(f2006,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(sK3)
        | k3_xboole_0(X1,sK16(sK3)) = k9_subset_1(u1_struct_0(sK3),X1,sK16(sK3)) )
    | ~ spl22_23
    | ~ spl22_117 ),
    inference(subsumption_resolution,[],[f1998,f455])).

fof(f455,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl22_23 ),
    inference(avatar_component_clause,[],[f454])).

fof(f1998,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(sK3)
        | v2_struct_0(sK3)
        | k3_xboole_0(X1,sK16(sK3)) = k9_subset_1(u1_struct_0(sK3),X1,sK16(sK3)) )
    | ~ spl22_117 ),
    inference(resolution,[],[f899,f825])).

fof(f825,plain,
    ( ~ v7_struct_0(sK3)
    | ~ spl22_117 ),
    inference(avatar_component_clause,[],[f824])).

fof(f3888,plain,
    ( spl22_334
    | ~ spl22_321
    | spl22_105
    | spl22_107 ),
    inference(avatar_split_clause,[],[f1996,f748,f741,f3697,f3886])).

fof(f3886,plain,
    ( spl22_334
  <=> ! [X5] : k3_xboole_0(X5,sK15(sK20)) = k9_subset_1(u1_struct_0(sK20),X5,sK15(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_334])])).

fof(f1996,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(sK20)
        | k3_xboole_0(X5,sK15(sK20)) = k9_subset_1(u1_struct_0(sK20),X5,sK15(sK20)) )
    | ~ spl22_105
    | ~ spl22_107 ),
    inference(subsumption_resolution,[],[f1988,f742])).

fof(f1988,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(sK20)
        | v2_struct_0(sK20)
        | k3_xboole_0(X5,sK15(sK20)) = k9_subset_1(u1_struct_0(sK20),X5,sK15(sK20)) )
    | ~ spl22_107 ),
    inference(resolution,[],[f897,f749])).

fof(f897,plain,(
    ! [X0,X1] :
      ( v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k3_xboole_0(X1,sK15(X0)) = k9_subset_1(u1_struct_0(X0),X1,sK15(X0)) ) ),
    inference(resolution,[],[f347,f294])).

fof(f3847,plain,
    ( spl22_332
    | ~ spl22_317
    | spl22_77
    | spl22_79 ),
    inference(avatar_split_clause,[],[f1995,f650,f643,f3665,f3845])).

fof(f3845,plain,
    ( spl22_332
  <=> ! [X4] : k3_xboole_0(X4,sK15(sK8)) = k9_subset_1(u1_struct_0(sK8),X4,sK15(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_332])])).

fof(f1995,plain,
    ( ! [X4] :
        ( ~ l1_struct_0(sK8)
        | k3_xboole_0(X4,sK15(sK8)) = k9_subset_1(u1_struct_0(sK8),X4,sK15(sK8)) )
    | ~ spl22_77
    | ~ spl22_79 ),
    inference(subsumption_resolution,[],[f1987,f644])).

fof(f1987,plain,
    ( ! [X4] :
        ( ~ l1_struct_0(sK8)
        | v2_struct_0(sK8)
        | k3_xboole_0(X4,sK15(sK8)) = k9_subset_1(u1_struct_0(sK8),X4,sK15(sK8)) )
    | ~ spl22_79 ),
    inference(resolution,[],[f897,f651])).

fof(f3840,plain,
    ( ~ spl22_185
    | spl22_119
    | ~ spl22_168
    | spl22_215 ),
    inference(avatar_split_clause,[],[f3457,f2577,f1422,f832,f1945])).

fof(f3457,plain,
    ( ~ v7_struct_0(sK1)
    | ~ spl22_119
    | ~ spl22_168
    | ~ spl22_215 ),
    inference(subsumption_resolution,[],[f3456,f833])).

fof(f3456,plain,
    ( v2_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | ~ spl22_168
    | ~ spl22_215 ),
    inference(subsumption_resolution,[],[f2606,f1423])).

fof(f2606,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | ~ spl22_215 ),
    inference(resolution,[],[f2578,f944])).

fof(f944,plain,(
    ! [X1] :
      ( v1_zfmisc_1(sK13(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ v7_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f943,f930])).

fof(f930,plain,(
    ! [X1] :
      ( ~ v1_subset_1(sK13(X1),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ v7_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f927,f341])).

fof(f927,plain,(
    ! [X1] :
      ( ~ v7_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(sK13(X1))
      | ~ v1_subset_1(sK13(X1),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f920])).

fof(f920,plain,(
    ! [X1] :
      ( ~ v7_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(sK13(X1))
      | ~ v1_subset_1(sK13(X1),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f336,f340])).

fof(f943,plain,(
    ! [X1] :
      ( ~ v7_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | v1_subset_1(sK13(X1),u1_struct_0(X1))
      | v1_zfmisc_1(sK13(X1)) ) ),
    inference(subsumption_resolution,[],[f941,f341])).

fof(f941,plain,(
    ! [X1] :
      ( ~ v7_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(sK13(X1))
      | v1_subset_1(sK13(X1),u1_struct_0(X1))
      | v1_zfmisc_1(sK13(X1)) ) ),
    inference(duplicate_literal_removal,[],[f934])).

fof(f934,plain,(
    ! [X1] :
      ( ~ v7_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(sK13(X1))
      | v1_subset_1(sK13(X1),u1_struct_0(X1))
      | v1_zfmisc_1(sK13(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f335,f340])).

fof(f2578,plain,
    ( ~ v1_zfmisc_1(sK13(sK1))
    | ~ spl22_215 ),
    inference(avatar_component_clause,[],[f2577])).

fof(f3832,plain,
    ( spl22_330
    | ~ spl22_313
    | spl22_47
    | spl22_125 ),
    inference(avatar_split_clause,[],[f1994,f981,f538,f3633,f3830])).

fof(f3830,plain,
    ( spl22_330
  <=> ! [X3] : k3_xboole_0(X3,sK15(sK5)) = k9_subset_1(u1_struct_0(sK5),X3,sK15(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_330])])).

fof(f1994,plain,
    ( ! [X3] :
        ( ~ l1_struct_0(sK5)
        | k3_xboole_0(X3,sK15(sK5)) = k9_subset_1(u1_struct_0(sK5),X3,sK15(sK5)) )
    | ~ spl22_47
    | ~ spl22_125 ),
    inference(subsumption_resolution,[],[f1986,f539])).

fof(f1986,plain,
    ( ! [X3] :
        ( ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | k3_xboole_0(X3,sK15(sK5)) = k9_subset_1(u1_struct_0(sK5),X3,sK15(sK5)) )
    | ~ spl22_125 ),
    inference(resolution,[],[f897,f982])).

fof(f3797,plain,
    ( spl22_328
    | ~ spl22_309
    | spl22_35
    | spl22_127 ),
    inference(avatar_split_clause,[],[f1993,f1002,f496,f3583,f3795])).

fof(f3795,plain,
    ( spl22_328
  <=> ! [X2] : k3_xboole_0(X2,sK15(sK4)) = k9_subset_1(u1_struct_0(sK4),X2,sK15(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_328])])).

fof(f1993,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(sK4)
        | k3_xboole_0(X2,sK15(sK4)) = k9_subset_1(u1_struct_0(sK4),X2,sK15(sK4)) )
    | ~ spl22_35
    | ~ spl22_127 ),
    inference(subsumption_resolution,[],[f1985,f497])).

fof(f1985,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(sK4)
        | v2_struct_0(sK4)
        | k3_xboole_0(X2,sK15(sK4)) = k9_subset_1(u1_struct_0(sK4),X2,sK15(sK4)) )
    | ~ spl22_127 ),
    inference(resolution,[],[f897,f1003])).

fof(f3751,plain,
    ( spl22_324
    | spl22_326
    | spl22_181
    | ~ spl22_182
    | ~ spl22_186
    | spl22_193
    | ~ spl22_238 ),
    inference(avatar_split_clause,[],[f3530,f2658,f2370,f1951,f1668,f1665,f3749,f3743])).

fof(f3530,plain,
    ( v1_xboole_0(sK12(sK1))
    | v1_zfmisc_1(sK12(sK1))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_186
    | ~ spl22_193
    | ~ spl22_238 ),
    inference(subsumption_resolution,[],[f3529,f2371])).

fof(f2371,plain,
    ( ~ v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | ~ spl22_193 ),
    inference(avatar_component_clause,[],[f2370])).

fof(f3529,plain,
    ( v1_xboole_0(sK12(sK1))
    | v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(sK12(sK1))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_186
    | ~ spl22_238 ),
    inference(subsumption_resolution,[],[f3528,f1666])).

fof(f3528,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(sK12(sK1))
    | v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(sK12(sK1))
    | ~ spl22_182
    | ~ spl22_186
    | ~ spl22_238 ),
    inference(subsumption_resolution,[],[f3527,f1669])).

fof(f3527,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK12(sK1))
    | v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(sK12(sK1))
    | ~ spl22_182
    | ~ spl22_186
    | ~ spl22_238 ),
    inference(subsumption_resolution,[],[f2675,f3524])).

fof(f3524,plain,
    ( v7_struct_0(sK0)
    | ~ spl22_182
    | ~ spl22_186 ),
    inference(subsumption_resolution,[],[f3523,f1669])).

fof(f3523,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ spl22_186 ),
    inference(resolution,[],[f1952,f357])).

fof(f1952,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl22_186 ),
    inference(avatar_component_clause,[],[f1951])).

fof(f3731,plain,
    ( spl22_322
    | ~ spl22_305
    | spl22_23
    | spl22_117 ),
    inference(avatar_split_clause,[],[f1992,f824,f454,f3551,f3729])).

fof(f3729,plain,
    ( spl22_322
  <=> ! [X1] : k3_xboole_0(X1,sK15(sK3)) = k9_subset_1(u1_struct_0(sK3),X1,sK15(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_322])])).

fof(f1992,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(sK3)
        | k3_xboole_0(X1,sK15(sK3)) = k9_subset_1(u1_struct_0(sK3),X1,sK15(sK3)) )
    | ~ spl22_23
    | ~ spl22_117 ),
    inference(subsumption_resolution,[],[f1984,f455])).

fof(f1984,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(sK3)
        | v2_struct_0(sK3)
        | k3_xboole_0(X1,sK15(sK3)) = k9_subset_1(u1_struct_0(sK3),X1,sK15(sK3)) )
    | ~ spl22_117 ),
    inference(resolution,[],[f897,f825])).

fof(f3709,plain,
    ( ~ spl22_102
    | spl22_321 ),
    inference(avatar_contradiction_clause,[],[f3708])).

fof(f3708,plain,
    ( $false
    | ~ spl22_102
    | ~ spl22_321 ),
    inference(subsumption_resolution,[],[f3707,f735])).

fof(f3707,plain,
    ( ~ l1_pre_topc(sK20)
    | ~ spl22_321 ),
    inference(resolution,[],[f3698,f372])).

fof(f3698,plain,
    ( ~ l1_struct_0(sK20)
    | ~ spl22_321 ),
    inference(avatar_component_clause,[],[f3697])).

fof(f3699,plain,
    ( spl22_318
    | ~ spl22_321
    | spl22_105
    | spl22_107 ),
    inference(avatar_split_clause,[],[f1978,f748,f741,f3697,f3691])).

fof(f3691,plain,
    ( spl22_318
  <=> ! [X4] : k3_xboole_0(X4,sK14(sK20)) = k9_subset_1(u1_struct_0(sK20),X4,sK14(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_318])])).

fof(f1978,plain,
    ( ! [X4] :
        ( ~ l1_struct_0(sK20)
        | k3_xboole_0(X4,sK14(sK20)) = k9_subset_1(u1_struct_0(sK20),X4,sK14(sK20)) )
    | ~ spl22_105
    | ~ spl22_107 ),
    inference(subsumption_resolution,[],[f1973,f742])).

fof(f1973,plain,
    ( ! [X4] :
        ( ~ l1_struct_0(sK20)
        | v2_struct_0(sK20)
        | k3_xboole_0(X4,sK14(sK20)) = k9_subset_1(u1_struct_0(sK20),X4,sK14(sK20)) )
    | ~ spl22_107 ),
    inference(resolution,[],[f895,f749])).

fof(f895,plain,(
    ! [X0,X1] :
      ( v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k3_xboole_0(X1,sK14(X0)) = k9_subset_1(u1_struct_0(X0),X1,sK14(X0)) ) ),
    inference(resolution,[],[f343,f294])).

fof(f3670,plain,
    ( ~ spl22_74
    | spl22_317 ),
    inference(avatar_contradiction_clause,[],[f3669])).

fof(f3669,plain,
    ( $false
    | ~ spl22_74
    | ~ spl22_317 ),
    inference(subsumption_resolution,[],[f3668,f637])).

fof(f3668,plain,
    ( ~ l1_pre_topc(sK8)
    | ~ spl22_317 ),
    inference(resolution,[],[f3666,f372])).

fof(f3666,plain,
    ( ~ l1_struct_0(sK8)
    | ~ spl22_317 ),
    inference(avatar_component_clause,[],[f3665])).

fof(f3667,plain,
    ( spl22_314
    | ~ spl22_317
    | spl22_77
    | spl22_79 ),
    inference(avatar_split_clause,[],[f1977,f650,f643,f3665,f3659])).

fof(f3659,plain,
    ( spl22_314
  <=> ! [X3] : k3_xboole_0(X3,sK14(sK8)) = k9_subset_1(u1_struct_0(sK8),X3,sK14(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_314])])).

fof(f1977,plain,
    ( ! [X3] :
        ( ~ l1_struct_0(sK8)
        | k3_xboole_0(X3,sK14(sK8)) = k9_subset_1(u1_struct_0(sK8),X3,sK14(sK8)) )
    | ~ spl22_77
    | ~ spl22_79 ),
    inference(subsumption_resolution,[],[f1972,f644])).

fof(f1972,plain,
    ( ! [X3] :
        ( ~ l1_struct_0(sK8)
        | v2_struct_0(sK8)
        | k3_xboole_0(X3,sK14(sK8)) = k9_subset_1(u1_struct_0(sK8),X3,sK14(sK8)) )
    | ~ spl22_79 ),
    inference(resolution,[],[f895,f651])).

fof(f3638,plain,
    ( ~ spl22_44
    | spl22_313 ),
    inference(avatar_contradiction_clause,[],[f3637])).

fof(f3637,plain,
    ( $false
    | ~ spl22_44
    | ~ spl22_313 ),
    inference(subsumption_resolution,[],[f3636,f532])).

fof(f3636,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ spl22_313 ),
    inference(resolution,[],[f3634,f372])).

fof(f3634,plain,
    ( ~ l1_struct_0(sK5)
    | ~ spl22_313 ),
    inference(avatar_component_clause,[],[f3633])).

fof(f3635,plain,
    ( spl22_310
    | ~ spl22_313
    | spl22_47
    | spl22_125 ),
    inference(avatar_split_clause,[],[f1976,f981,f538,f3633,f3627])).

fof(f3627,plain,
    ( spl22_310
  <=> ! [X2] : k3_xboole_0(X2,sK14(sK5)) = k9_subset_1(u1_struct_0(sK5),X2,sK14(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_310])])).

fof(f1976,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(sK5)
        | k3_xboole_0(X2,sK14(sK5)) = k9_subset_1(u1_struct_0(sK5),X2,sK14(sK5)) )
    | ~ spl22_47
    | ~ spl22_125 ),
    inference(subsumption_resolution,[],[f1971,f539])).

fof(f1971,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | k3_xboole_0(X2,sK14(sK5)) = k9_subset_1(u1_struct_0(sK5),X2,sK14(sK5)) )
    | ~ spl22_125 ),
    inference(resolution,[],[f895,f982])).

fof(f3606,plain,
    ( ~ spl22_32
    | spl22_309 ),
    inference(avatar_contradiction_clause,[],[f3605])).

fof(f3605,plain,
    ( $false
    | ~ spl22_32
    | ~ spl22_309 ),
    inference(subsumption_resolution,[],[f3604,f490])).

fof(f3604,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ spl22_309 ),
    inference(resolution,[],[f3584,f372])).

fof(f3584,plain,
    ( ~ l1_struct_0(sK4)
    | ~ spl22_309 ),
    inference(avatar_component_clause,[],[f3583])).

fof(f3592,plain,
    ( spl22_119
    | ~ spl22_168
    | ~ spl22_216 ),
    inference(avatar_contradiction_clause,[],[f3591])).

fof(f3591,plain,
    ( $false
    | ~ spl22_119
    | ~ spl22_168
    | ~ spl22_216 ),
    inference(subsumption_resolution,[],[f3590,f833])).

fof(f3590,plain,
    ( v2_struct_0(sK1)
    | ~ spl22_168
    | ~ spl22_216 ),
    inference(subsumption_resolution,[],[f3586,f1423])).

fof(f3586,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_216 ),
    inference(resolution,[],[f2584,f341])).

fof(f2584,plain,
    ( v1_xboole_0(sK13(sK1))
    | ~ spl22_216 ),
    inference(avatar_component_clause,[],[f2583])).

fof(f2583,plain,
    ( spl22_216
  <=> v1_xboole_0(sK13(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_216])])).

fof(f3585,plain,
    ( spl22_306
    | ~ spl22_309
    | spl22_35
    | spl22_127 ),
    inference(avatar_split_clause,[],[f1975,f1002,f496,f3583,f3577])).

fof(f3577,plain,
    ( spl22_306
  <=> ! [X1] : k3_xboole_0(X1,sK14(sK4)) = k9_subset_1(u1_struct_0(sK4),X1,sK14(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_306])])).

fof(f1975,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(sK4)
        | k3_xboole_0(X1,sK14(sK4)) = k9_subset_1(u1_struct_0(sK4),X1,sK14(sK4)) )
    | ~ spl22_35
    | ~ spl22_127 ),
    inference(subsumption_resolution,[],[f1970,f497])).

fof(f1970,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(sK4)
        | v2_struct_0(sK4)
        | k3_xboole_0(X1,sK14(sK4)) = k9_subset_1(u1_struct_0(sK4),X1,sK14(sK4)) )
    | ~ spl22_127 ),
    inference(resolution,[],[f895,f1003])).

fof(f3556,plain,
    ( ~ spl22_20
    | spl22_305 ),
    inference(avatar_contradiction_clause,[],[f3555])).

fof(f3555,plain,
    ( $false
    | ~ spl22_20
    | ~ spl22_305 ),
    inference(subsumption_resolution,[],[f3554,f448])).

fof(f3554,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl22_305 ),
    inference(resolution,[],[f3552,f372])).

fof(f3552,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl22_305 ),
    inference(avatar_component_clause,[],[f3551])).

fof(f3553,plain,
    ( spl22_302
    | ~ spl22_305
    | spl22_23
    | spl22_117 ),
    inference(avatar_split_clause,[],[f1974,f824,f454,f3551,f3545])).

fof(f3545,plain,
    ( spl22_302
  <=> ! [X0] : k3_xboole_0(X0,sK14(sK3)) = k9_subset_1(u1_struct_0(sK3),X0,sK14(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_302])])).

fof(f1974,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK3)
        | k3_xboole_0(X0,sK14(sK3)) = k9_subset_1(u1_struct_0(sK3),X0,sK14(sK3)) )
    | ~ spl22_23
    | ~ spl22_117 ),
    inference(subsumption_resolution,[],[f1969,f455])).

fof(f1969,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK3)
        | v2_struct_0(sK3)
        | k3_xboole_0(X0,sK14(sK3)) = k9_subset_1(u1_struct_0(sK3),X0,sK14(sK3)) )
    | ~ spl22_117 ),
    inference(resolution,[],[f895,f825])).

fof(f3537,plain,
    ( spl22_188
    | ~ spl22_182
    | ~ spl22_186 ),
    inference(avatar_split_clause,[],[f3524,f1951,f1668,f2076])).

fof(f3526,plain,
    ( ~ spl22_182
    | ~ spl22_186
    | spl22_189 ),
    inference(avatar_contradiction_clause,[],[f3525])).

fof(f3525,plain,
    ( $false
    | ~ spl22_182
    | ~ spl22_186
    | ~ spl22_189 ),
    inference(subsumption_resolution,[],[f3524,f2080])).

fof(f3480,plain,
    ( spl22_119
    | ~ spl22_168
    | ~ spl22_184
    | spl22_215 ),
    inference(avatar_contradiction_clause,[],[f3479])).

fof(f3479,plain,
    ( $false
    | ~ spl22_119
    | ~ spl22_168
    | ~ spl22_184
    | ~ spl22_215 ),
    inference(subsumption_resolution,[],[f1949,f3457])).

fof(f1949,plain,
    ( v7_struct_0(sK1)
    | ~ spl22_184 ),
    inference(avatar_component_clause,[],[f1948])).

fof(f3455,plain,
    ( spl22_118
    | spl22_184
    | spl22_300
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1598,f1422,f1095,f3453,f1948,f835])).

fof(f1598,plain,
    ( m1_subset_1(sK16(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1151,f1423])).

fof(f1151,plain,
    ( m1_subset_1(sK16(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f351,f1096])).

fof(f3435,plain,
    ( ~ spl22_2
    | ~ spl22_6
    | spl22_297 ),
    inference(avatar_contradiction_clause,[],[f3434])).

fof(f3434,plain,
    ( $false
    | ~ spl22_2
    | ~ spl22_6
    | ~ spl22_297 ),
    inference(subsumption_resolution,[],[f3433,f385])).

fof(f3433,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl22_6
    | ~ spl22_297 ),
    inference(subsumption_resolution,[],[f3432,f399])).

fof(f3432,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl22_297 ),
    inference(resolution,[],[f3412,f309])).

fof(f309,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f207])).

fof(f207,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f206])).

fof(f206,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f98])).

fof(f98,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',fc6_pre_topc)).

fof(f3412,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_297 ),
    inference(avatar_component_clause,[],[f3411])).

fof(f3419,plain,
    ( ~ spl22_297
    | ~ spl22_299
    | ~ spl22_114
    | ~ spl22_286 ),
    inference(avatar_split_clause,[],[f2953,f2880,f799,f3417,f3411])).

fof(f3417,plain,
    ( spl22_299
  <=> ~ v1_xboole_0(u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_299])])).

fof(f2953,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK0))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_114
    | ~ spl22_286 ),
    inference(subsumption_resolution,[],[f2910,f800])).

fof(f2910,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_286 ),
    inference(superposition,[],[f312,f2881])).

fof(f312,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f211])).

fof(f211,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f210])).

fof(f210,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f90])).

fof(f90,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ~ v1_xboole_0(u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',fc1_pre_topc)).

fof(f3091,plain,
    ( spl22_294
    | ~ spl22_114
    | ~ spl22_286 ),
    inference(avatar_split_clause,[],[f3012,f2880,f799,f3089])).

fof(f3089,plain,
    ( spl22_294
  <=> v1_tops_2(u1_pre_topc(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_294])])).

fof(f3012,plain,
    ( v1_tops_2(u1_pre_topc(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_114
    | ~ spl22_286 ),
    inference(subsumption_resolution,[],[f2924,f800])).

fof(f2924,plain,
    ( v1_tops_2(u1_pre_topc(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_286 ),
    inference(superposition,[],[f332,f2881])).

fof(f332,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f215])).

fof(f215,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f97])).

fof(f97,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_tops_2(u1_pre_topc(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',fc5_compts_1)).

fof(f2902,plain,
    ( spl22_292
    | ~ spl22_132
    | ~ spl22_280 ),
    inference(avatar_split_clause,[],[f2845,f2828,f1051,f2900])).

fof(f1051,plain,
    ( spl22_132
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_132])])).

fof(f2828,plain,
    ( spl22_280
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_280])])).

fof(f2845,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_132
    | ~ spl22_280 ),
    inference(trivial_inequality_removal,[],[f2842])).

fof(f2842,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_132
    | ~ spl22_280 ),
    inference(superposition,[],[f1075,f2829])).

fof(f2829,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl22_280 ),
    inference(avatar_component_clause,[],[f2828])).

fof(f1075,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(sK0) = X0 )
    | ~ spl22_132 ),
    inference(backward_demodulation,[],[f1070,f1052])).

fof(f1052,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(sK1) = X0 )
    | ~ spl22_132 ),
    inference(avatar_component_clause,[],[f1051])).

fof(f1070,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl22_132 ),
    inference(equality_resolution,[],[f1052])).

fof(f2895,plain,
    ( spl22_288
    | ~ spl22_291
    | ~ spl22_176 ),
    inference(avatar_split_clause,[],[f1616,f1578,f2893,f2887])).

fof(f2887,plain,
    ( spl22_288
  <=> g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_288])])).

fof(f2893,plain,
    ( spl22_291
  <=> ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_291])])).

fof(f1578,plain,
    ( spl22_176
  <=> v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_176])])).

fof(f1616,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
    | ~ spl22_176 ),
    inference(resolution,[],[f1579,f302])).

fof(f1579,plain,
    ( v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl22_176 ),
    inference(avatar_component_clause,[],[f1578])).

fof(f2882,plain,
    ( spl22_286
    | ~ spl22_140
    | ~ spl22_280 ),
    inference(avatar_split_clause,[],[f2844,f2828,f1205,f2880])).

fof(f2844,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_140
    | ~ spl22_280 ),
    inference(trivial_inequality_removal,[],[f2843])).

fof(f2843,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_140
    | ~ spl22_280 ),
    inference(superposition,[],[f1227,f2829])).

fof(f1227,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_pre_topc(sK0) = X1 )
    | ~ spl22_140 ),
    inference(backward_demodulation,[],[f1209,f1206])).

fof(f2873,plain,
    ( spl22_282
    | ~ spl22_285
    | ~ spl22_90
    | ~ spl22_164 ),
    inference(avatar_split_clause,[],[f1778,f1411,f692,f2871,f2865])).

fof(f2865,plain,
    ( spl22_282
  <=> v1_xboole_0(u1_struct_0(sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_282])])).

fof(f2871,plain,
    ( spl22_285
  <=> ~ v2_struct_0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_285])])).

fof(f1778,plain,
    ( ~ v2_struct_0(sK18)
    | v1_xboole_0(u1_struct_0(sK18))
    | ~ spl22_90
    | ~ spl22_164 ),
    inference(subsumption_resolution,[],[f1771,f693])).

fof(f1771,plain,
    ( ~ v2_struct_0(sK18)
    | v1_xboole_0(u1_struct_0(sK18))
    | ~ l1_pre_topc(sK18)
    | ~ spl22_164 ),
    inference(superposition,[],[f875,f1412])).

fof(f875,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f304,f331])).

fof(f2830,plain,
    ( spl22_280
    | ~ spl22_114
    | ~ spl22_122 ),
    inference(avatar_split_clause,[],[f932,f881,f799,f2828])).

fof(f881,plain,
    ( spl22_122
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_122])])).

fof(f932,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl22_114
    | ~ spl22_122 ),
    inference(subsumption_resolution,[],[f931,f800])).

fof(f931,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl22_122 ),
    inference(resolution,[],[f882,f302])).

fof(f882,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_122 ),
    inference(avatar_component_clause,[],[f881])).

fof(f2823,plain,
    ( spl22_178
    | ~ spl22_274 ),
    inference(avatar_split_clause,[],[f2807,f2786,f1585])).

fof(f1585,plain,
    ( spl22_178
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_178])])).

fof(f2807,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl22_274 ),
    inference(backward_demodulation,[],[f2798,f2787])).

fof(f2818,plain,
    ( spl22_278
    | ~ spl22_162
    | ~ spl22_274 ),
    inference(avatar_split_clause,[],[f2799,f2786,f1404,f2816])).

fof(f2799,plain,
    ( g1_pre_topc(k1_xboole_0,u1_pre_topc(sK17)) = sK17
    | ~ spl22_162
    | ~ spl22_274 ),
    inference(backward_demodulation,[],[f2798,f1405])).

fof(f2811,plain,
    ( spl22_179
    | ~ spl22_274 ),
    inference(avatar_contradiction_clause,[],[f2810])).

fof(f2810,plain,
    ( $false
    | ~ spl22_179
    | ~ spl22_274 ),
    inference(subsumption_resolution,[],[f2807,f1583])).

fof(f1583,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl22_179 ),
    inference(avatar_component_clause,[],[f1582])).

fof(f1582,plain,
    ( spl22_179
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_179])])).

fof(f2795,plain,
    ( spl22_118
    | spl22_184
    | spl22_276
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1601,f1422,f1095,f2793,f1948,f835])).

fof(f2793,plain,
    ( spl22_276
  <=> v1_subset_1(sK14(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_276])])).

fof(f1601,plain,
    ( v1_subset_1(sK14(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1148,f1423])).

fof(f1148,plain,
    ( v1_subset_1(sK14(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f346,f1096])).

fof(f346,plain,(
    ! [X0] :
      ( v1_subset_1(sK14(X0),u1_struct_0(X0))
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f231])).

fof(f2788,plain,
    ( spl22_274
    | ~ spl22_84
    | ~ spl22_86
    | ~ spl22_162 ),
    inference(avatar_split_clause,[],[f1777,f1404,f678,f671,f2786])).

fof(f678,plain,
    ( spl22_86
  <=> v2_struct_0(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_86])])).

fof(f1777,plain,
    ( v1_xboole_0(u1_struct_0(sK17))
    | ~ spl22_84
    | ~ spl22_86
    | ~ spl22_162 ),
    inference(subsumption_resolution,[],[f1776,f672])).

fof(f1776,plain,
    ( v1_xboole_0(u1_struct_0(sK17))
    | ~ l1_pre_topc(sK17)
    | ~ spl22_86
    | ~ spl22_162 ),
    inference(subsumption_resolution,[],[f1770,f679])).

fof(f679,plain,
    ( v2_struct_0(sK17)
    | ~ spl22_86 ),
    inference(avatar_component_clause,[],[f678])).

fof(f1770,plain,
    ( ~ v2_struct_0(sK17)
    | v1_xboole_0(u1_struct_0(sK17))
    | ~ l1_pre_topc(sK17)
    | ~ spl22_162 ),
    inference(superposition,[],[f875,f1405])).

fof(f2781,plain,
    ( spl22_272
    | ~ spl22_271
    | ~ spl22_140
    | ~ spl22_172 ),
    inference(avatar_split_clause,[],[f1717,f1438,f1205,f2772,f2779])).

fof(f2779,plain,
    ( spl22_272
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_272])])).

fof(f2772,plain,
    ( spl22_271
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK20 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_271])])).

fof(f1717,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK20
    | u1_pre_topc(sK0) = u1_pre_topc(sK20)
    | ~ spl22_140
    | ~ spl22_172 ),
    inference(superposition,[],[f1227,f1439])).

fof(f2774,plain,
    ( spl22_268
    | ~ spl22_271
    | ~ spl22_132
    | ~ spl22_172 ),
    inference(avatar_split_clause,[],[f1716,f1438,f1051,f2772,f2766])).

fof(f2766,plain,
    ( spl22_268
  <=> u1_struct_0(sK0) = u1_struct_0(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_268])])).

fof(f1716,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK20
    | u1_struct_0(sK0) = u1_struct_0(sK20)
    | ~ spl22_132
    | ~ spl22_172 ),
    inference(superposition,[],[f1075,f1439])).

fof(f2761,plain,
    ( spl22_118
    | spl22_184
    | spl22_266
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1599,f1422,f1095,f2759,f1948,f835])).

fof(f2759,plain,
    ( spl22_266
  <=> v1_subset_1(sK15(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_266])])).

fof(f1599,plain,
    ( v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1150,f1423])).

fof(f1150,plain,
    ( v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f350,f1096])).

fof(f350,plain,(
    ! [X0] :
      ( v1_subset_1(sK15(X0),u1_struct_0(X0))
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f233])).

fof(f2754,plain,
    ( spl22_264
    | ~ spl22_263
    | ~ spl22_140
    | ~ spl22_166 ),
    inference(avatar_split_clause,[],[f1706,f1418,f1205,f2745,f2752])).

fof(f2752,plain,
    ( spl22_264
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_264])])).

fof(f2745,plain,
    ( spl22_263
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK19 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_263])])).

fof(f1706,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK19
    | u1_pre_topc(sK0) = u1_pre_topc(sK19)
    | ~ spl22_140
    | ~ spl22_166 ),
    inference(superposition,[],[f1227,f1419])).

fof(f2747,plain,
    ( spl22_260
    | ~ spl22_263
    | ~ spl22_132
    | ~ spl22_166 ),
    inference(avatar_split_clause,[],[f1705,f1418,f1051,f2745,f2739])).

fof(f2739,plain,
    ( spl22_260
  <=> u1_struct_0(sK0) = u1_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_260])])).

fof(f1705,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK19
    | u1_struct_0(sK0) = u1_struct_0(sK19)
    | ~ spl22_132
    | ~ spl22_166 ),
    inference(superposition,[],[f1075,f1419])).

fof(f2734,plain,
    ( spl22_258
    | ~ spl22_257
    | ~ spl22_140
    | ~ spl22_164 ),
    inference(avatar_split_clause,[],[f1695,f1411,f1205,f2725,f2732])).

fof(f2732,plain,
    ( spl22_258
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_258])])).

fof(f2725,plain,
    ( spl22_257
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK18 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_257])])).

fof(f1695,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK18
    | u1_pre_topc(sK0) = u1_pre_topc(sK18)
    | ~ spl22_140
    | ~ spl22_164 ),
    inference(superposition,[],[f1227,f1412])).

fof(f2727,plain,
    ( spl22_254
    | ~ spl22_257
    | ~ spl22_132
    | ~ spl22_164 ),
    inference(avatar_split_clause,[],[f1694,f1411,f1051,f2725,f2719])).

fof(f2719,plain,
    ( spl22_254
  <=> u1_struct_0(sK0) = u1_struct_0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_254])])).

fof(f1694,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK18
    | u1_struct_0(sK0) = u1_struct_0(sK18)
    | ~ spl22_132
    | ~ spl22_164 ),
    inference(superposition,[],[f1075,f1412])).

fof(f2714,plain,
    ( spl22_118
    | spl22_184
    | ~ spl22_253
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1597,f1422,f1095,f2712,f1948,f835])).

fof(f1597,plain,
    ( ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1152,f1423])).

fof(f1152,plain,
    ( ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f354,f1096])).

fof(f354,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK16(X0),u1_struct_0(X0))
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f235])).

fof(f2707,plain,
    ( spl22_250
    | ~ spl22_249
    | ~ spl22_140
    | ~ spl22_162 ),
    inference(avatar_split_clause,[],[f1684,f1404,f1205,f2698,f2705])).

fof(f2705,plain,
    ( spl22_250
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_250])])).

fof(f2698,plain,
    ( spl22_249
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK17 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_249])])).

fof(f1684,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK17
    | u1_pre_topc(sK0) = u1_pre_topc(sK17)
    | ~ spl22_140
    | ~ spl22_162 ),
    inference(superposition,[],[f1227,f1405])).

fof(f2700,plain,
    ( spl22_246
    | ~ spl22_249
    | ~ spl22_132
    | ~ spl22_162 ),
    inference(avatar_split_clause,[],[f1683,f1404,f1051,f2698,f2692])).

fof(f2692,plain,
    ( spl22_246
  <=> u1_struct_0(sK0) = u1_struct_0(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_246])])).

fof(f1683,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK17
    | u1_struct_0(sK0) = u1_struct_0(sK17)
    | ~ spl22_132
    | ~ spl22_162 ),
    inference(superposition,[],[f1075,f1405])).

fof(f2687,plain,
    ( spl22_244
    | ~ spl22_243
    | ~ spl22_140
    | ~ spl22_160 ),
    inference(avatar_split_clause,[],[f1660,f1397,f1205,f2671,f2685])).

fof(f2685,plain,
    ( spl22_244
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_244])])).

fof(f2671,plain,
    ( spl22_243
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_243])])).

fof(f1660,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK8
    | u1_pre_topc(sK0) = u1_pre_topc(sK8)
    | ~ spl22_140
    | ~ spl22_160 ),
    inference(superposition,[],[f1227,f1398])).

fof(f2673,plain,
    ( spl22_240
    | ~ spl22_243
    | ~ spl22_132
    | ~ spl22_160 ),
    inference(avatar_split_clause,[],[f1659,f1397,f1051,f2671,f2665])).

fof(f2665,plain,
    ( spl22_240
  <=> u1_struct_0(sK0) = u1_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_240])])).

fof(f1659,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK8
    | u1_struct_0(sK0) = u1_struct_0(sK8)
    | ~ spl22_132
    | ~ spl22_160 ),
    inference(superposition,[],[f1075,f1398])).

fof(f2660,plain,
    ( spl22_118
    | spl22_238
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1605,f1422,f1095,f2658,f835])).

fof(f1605,plain,
    ( m1_subset_1(sK12(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK1)
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1144,f1423])).

fof(f1144,plain,
    ( m1_subset_1(sK12(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f337,f1096])).

fof(f2653,plain,
    ( spl22_236
    | ~ spl22_235
    | ~ spl22_140
    | ~ spl22_158 ),
    inference(avatar_split_clause,[],[f1649,f1390,f1205,f2644,f2651])).

fof(f2651,plain,
    ( spl22_236
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_236])])).

fof(f2644,plain,
    ( spl22_235
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_235])])).

fof(f1649,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK7
    | u1_pre_topc(sK0) = u1_pre_topc(sK7)
    | ~ spl22_140
    | ~ spl22_158 ),
    inference(superposition,[],[f1227,f1391])).

fof(f2646,plain,
    ( spl22_232
    | ~ spl22_235
    | ~ spl22_132
    | ~ spl22_158 ),
    inference(avatar_split_clause,[],[f1648,f1390,f1051,f2644,f2638])).

fof(f2638,plain,
    ( spl22_232
  <=> u1_struct_0(sK0) = u1_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_232])])).

fof(f1648,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK7
    | u1_struct_0(sK0) = u1_struct_0(sK7)
    | ~ spl22_132
    | ~ spl22_158 ),
    inference(superposition,[],[f1075,f1391])).

fof(f2633,plain,
    ( spl22_230
    | ~ spl22_229
    | ~ spl22_140
    | ~ spl22_156 ),
    inference(avatar_split_clause,[],[f1498,f1383,f1205,f2624,f2631])).

fof(f2631,plain,
    ( spl22_230
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_230])])).

fof(f2624,plain,
    ( spl22_229
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_229])])).

fof(f1498,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK6
    | u1_pre_topc(sK0) = u1_pre_topc(sK6)
    | ~ spl22_140
    | ~ spl22_156 ),
    inference(superposition,[],[f1227,f1384])).

fof(f2626,plain,
    ( spl22_226
    | ~ spl22_229
    | ~ spl22_132
    | ~ spl22_156 ),
    inference(avatar_split_clause,[],[f1497,f1383,f1051,f2624,f2618])).

fof(f2618,plain,
    ( spl22_226
  <=> u1_struct_0(sK0) = u1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_226])])).

fof(f1497,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK6
    | u1_struct_0(sK0) = u1_struct_0(sK6)
    | ~ spl22_132
    | ~ spl22_156 ),
    inference(superposition,[],[f1075,f1384])).

fof(f2613,plain,
    ( spl22_224
    | ~ spl22_223
    | ~ spl22_140
    | ~ spl22_152 ),
    inference(avatar_split_clause,[],[f1487,f1369,f1205,f2603,f2611])).

fof(f2611,plain,
    ( spl22_224
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_224])])).

fof(f2603,plain,
    ( spl22_223
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_223])])).

fof(f1487,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK5
    | u1_pre_topc(sK0) = u1_pre_topc(sK5)
    | ~ spl22_140
    | ~ spl22_152 ),
    inference(superposition,[],[f1227,f1370])).

fof(f2605,plain,
    ( spl22_220
    | ~ spl22_223
    | ~ spl22_132
    | ~ spl22_152 ),
    inference(avatar_split_clause,[],[f1486,f1369,f1051,f2603,f2597])).

fof(f2597,plain,
    ( spl22_220
  <=> u1_struct_0(sK0) = u1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_220])])).

fof(f1486,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK5
    | u1_struct_0(sK0) = u1_struct_0(sK5)
    | ~ spl22_132
    | ~ spl22_152 ),
    inference(superposition,[],[f1075,f1370])).

fof(f2592,plain,
    ( spl22_218
    | ~ spl22_213
    | ~ spl22_140
    | ~ spl22_150 ),
    inference(avatar_split_clause,[],[f1476,f1362,f1205,f2570,f2590])).

fof(f2590,plain,
    ( spl22_218
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_218])])).

fof(f2570,plain,
    ( spl22_213
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_213])])).

fof(f1476,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK4
    | u1_pre_topc(sK0) = u1_pre_topc(sK4)
    | ~ spl22_140
    | ~ spl22_150 ),
    inference(superposition,[],[f1227,f1363])).

fof(f2585,plain,
    ( ~ spl22_215
    | spl22_216
    | spl22_181
    | ~ spl22_182
    | spl22_189
    | spl22_195
    | ~ spl22_200 ),
    inference(avatar_split_clause,[],[f2558,f2519,f2417,f2079,f1668,f1665,f2583,f2577])).

fof(f2558,plain,
    ( v1_xboole_0(sK13(sK1))
    | ~ v1_zfmisc_1(sK13(sK1))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_189
    | ~ spl22_195
    | ~ spl22_200 ),
    inference(subsumption_resolution,[],[f2557,f2418])).

fof(f2557,plain,
    ( v1_xboole_0(sK13(sK1))
    | v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK13(sK1))
    | ~ spl22_181
    | ~ spl22_182
    | ~ spl22_189
    | ~ spl22_200 ),
    inference(subsumption_resolution,[],[f2556,f1666])).

fof(f2556,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(sK13(sK1))
    | v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK13(sK1))
    | ~ spl22_182
    | ~ spl22_189
    | ~ spl22_200 ),
    inference(subsumption_resolution,[],[f2555,f1669])).

fof(f2555,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK13(sK1))
    | v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK13(sK1))
    | ~ spl22_189
    | ~ spl22_200 ),
    inference(subsumption_resolution,[],[f2549,f2080])).

fof(f2572,plain,
    ( spl22_210
    | ~ spl22_213
    | ~ spl22_132
    | ~ spl22_150 ),
    inference(avatar_split_clause,[],[f1475,f1362,f1051,f2570,f2564])).

fof(f2564,plain,
    ( spl22_210
  <=> u1_struct_0(sK0) = u1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_210])])).

fof(f1475,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK4
    | u1_struct_0(sK0) = u1_struct_0(sK4)
    | ~ spl22_132
    | ~ spl22_150 ),
    inference(superposition,[],[f1075,f1363])).

fof(f2548,plain,
    ( spl22_208
    | ~ spl22_207
    | ~ spl22_140
    | ~ spl22_148 ),
    inference(avatar_split_clause,[],[f1462,f1355,f1205,f2539,f2546])).

fof(f2546,plain,
    ( spl22_208
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_208])])).

fof(f2539,plain,
    ( spl22_207
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_207])])).

fof(f1462,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK3
    | u1_pre_topc(sK0) = u1_pre_topc(sK3)
    | ~ spl22_140
    | ~ spl22_148 ),
    inference(superposition,[],[f1227,f1356])).

fof(f2541,plain,
    ( spl22_204
    | ~ spl22_207
    | ~ spl22_132
    | ~ spl22_148 ),
    inference(avatar_split_clause,[],[f1461,f1355,f1051,f2539,f2533])).

fof(f2533,plain,
    ( spl22_204
  <=> u1_struct_0(sK0) = u1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_204])])).

fof(f1461,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK3
    | u1_struct_0(sK0) = u1_struct_0(sK3)
    | ~ spl22_132
    | ~ spl22_148 ),
    inference(superposition,[],[f1075,f1356])).

fof(f2528,plain,
    ( spl22_202
    | ~ spl22_199
    | ~ spl22_140
    | ~ spl22_146 ),
    inference(avatar_split_clause,[],[f1451,f1270,f1205,f2512,f2526])).

fof(f2526,plain,
    ( spl22_202
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_202])])).

fof(f2512,plain,
    ( spl22_199
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_199])])).

fof(f1451,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK2
    | u1_pre_topc(sK0) = u1_pre_topc(sK2)
    | ~ spl22_140
    | ~ spl22_146 ),
    inference(superposition,[],[f1227,f1271])).

fof(f2521,plain,
    ( spl22_118
    | spl22_200
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1604,f1422,f1095,f2519,f835])).

fof(f1604,plain,
    ( m1_subset_1(sK13(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK1)
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1145,f1423])).

fof(f1145,plain,
    ( m1_subset_1(sK13(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f340,f1096])).

fof(f2514,plain,
    ( spl22_196
    | ~ spl22_199
    | ~ spl22_132
    | ~ spl22_146 ),
    inference(avatar_split_clause,[],[f1450,f1270,f1051,f2512,f2506])).

fof(f2506,plain,
    ( spl22_196
  <=> u1_struct_0(sK0) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_196])])).

fof(f1450,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK2
    | u1_struct_0(sK0) = u1_struct_0(sK2)
    | ~ spl22_132
    | ~ spl22_146 ),
    inference(superposition,[],[f1075,f1271])).

fof(f2459,plain,
    ( spl22_184
    | spl22_192
    | spl22_119
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1921,f1422,f1095,f832,f2367,f1948])).

fof(f1921,plain,
    ( v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1920,f833])).

fof(f1920,plain,
    ( v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1918,f1423])).

fof(f1918,plain,
    ( v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f957,f1096])).

fof(f957,plain,(
    ! [X0] :
      ( v1_subset_1(sK12(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f956,f339])).

fof(f956,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_subset_1(sK12(X0),u1_struct_0(X0))
      | ~ v1_zfmisc_1(sK12(X0)) ) ),
    inference(subsumption_resolution,[],[f955,f338])).

fof(f955,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK12(X0))
      | v1_subset_1(sK12(X0),u1_struct_0(X0))
      | ~ v1_zfmisc_1(sK12(X0)) ) ),
    inference(duplicate_literal_removal,[],[f946])).

fof(f946,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK12(X0))
      | v1_subset_1(sK12(X0),u1_struct_0(X0))
      | ~ v1_zfmisc_1(sK12(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f355,f337])).

fof(f2419,plain,
    ( ~ spl22_185
    | ~ spl22_195
    | spl22_119
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1916,f1422,f1095,f832,f2417,f1945])).

fof(f1916,plain,
    ( ~ v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | ~ v7_struct_0(sK1)
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1915,f833])).

fof(f1915,plain,
    ( ~ v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1819,f1423])).

fof(f1819,plain,
    ( ~ v1_subset_1(sK13(sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f930,f1096])).

fof(f2372,plain,
    ( ~ spl22_185
    | ~ spl22_193
    | spl22_119
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1914,f1422,f1095,f832,f2370,f1945])).

fof(f1914,plain,
    ( ~ v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | ~ v7_struct_0(sK1)
    | ~ spl22_119
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1913,f833])).

fof(f1913,plain,
    ( ~ v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1818,f1423])).

fof(f1818,plain,
    ( ~ v1_subset_1(sK12(sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f929,f1096])).

fof(f929,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK12(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f928,f338])).

fof(f928,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK12(X0))
      | ~ v1_subset_1(sK12(X0),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f919])).

fof(f919,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK12(X0))
      | ~ v1_subset_1(sK12(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f336,f337])).

fof(f2320,plain,
    ( ~ spl22_119
    | spl22_190
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1590,f1422,f1095,f2318,f832])).

fof(f2318,plain,
    ( spl22_190
  <=> u1_struct_0(sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_190])])).

fof(f1590,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | ~ v2_struct_0(sK1)
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(forward_demodulation,[],[f1499,f1096])).

fof(f1499,plain,
    ( ~ v2_struct_0(sK1)
    | u1_struct_0(sK1) = k1_xboole_0
    | ~ spl22_168 ),
    inference(resolution,[],[f1423,f781])).

fof(f781,plain,(
    ! [X2] :
      ( ~ l1_struct_0(X2)
      | ~ v2_struct_0(X2)
      | u1_struct_0(X2) = k1_xboole_0 ) ),
    inference(resolution,[],[f333,f301])).

fof(f333,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f217])).

fof(f217,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f216])).

fof(f216,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f92])).

fof(f92,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',fc1_struct_0)).

fof(f2250,plain,
    ( ~ spl22_119
    | spl22_170
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1611,f1422,f1095,f1431,f832])).

fof(f1431,plain,
    ( spl22_170
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_170])])).

fof(f1611,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_struct_0(sK1)
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1140,f1423])).

fof(f1140,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | ~ v2_struct_0(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f333,f1096])).

fof(f2204,plain,
    ( spl22_118
    | ~ spl22_171
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1603,f1422,f1095,f1428,f835])).

fof(f1603,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1146,f1423])).

fof(f1146,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f342,f1096])).

fof(f342,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f229])).

fof(f229,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f228])).

fof(f228,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f95])).

fof(f95,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',fc2_struct_0)).

fof(f2167,plain,
    ( ~ spl22_185
    | spl22_186
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1589,f1422,f1095,f1951,f1945])).

fof(f1589,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v7_struct_0(sK1)
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1141,f1423])).

fof(f1141,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f334,f1096])).

fof(f2081,plain,
    ( ~ spl22_189
    | ~ spl22_182
    | spl22_187 ),
    inference(avatar_split_clause,[],[f2043,f1954,f1668,f2079])).

fof(f2043,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl22_182
    | ~ spl22_187 ),
    inference(subsumption_resolution,[],[f2042,f1669])).

fof(f2042,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ spl22_187 ),
    inference(resolution,[],[f1955,f334])).

fof(f1955,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl22_187 ),
    inference(avatar_component_clause,[],[f1954])).

fof(f1956,plain,
    ( spl22_184
    | ~ spl22_187
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1588,f1422,f1095,f1954,f1948])).

fof(f1588,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1154,f1423])).

fof(f1154,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl22_136 ),
    inference(superposition,[],[f357,f1096])).

fof(f1736,plain,
    ( ~ spl22_6
    | spl22_183 ),
    inference(avatar_contradiction_clause,[],[f1735])).

fof(f1735,plain,
    ( $false
    | ~ spl22_6
    | ~ spl22_183 ),
    inference(subsumption_resolution,[],[f1734,f399])).

fof(f1734,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl22_183 ),
    inference(resolution,[],[f1672,f372])).

fof(f1672,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl22_183 ),
    inference(avatar_component_clause,[],[f1671])).

fof(f1671,plain,
    ( spl22_183
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_183])])).

fof(f1673,plain,
    ( ~ spl22_181
    | ~ spl22_183
    | spl22_171 ),
    inference(avatar_split_clause,[],[f1632,f1428,f1671,f1665])).

fof(f1632,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v2_struct_0(sK0)
    | ~ spl22_171 ),
    inference(resolution,[],[f1429,f333])).

fof(f1587,plain,
    ( spl22_178
    | ~ spl22_118
    | ~ spl22_136
    | ~ spl22_168
    | ~ spl22_170 ),
    inference(avatar_split_clause,[],[f1529,f1431,f1422,f1095,f835,f1585])).

fof(f1529,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl22_118
    | ~ spl22_136
    | ~ spl22_168
    | ~ spl22_170 ),
    inference(backward_demodulation,[],[f1501,f1432])).

fof(f1432,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl22_170 ),
    inference(avatar_component_clause,[],[f1431])).

fof(f1501,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | ~ spl22_118
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(backward_demodulation,[],[f1500,f1096])).

fof(f1500,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | ~ spl22_118
    | ~ spl22_168 ),
    inference(subsumption_resolution,[],[f1499,f836])).

fof(f836,plain,
    ( v2_struct_0(sK1)
    | ~ spl22_118 ),
    inference(avatar_component_clause,[],[f835])).

fof(f1580,plain,
    ( spl22_176
    | ~ spl22_118
    | ~ spl22_122
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1504,f1422,f1095,f881,f835,f1578])).

fof(f1504,plain,
    ( v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl22_118
    | ~ spl22_122
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(backward_demodulation,[],[f1501,f882])).

fof(f1573,plain,
    ( ~ spl22_175
    | ~ spl22_118
    | spl22_121
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(avatar_split_clause,[],[f1503,f1422,f1095,f841,f835,f1571])).

fof(f1571,plain,
    ( spl22_175
  <=> ~ v2_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_175])])).

fof(f1503,plain,
    ( ~ v2_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl22_118
    | ~ spl22_121
    | ~ spl22_136
    | ~ spl22_168 ),
    inference(backward_demodulation,[],[f1501,f842])).

fof(f1465,plain,
    ( ~ spl22_0
    | spl22_169 ),
    inference(avatar_contradiction_clause,[],[f1464])).

fof(f1464,plain,
    ( $false
    | ~ spl22_0
    | ~ spl22_169 ),
    inference(subsumption_resolution,[],[f1463,f378])).

fof(f1463,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl22_169 ),
    inference(resolution,[],[f1426,f372])).

fof(f1426,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl22_169 ),
    inference(avatar_component_clause,[],[f1425])).

fof(f1425,plain,
    ( spl22_169
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_169])])).

fof(f1440,plain,
    ( spl22_172
    | ~ spl22_102
    | ~ spl22_108 ),
    inference(avatar_split_clause,[],[f874,f755,f734,f1438])).

fof(f755,plain,
    ( spl22_108
  <=> v1_pre_topc(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_108])])).

fof(f874,plain,
    ( g1_pre_topc(u1_struct_0(sK20),u1_pre_topc(sK20)) = sK20
    | ~ spl22_102
    | ~ spl22_108 ),
    inference(subsumption_resolution,[],[f861,f735])).

fof(f861,plain,
    ( ~ l1_pre_topc(sK20)
    | g1_pre_topc(u1_struct_0(sK20),u1_pre_topc(sK20)) = sK20
    | ~ spl22_108 ),
    inference(resolution,[],[f302,f756])).

fof(f756,plain,
    ( v1_pre_topc(sK20)
    | ~ spl22_108 ),
    inference(avatar_component_clause,[],[f755])).

fof(f1433,plain,
    ( ~ spl22_169
    | spl22_170
    | ~ spl22_118
    | ~ spl22_136 ),
    inference(avatar_split_clause,[],[f1201,f1095,f835,f1431,f1425])).

fof(f1201,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | ~ spl22_118
    | ~ spl22_136 ),
    inference(subsumption_resolution,[],[f1140,f836])).

fof(f1420,plain,
    ( spl22_166
    | ~ spl22_94
    | ~ spl22_100 ),
    inference(avatar_split_clause,[],[f873,f727,f706,f1418])).

fof(f727,plain,
    ( spl22_100
  <=> v1_pre_topc(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_100])])).

fof(f873,plain,
    ( g1_pre_topc(u1_struct_0(sK19),u1_pre_topc(sK19)) = sK19
    | ~ spl22_94
    | ~ spl22_100 ),
    inference(subsumption_resolution,[],[f860,f707])).

fof(f860,plain,
    ( ~ l1_pre_topc(sK19)
    | g1_pre_topc(u1_struct_0(sK19),u1_pre_topc(sK19)) = sK19
    | ~ spl22_100 ),
    inference(resolution,[],[f302,f728])).

fof(f728,plain,
    ( v1_pre_topc(sK19)
    | ~ spl22_100 ),
    inference(avatar_component_clause,[],[f727])).

fof(f1413,plain,
    ( spl22_164
    | ~ spl22_90
    | ~ spl22_92 ),
    inference(avatar_split_clause,[],[f872,f699,f692,f1411])).

fof(f699,plain,
    ( spl22_92
  <=> v1_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_92])])).

fof(f872,plain,
    ( g1_pre_topc(u1_struct_0(sK18),u1_pre_topc(sK18)) = sK18
    | ~ spl22_90
    | ~ spl22_92 ),
    inference(subsumption_resolution,[],[f859,f693])).

fof(f859,plain,
    ( ~ l1_pre_topc(sK18)
    | g1_pre_topc(u1_struct_0(sK18),u1_pre_topc(sK18)) = sK18
    | ~ spl22_92 ),
    inference(resolution,[],[f302,f700])).

fof(f700,plain,
    ( v1_pre_topc(sK18)
    | ~ spl22_92 ),
    inference(avatar_component_clause,[],[f699])).

fof(f1406,plain,
    ( spl22_162
    | ~ spl22_84
    | ~ spl22_88 ),
    inference(avatar_split_clause,[],[f871,f685,f671,f1404])).

fof(f685,plain,
    ( spl22_88
  <=> v1_pre_topc(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_88])])).

fof(f871,plain,
    ( g1_pre_topc(u1_struct_0(sK17),u1_pre_topc(sK17)) = sK17
    | ~ spl22_84
    | ~ spl22_88 ),
    inference(subsumption_resolution,[],[f858,f672])).

fof(f858,plain,
    ( ~ l1_pre_topc(sK17)
    | g1_pre_topc(u1_struct_0(sK17),u1_pre_topc(sK17)) = sK17
    | ~ spl22_88 ),
    inference(resolution,[],[f302,f686])).

fof(f686,plain,
    ( v1_pre_topc(sK17)
    | ~ spl22_88 ),
    inference(avatar_component_clause,[],[f685])).

fof(f1399,plain,
    ( spl22_160
    | ~ spl22_74
    | ~ spl22_80 ),
    inference(avatar_split_clause,[],[f870,f657,f636,f1397])).

fof(f657,plain,
    ( spl22_80
  <=> v1_pre_topc(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_80])])).

fof(f870,plain,
    ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) = sK8
    | ~ spl22_74
    | ~ spl22_80 ),
    inference(subsumption_resolution,[],[f857,f637])).

fof(f857,plain,
    ( ~ l1_pre_topc(sK8)
    | g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) = sK8
    | ~ spl22_80 ),
    inference(resolution,[],[f302,f658])).

fof(f658,plain,
    ( v1_pre_topc(sK8)
    | ~ spl22_80 ),
    inference(avatar_component_clause,[],[f657])).

fof(f1392,plain,
    ( spl22_158
    | ~ spl22_64
    | ~ spl22_70 ),
    inference(avatar_split_clause,[],[f869,f622,f601,f1390])).

fof(f622,plain,
    ( spl22_70
  <=> v1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_70])])).

fof(f869,plain,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7
    | ~ spl22_64
    | ~ spl22_70 ),
    inference(subsumption_resolution,[],[f856,f602])).

fof(f856,plain,
    ( ~ l1_pre_topc(sK7)
    | g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7
    | ~ spl22_70 ),
    inference(resolution,[],[f302,f623])).

fof(f623,plain,
    ( v1_pre_topc(sK7)
    | ~ spl22_70 ),
    inference(avatar_component_clause,[],[f622])).

fof(f1385,plain,
    ( spl22_156
    | ~ spl22_56
    | ~ spl22_60 ),
    inference(avatar_split_clause,[],[f868,f587,f573,f1383])).

fof(f587,plain,
    ( spl22_60
  <=> v1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_60])])).

fof(f868,plain,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK6
    | ~ spl22_56
    | ~ spl22_60 ),
    inference(subsumption_resolution,[],[f855,f574])).

fof(f855,plain,
    ( ~ l1_pre_topc(sK6)
    | g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK6
    | ~ spl22_60 ),
    inference(resolution,[],[f302,f588])).

fof(f588,plain,
    ( v1_pre_topc(sK6)
    | ~ spl22_60 ),
    inference(avatar_component_clause,[],[f587])).

fof(f1378,plain,
    ( spl22_154
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(avatar_split_clause,[],[f1348,f1254,f377,f1376])).

fof(f1376,plain,
    ( spl22_154
  <=> v1_tops_2(u1_pre_topc(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_154])])).

fof(f1348,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK1)
    | ~ spl22_0
    | ~ spl22_144 ),
    inference(subsumption_resolution,[],[f1291,f378])).

fof(f1291,plain,
    ( v1_tops_2(u1_pre_topc(sK0),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl22_144 ),
    inference(superposition,[],[f332,f1255])).

fof(f1371,plain,
    ( spl22_152
    | ~ spl22_44
    | ~ spl22_48 ),
    inference(avatar_split_clause,[],[f867,f545,f531,f1369])).

fof(f545,plain,
    ( spl22_48
  <=> v1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_48])])).

fof(f867,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK5
    | ~ spl22_44
    | ~ spl22_48 ),
    inference(subsumption_resolution,[],[f854,f532])).

fof(f854,plain,
    ( ~ l1_pre_topc(sK5)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK5
    | ~ spl22_48 ),
    inference(resolution,[],[f302,f546])).

fof(f546,plain,
    ( v1_pre_topc(sK5)
    | ~ spl22_48 ),
    inference(avatar_component_clause,[],[f545])).

fof(f1364,plain,
    ( spl22_150
    | ~ spl22_32
    | ~ spl22_36 ),
    inference(avatar_split_clause,[],[f866,f503,f489,f1362])).

fof(f503,plain,
    ( spl22_36
  <=> v1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_36])])).

fof(f866,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4
    | ~ spl22_32
    | ~ spl22_36 ),
    inference(subsumption_resolution,[],[f853,f490])).

fof(f853,plain,
    ( ~ l1_pre_topc(sK4)
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4
    | ~ spl22_36 ),
    inference(resolution,[],[f302,f504])).

fof(f504,plain,
    ( v1_pre_topc(sK4)
    | ~ spl22_36 ),
    inference(avatar_component_clause,[],[f503])).

fof(f1357,plain,
    ( spl22_148
    | ~ spl22_20
    | ~ spl22_24 ),
    inference(avatar_split_clause,[],[f865,f461,f447,f1355])).

fof(f461,plain,
    ( spl22_24
  <=> v1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_24])])).

fof(f865,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
    | ~ spl22_20
    | ~ spl22_24 ),
    inference(subsumption_resolution,[],[f852,f448])).

fof(f852,plain,
    ( ~ l1_pre_topc(sK3)
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
    | ~ spl22_24 ),
    inference(resolution,[],[f302,f462])).

fof(f462,plain,
    ( v1_pre_topc(sK3)
    | ~ spl22_24 ),
    inference(avatar_component_clause,[],[f461])).

fof(f1272,plain,
    ( spl22_146
    | ~ spl22_8
    | ~ spl22_12 ),
    inference(avatar_split_clause,[],[f864,f419,f405,f1270])).

fof(f419,plain,
    ( spl22_12
  <=> v1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_12])])).

fof(f864,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2
    | ~ spl22_8
    | ~ spl22_12 ),
    inference(subsumption_resolution,[],[f851,f406])).

fof(f851,plain,
    ( ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK2
    | ~ spl22_12 ),
    inference(resolution,[],[f302,f420])).

fof(f420,plain,
    ( v1_pre_topc(sK2)
    | ~ spl22_12 ),
    inference(avatar_component_clause,[],[f419])).

fof(f1256,plain,
    ( spl22_144
    | ~ spl22_140 ),
    inference(avatar_split_clause,[],[f1209,f1205,f1254])).

fof(f1249,plain,
    ( spl22_142
    | ~ spl22_138
    | ~ spl22_140 ),
    inference(avatar_split_clause,[],[f1213,f1205,f1102,f1247])).

fof(f1247,plain,
    ( spl22_142
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_142])])).

fof(f1102,plain,
    ( spl22_138
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_138])])).

fof(f1213,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl22_138
    | ~ spl22_140 ),
    inference(backward_demodulation,[],[f1209,f1103])).

fof(f1103,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl22_138 ),
    inference(avatar_component_clause,[],[f1102])).

fof(f1207,plain,
    ( spl22_140
    | ~ spl22_139
    | ~ spl22_112
    | ~ spl22_132 ),
    inference(avatar_split_clause,[],[f1073,f1051,f769,f1099,f1205])).

fof(f1099,plain,
    ( spl22_139
  <=> ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_139])])).

fof(f769,plain,
    ( spl22_112
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_112])])).

fof(f1073,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_pre_topc(sK1) = X1 )
    | ~ spl22_112
    | ~ spl22_132 ),
    inference(backward_demodulation,[],[f1070,f916])).

fof(f916,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | u1_pre_topc(sK1) = X1 )
    | ~ spl22_112 ),
    inference(superposition,[],[f298,f770])).

fof(f770,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl22_112 ),
    inference(avatar_component_clause,[],[f769])).

fof(f1104,plain,
    ( spl22_138
    | ~ spl22_130
    | ~ spl22_132 ),
    inference(avatar_split_clause,[],[f1074,f1051,f1045,f1102])).

fof(f1045,plain,
    ( spl22_130
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_130])])).

fof(f1074,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl22_130
    | ~ spl22_132 ),
    inference(backward_demodulation,[],[f1070,f1046])).

fof(f1046,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl22_130 ),
    inference(avatar_component_clause,[],[f1045])).

fof(f1097,plain,
    ( spl22_136
    | ~ spl22_132 ),
    inference(avatar_split_clause,[],[f1070,f1051,f1095])).

fof(f1085,plain,
    ( spl22_134
    | ~ spl22_112
    | ~ spl22_132 ),
    inference(avatar_split_clause,[],[f1071,f1051,f769,f1083])).

fof(f1083,plain,
    ( spl22_134
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_134])])).

fof(f1071,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ spl22_112
    | ~ spl22_132 ),
    inference(backward_demodulation,[],[f1070,f770])).

fof(f1056,plain,
    ( ~ spl22_0
    | spl22_131 ),
    inference(avatar_contradiction_clause,[],[f1055])).

fof(f1055,plain,
    ( $false
    | ~ spl22_0
    | ~ spl22_131 ),
    inference(subsumption_resolution,[],[f1054,f378])).

fof(f1054,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl22_131 ),
    inference(resolution,[],[f1049,f331])).

fof(f1049,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl22_131 ),
    inference(avatar_component_clause,[],[f1048])).

fof(f1048,plain,
    ( spl22_131
  <=> ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_131])])).

fof(f1053,plain,
    ( ~ spl22_131
    | spl22_132
    | ~ spl22_112 ),
    inference(avatar_split_clause,[],[f913,f769,f1051,f1048])).

fof(f913,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | u1_struct_0(sK1) = X0 )
    | ~ spl22_112 ),
    inference(superposition,[],[f297,f770])).

fof(f1033,plain,
    ( spl22_128
    | ~ spl22_8
    | spl22_11
    | ~ spl22_14
    | ~ spl22_16
    | ~ spl22_18 ),
    inference(avatar_split_clause,[],[f891,f440,f433,f426,f412,f405,f1031])).

fof(f1031,plain,
    ( spl22_128
  <=> v7_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_128])])).

fof(f412,plain,
    ( spl22_11
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_11])])).

fof(f426,plain,
    ( spl22_14
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_14])])).

fof(f433,plain,
    ( spl22_16
  <=> v1_tdlat_3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_16])])).

fof(f440,plain,
    ( spl22_18
  <=> v2_tdlat_3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_18])])).

fof(f891,plain,
    ( v7_struct_0(sK2)
    | ~ spl22_8
    | ~ spl22_11
    | ~ spl22_14
    | ~ spl22_16
    | ~ spl22_18 ),
    inference(subsumption_resolution,[],[f890,f406])).

fof(f890,plain,
    ( ~ l1_pre_topc(sK2)
    | v7_struct_0(sK2)
    | ~ spl22_11
    | ~ spl22_14
    | ~ spl22_16
    | ~ spl22_18 ),
    inference(subsumption_resolution,[],[f889,f434])).

fof(f434,plain,
    ( v1_tdlat_3(sK2)
    | ~ spl22_16 ),
    inference(avatar_component_clause,[],[f433])).

fof(f889,plain,
    ( ~ v1_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | v7_struct_0(sK2)
    | ~ spl22_11
    | ~ spl22_14
    | ~ spl22_18 ),
    inference(subsumption_resolution,[],[f888,f427])).

fof(f427,plain,
    ( v2_pre_topc(sK2)
    | ~ spl22_14 ),
    inference(avatar_component_clause,[],[f426])).

fof(f888,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ v1_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | v7_struct_0(sK2)
    | ~ spl22_11
    | ~ spl22_18 ),
    inference(subsumption_resolution,[],[f884,f413])).

fof(f413,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl22_11 ),
    inference(avatar_component_clause,[],[f412])).

fof(f884,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ v1_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | v7_struct_0(sK2)
    | ~ spl22_18 ),
    inference(resolution,[],[f286,f441])).

fof(f441,plain,
    ( v2_tdlat_3(sK2)
    | ~ spl22_18 ),
    inference(avatar_component_clause,[],[f440])).

fof(f286,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f184])).

fof(f184,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f183])).

fof(f183,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',cc2_tex_1)).

fof(f1004,plain,
    ( ~ spl22_127
    | ~ spl22_32
    | spl22_35
    | ~ spl22_38
    | spl22_41 ),
    inference(avatar_split_clause,[],[f818,f517,f510,f496,f489,f1002])).

fof(f510,plain,
    ( spl22_38
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_38])])).

fof(f517,plain,
    ( spl22_41
  <=> ~ v1_tdlat_3(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_41])])).

fof(f818,plain,
    ( ~ v7_struct_0(sK4)
    | ~ spl22_32
    | ~ spl22_35
    | ~ spl22_38
    | ~ spl22_41 ),
    inference(subsumption_resolution,[],[f817,f490])).

fof(f817,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v7_struct_0(sK4)
    | ~ spl22_35
    | ~ spl22_38
    | ~ spl22_41 ),
    inference(subsumption_resolution,[],[f816,f511])).

fof(f511,plain,
    ( v2_pre_topc(sK4)
    | ~ spl22_38 ),
    inference(avatar_component_clause,[],[f510])).

fof(f816,plain,
    ( ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v7_struct_0(sK4)
    | ~ spl22_35
    | ~ spl22_41 ),
    inference(subsumption_resolution,[],[f812,f497])).

fof(f812,plain,
    ( v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v7_struct_0(sK4)
    | ~ spl22_41 ),
    inference(resolution,[],[f288,f518])).

fof(f518,plain,
    ( ~ v1_tdlat_3(sK4)
    | ~ spl22_41 ),
    inference(avatar_component_clause,[],[f517])).

fof(f288,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f188,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f187])).

fof(f187,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( ~ v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',cc3_tex_1)).

fof(f983,plain,
    ( ~ spl22_125
    | ~ spl22_44
    | spl22_47
    | ~ spl22_50
    | spl22_55 ),
    inference(avatar_split_clause,[],[f811,f566,f552,f538,f531,f981])).

fof(f552,plain,
    ( spl22_50
  <=> v2_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_50])])).

fof(f566,plain,
    ( spl22_55
  <=> ~ v2_tdlat_3(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_55])])).

fof(f811,plain,
    ( ~ v7_struct_0(sK5)
    | ~ spl22_44
    | ~ spl22_47
    | ~ spl22_50
    | ~ spl22_55 ),
    inference(subsumption_resolution,[],[f810,f532])).

fof(f810,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v7_struct_0(sK5)
    | ~ spl22_47
    | ~ spl22_50
    | ~ spl22_55 ),
    inference(subsumption_resolution,[],[f809,f553])).

fof(f553,plain,
    ( v2_pre_topc(sK5)
    | ~ spl22_50 ),
    inference(avatar_component_clause,[],[f552])).

fof(f809,plain,
    ( ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v7_struct_0(sK5)
    | ~ spl22_47
    | ~ spl22_55 ),
    inference(subsumption_resolution,[],[f803,f539])).

fof(f803,plain,
    ( v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v7_struct_0(sK5)
    | ~ spl22_55 ),
    inference(resolution,[],[f287,f567])).

fof(f567,plain,
    ( ~ v2_tdlat_3(sK5)
    | ~ spl22_55 ),
    inference(avatar_component_clause,[],[f566])).

fof(f287,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f186])).

fof(f186,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f185])).

fof(f185,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( ~ v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',cc4_tex_1)).

fof(f945,plain,
    ( spl22_118
    | spl22_122
    | ~ spl22_0
    | ~ spl22_112 ),
    inference(avatar_split_clause,[],[f845,f769,f377,f881,f835])).

fof(f845,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(sK1)
    | ~ spl22_0
    | ~ spl22_112 ),
    inference(subsumption_resolution,[],[f844,f378])).

fof(f844,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_112 ),
    inference(superposition,[],[f311,f770])).

fof(f311,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f209])).

fof(f209,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f208])).

fof(f208,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f101,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',fc7_pre_topc)).

fof(f912,plain,
    ( ~ spl22_2
    | ~ spl22_6
    | spl22_123 ),
    inference(avatar_contradiction_clause,[],[f911])).

fof(f911,plain,
    ( $false
    | ~ spl22_2
    | ~ spl22_6
    | ~ spl22_123 ),
    inference(subsumption_resolution,[],[f910,f385])).

fof(f910,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl22_6
    | ~ spl22_123 ),
    inference(subsumption_resolution,[],[f908,f399])).

fof(f908,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl22_123 ),
    inference(resolution,[],[f879,f308])).

fof(f308,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f207])).

fof(f879,plain,
    ( ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_123 ),
    inference(avatar_component_clause,[],[f878])).

fof(f878,plain,
    ( spl22_123
  <=> ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_123])])).

fof(f883,plain,
    ( spl22_122
    | ~ spl22_0
    | ~ spl22_112
    | spl22_119 ),
    inference(avatar_split_clause,[],[f846,f832,f769,f377,f881])).

fof(f846,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_0
    | ~ spl22_112
    | ~ spl22_119 ),
    inference(subsumption_resolution,[],[f845,f833])).

fof(f843,plain,
    ( spl22_118
    | ~ spl22_121
    | ~ spl22_0
    | ~ spl22_112 ),
    inference(avatar_split_clause,[],[f830,f769,f377,f841,f835])).

fof(f830,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(sK1)
    | ~ spl22_0
    | ~ spl22_112 ),
    inference(subsumption_resolution,[],[f829,f378])).

fof(f829,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl22_112 ),
    inference(superposition,[],[f310,f770])).

fof(f310,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f209])).

fof(f826,plain,
    ( ~ spl22_117
    | ~ spl22_20
    | spl22_23
    | ~ spl22_26
    | spl22_31 ),
    inference(avatar_split_clause,[],[f808,f482,f468,f454,f447,f824])).

fof(f468,plain,
    ( spl22_26
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_26])])).

fof(f482,plain,
    ( spl22_31
  <=> ~ v2_tdlat_3(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_31])])).

fof(f808,plain,
    ( ~ v7_struct_0(sK3)
    | ~ spl22_20
    | ~ spl22_23
    | ~ spl22_26
    | ~ spl22_31 ),
    inference(subsumption_resolution,[],[f807,f448])).

fof(f807,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v7_struct_0(sK3)
    | ~ spl22_23
    | ~ spl22_26
    | ~ spl22_31 ),
    inference(subsumption_resolution,[],[f806,f469])).

fof(f469,plain,
    ( v2_pre_topc(sK3)
    | ~ spl22_26 ),
    inference(avatar_component_clause,[],[f468])).

fof(f806,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v7_struct_0(sK3)
    | ~ spl22_23
    | ~ spl22_31 ),
    inference(subsumption_resolution,[],[f802,f455])).

fof(f802,plain,
    ( v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v7_struct_0(sK3)
    | ~ spl22_31 ),
    inference(resolution,[],[f287,f483])).

fof(f483,plain,
    ( ~ v2_tdlat_3(sK3)
    | ~ spl22_31 ),
    inference(avatar_component_clause,[],[f482])).

fof(f801,plain,
    ( spl22_114
    | ~ spl22_0
    | ~ spl22_112 ),
    inference(avatar_split_clause,[],[f794,f769,f377,f799])).

fof(f794,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl22_0
    | ~ spl22_112 ),
    inference(subsumption_resolution,[],[f793,f378])).

fof(f793,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl22_112 ),
    inference(superposition,[],[f791,f770])).

fof(f791,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f331,f307])).

fof(f771,plain,(
    spl22_112 ),
    inference(avatar_split_clause,[],[f244,f769])).

fof(f244,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f182])).

fof(f182,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f181])).

fof(f181,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_pre_topc(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_pre_topc(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_pre_topc(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',t12_tex_2)).

fof(f764,plain,(
    spl22_110 ),
    inference(avatar_split_clause,[],[f371,f762])).

fof(f762,plain,
    ( spl22_110
  <=> l1_pre_topc(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_110])])).

fof(f371,plain,(
    l1_pre_topc(sK21) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',existence_l1_pre_topc)).

fof(f757,plain,(
    spl22_108 ),
    inference(avatar_split_clause,[],[f370,f755])).

fof(f370,plain,(
    v1_pre_topc(sK20) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',rc2_tex_1)).

fof(f750,plain,(
    ~ spl22_107 ),
    inference(avatar_split_clause,[],[f369,f748])).

fof(f369,plain,(
    ~ v7_struct_0(sK20) ),
    inference(cnf_transformation,[],[f131])).

fof(f743,plain,(
    ~ spl22_105 ),
    inference(avatar_split_clause,[],[f368,f741])).

fof(f368,plain,(
    ~ v2_struct_0(sK20) ),
    inference(cnf_transformation,[],[f131])).

fof(f736,plain,(
    spl22_102 ),
    inference(avatar_split_clause,[],[f367,f734])).

fof(f367,plain,(
    l1_pre_topc(sK20) ),
    inference(cnf_transformation,[],[f131])).

fof(f729,plain,(
    spl22_100 ),
    inference(avatar_split_clause,[],[f366,f727])).

fof(f366,plain,(
    v1_pre_topc(sK19) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',rc1_tex_1)).

fof(f722,plain,(
    spl22_98 ),
    inference(avatar_split_clause,[],[f365,f720])).

fof(f720,plain,
    ( spl22_98
  <=> v7_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_98])])).

fof(f365,plain,(
    v7_struct_0(sK19) ),
    inference(cnf_transformation,[],[f119])).

fof(f715,plain,(
    ~ spl22_97 ),
    inference(avatar_split_clause,[],[f364,f713])).

fof(f713,plain,
    ( spl22_97
  <=> ~ v2_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_97])])).

fof(f364,plain,(
    ~ v2_struct_0(sK19) ),
    inference(cnf_transformation,[],[f119])).

fof(f708,plain,(
    spl22_94 ),
    inference(avatar_split_clause,[],[f363,f706])).

fof(f363,plain,(
    l1_pre_topc(sK19) ),
    inference(cnf_transformation,[],[f119])).

fof(f701,plain,(
    spl22_92 ),
    inference(avatar_split_clause,[],[f362,f699])).

fof(f362,plain,(
    v1_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',rc1_pre_topc)).

fof(f694,plain,(
    spl22_90 ),
    inference(avatar_split_clause,[],[f361,f692])).

fof(f361,plain,(
    l1_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f114])).

fof(f687,plain,(
    spl22_88 ),
    inference(avatar_split_clause,[],[f360,f685])).

fof(f360,plain,(
    v1_pre_topc(sK17) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',rc11_pre_topc)).

fof(f680,plain,(
    spl22_86 ),
    inference(avatar_split_clause,[],[f359,f678])).

fof(f359,plain,(
    v2_struct_0(sK17) ),
    inference(cnf_transformation,[],[f111])).

fof(f673,plain,(
    spl22_84 ),
    inference(avatar_split_clause,[],[f358,f671])).

fof(f358,plain,(
    l1_pre_topc(sK17) ),
    inference(cnf_transformation,[],[f111])).

fof(f666,plain,(
    spl22_82 ),
    inference(avatar_split_clause,[],[f285,f664])).

fof(f664,plain,
    ( spl22_82
  <=> v2_pre_topc(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_82])])).

fof(f285,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f147])).

fof(f147,axiom,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',rc4_tex_1)).

fof(f659,plain,(
    spl22_80 ),
    inference(avatar_split_clause,[],[f284,f657])).

fof(f284,plain,(
    v1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f147])).

fof(f652,plain,(
    ~ spl22_79 ),
    inference(avatar_split_clause,[],[f283,f650])).

fof(f283,plain,(
    ~ v7_struct_0(sK8) ),
    inference(cnf_transformation,[],[f147])).

fof(f645,plain,(
    ~ spl22_77 ),
    inference(avatar_split_clause,[],[f282,f643])).

fof(f282,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f147])).

fof(f638,plain,(
    spl22_74 ),
    inference(avatar_split_clause,[],[f281,f636])).

fof(f281,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f147])).

fof(f631,plain,(
    spl22_72 ),
    inference(avatar_split_clause,[],[f280,f629])).

fof(f629,plain,
    ( spl22_72
  <=> v2_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_72])])).

fof(f280,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f140])).

fof(f140,axiom,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',rc3_tex_1)).

fof(f624,plain,(
    spl22_70 ),
    inference(avatar_split_clause,[],[f279,f622])).

fof(f279,plain,(
    v1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f140])).

fof(f617,plain,(
    spl22_68 ),
    inference(avatar_split_clause,[],[f278,f615])).

fof(f615,plain,
    ( spl22_68
  <=> v7_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_68])])).

fof(f278,plain,(
    v7_struct_0(sK7) ),
    inference(cnf_transformation,[],[f140])).

fof(f610,plain,(
    ~ spl22_67 ),
    inference(avatar_split_clause,[],[f277,f608])).

fof(f608,plain,
    ( spl22_67
  <=> ~ v2_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_67])])).

fof(f277,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f140])).

fof(f603,plain,(
    spl22_64 ),
    inference(avatar_split_clause,[],[f276,f601])).

fof(f276,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f140])).

fof(f596,plain,(
    spl22_62 ),
    inference(avatar_split_clause,[],[f275,f594])).

fof(f594,plain,
    ( spl22_62
  <=> v2_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_62])])).

fof(f275,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f126])).

fof(f126,axiom,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',rc2_pre_topc)).

fof(f589,plain,(
    spl22_60 ),
    inference(avatar_split_clause,[],[f274,f587])).

fof(f274,plain,(
    v1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f126])).

fof(f582,plain,(
    ~ spl22_59 ),
    inference(avatar_split_clause,[],[f273,f580])).

fof(f580,plain,
    ( spl22_59
  <=> ~ v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_59])])).

fof(f273,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f126])).

fof(f575,plain,(
    spl22_56 ),
    inference(avatar_split_clause,[],[f272,f573])).

fof(f272,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f126])).

fof(f568,plain,(
    ~ spl22_55 ),
    inference(avatar_split_clause,[],[f271,f566])).

fof(f271,plain,(
    ~ v2_tdlat_3(sK5) ),
    inference(cnf_transformation,[],[f160])).

fof(f160,axiom,(
    ? [X0] :
      ( ~ v2_tdlat_3(X0)
      & ~ v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',rc7_tex_1)).

fof(f561,plain,(
    ~ spl22_53 ),
    inference(avatar_split_clause,[],[f270,f559])).

fof(f559,plain,
    ( spl22_53
  <=> ~ v1_tdlat_3(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_53])])).

fof(f270,plain,(
    ~ v1_tdlat_3(sK5) ),
    inference(cnf_transformation,[],[f160])).

fof(f554,plain,(
    spl22_50 ),
    inference(avatar_split_clause,[],[f269,f552])).

fof(f269,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f160])).

fof(f547,plain,(
    spl22_48 ),
    inference(avatar_split_clause,[],[f268,f545])).

fof(f268,plain,(
    v1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f160])).

fof(f540,plain,(
    ~ spl22_47 ),
    inference(avatar_split_clause,[],[f267,f538])).

fof(f267,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f160])).

fof(f533,plain,(
    spl22_44 ),
    inference(avatar_split_clause,[],[f266,f531])).

fof(f266,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f160])).

fof(f526,plain,(
    spl22_42 ),
    inference(avatar_split_clause,[],[f265,f524])).

fof(f524,plain,
    ( spl22_42
  <=> v2_tdlat_3(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_42])])).

fof(f265,plain,(
    v2_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f155])).

fof(f155,axiom,(
    ? [X0] :
      ( v2_tdlat_3(X0)
      & ~ v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',rc6_tex_1)).

fof(f519,plain,(
    ~ spl22_41 ),
    inference(avatar_split_clause,[],[f264,f517])).

fof(f264,plain,(
    ~ v1_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f155])).

fof(f512,plain,(
    spl22_38 ),
    inference(avatar_split_clause,[],[f263,f510])).

fof(f263,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f155])).

fof(f505,plain,(
    spl22_36 ),
    inference(avatar_split_clause,[],[f262,f503])).

fof(f262,plain,(
    v1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f155])).

fof(f498,plain,(
    ~ spl22_35 ),
    inference(avatar_split_clause,[],[f261,f496])).

fof(f261,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f155])).

fof(f491,plain,(
    spl22_32 ),
    inference(avatar_split_clause,[],[f260,f489])).

fof(f260,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f155])).

fof(f484,plain,(
    ~ spl22_31 ),
    inference(avatar_split_clause,[],[f259,f482])).

fof(f259,plain,(
    ~ v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f150])).

fof(f150,axiom,(
    ? [X0] :
      ( ~ v2_tdlat_3(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',rc5_tex_1)).

fof(f477,plain,(
    spl22_28 ),
    inference(avatar_split_clause,[],[f258,f475])).

fof(f475,plain,
    ( spl22_28
  <=> v1_tdlat_3(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_28])])).

fof(f258,plain,(
    v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f150])).

fof(f470,plain,(
    spl22_26 ),
    inference(avatar_split_clause,[],[f257,f468])).

fof(f257,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f150])).

fof(f463,plain,(
    spl22_24 ),
    inference(avatar_split_clause,[],[f256,f461])).

fof(f256,plain,(
    v1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f150])).

fof(f456,plain,(
    ~ spl22_23 ),
    inference(avatar_split_clause,[],[f255,f454])).

fof(f255,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f150])).

fof(f449,plain,(
    spl22_20 ),
    inference(avatar_split_clause,[],[f254,f447])).

fof(f254,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f150])).

fof(f442,plain,(
    spl22_18 ),
    inference(avatar_split_clause,[],[f253,f440])).

fof(f253,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f139])).

fof(f139,axiom,(
    ? [X0] :
      ( v2_tdlat_3(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t12_tex_2.p',rc3_tdlat_3)).

fof(f435,plain,(
    spl22_16 ),
    inference(avatar_split_clause,[],[f252,f433])).

fof(f252,plain,(
    v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f139])).

fof(f428,plain,(
    spl22_14 ),
    inference(avatar_split_clause,[],[f251,f426])).

fof(f251,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f139])).

fof(f421,plain,(
    spl22_12 ),
    inference(avatar_split_clause,[],[f250,f419])).

fof(f250,plain,(
    v1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f139])).

fof(f414,plain,(
    ~ spl22_11 ),
    inference(avatar_split_clause,[],[f249,f412])).

fof(f249,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f139])).

fof(f407,plain,(
    spl22_8 ),
    inference(avatar_split_clause,[],[f248,f405])).

fof(f248,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f139])).

fof(f400,plain,(
    spl22_6 ),
    inference(avatar_split_clause,[],[f247,f398])).

fof(f247,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f182])).

fof(f393,plain,(
    ~ spl22_5 ),
    inference(avatar_split_clause,[],[f246,f391])).

fof(f246,plain,(
    ~ v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f182])).

fof(f386,plain,(
    spl22_2 ),
    inference(avatar_split_clause,[],[f245,f384])).

fof(f245,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f182])).

fof(f379,plain,(
    spl22_0 ),
    inference(avatar_split_clause,[],[f243,f377])).

fof(f243,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f182])).
%------------------------------------------------------------------------------
