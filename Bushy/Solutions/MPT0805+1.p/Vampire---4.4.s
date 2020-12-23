%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t58_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:15 EDT 2019

% Result     : Theorem 5.47s
% Output     : Refutation 5.47s
% Verified   : 
% Statistics : Number of formulae       :  269 ( 555 expanded)
%              Number of leaves         :   74 ( 236 expanded)
%              Depth                    :   12
%              Number of atoms          : 1009 (2092 expanded)
%              Number of equality atoms :  104 ( 302 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2750,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f159,f163,f167,f171,f175,f179,f183,f803,f825,f835,f843,f907,f935,f958,f1097,f1136,f1139,f1146,f1175,f1187,f1202,f1213,f1230,f1247,f1303,f1311,f1355,f1450,f1454,f1621,f1626,f1712,f1816,f2158,f2529,f2536,f2561,f2578,f2666,f2726,f2748])).

fof(f2748,plain,
    ( ~ spl7_215
    | ~ spl7_301
    | ~ spl7_525
    | ~ spl7_1
    | ~ spl7_253
    | ~ spl7_10
    | ~ spl7_166 ),
    inference(avatar_split_clause,[],[f2587,f956,f177,f1413,f1089,f2521,f1407,f1095])).

fof(f1095,plain,
    ( spl7_215
  <=> ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_215])])).

fof(f1407,plain,
    ( spl7_301
  <=> ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_301])])).

fof(f2521,plain,
    ( spl7_525
  <=> ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_525])])).

fof(f1089,plain,
    ( spl7_1
  <=> ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1413,plain,
    ( spl7_253
  <=> ~ r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_253])])).

fof(f177,plain,
    ( spl7_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f956,plain,
    ( spl7_166
  <=> k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_166])])).

fof(f2587,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))))
    | ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ spl7_10
    | ~ spl7_166 ),
    inference(forward_demodulation,[],[f2508,f957])).

fof(f957,plain,
    ( k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1)
    | ~ spl7_166 ),
    inference(avatar_component_clause,[],[f956])).

fof(f2508,plain,
    ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))))
    | ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1),k1_wellord1(sK2,sK0))
    | ~ spl7_10
    | ~ spl7_166 ),
    inference(superposition,[],[f547,f957])).

fof(f547,plain,
    ( ! [X0,X1] :
        ( ~ r4_wellord1(k2_wellord1(sK2,X0),k2_wellord1(sK2,k1_wellord1(k2_wellord1(sK2,X0),X1)))
        | ~ r2_hidden(X1,k3_relat_1(k2_wellord1(sK2,X0)))
        | ~ v2_wellord1(k2_wellord1(sK2,X0))
        | ~ v1_relat_1(k2_wellord1(sK2,X0))
        | ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,X0),X1),X0) )
    | ~ spl7_10 ),
    inference(superposition,[],[f107,f480])).

fof(f480,plain,
    ( ! [X0,X1] :
        ( k2_wellord1(sK2,X0) = k2_wellord1(k2_wellord1(sK2,X1),X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl7_10 ),
    inference(resolution,[],[f148,f178])).

fof(f178,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f177])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',t29_wellord1)).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',t57_wellord1)).

fof(f2726,plain,
    ( spl7_316
    | ~ spl7_142
    | ~ spl7_540 ),
    inference(avatar_split_clause,[],[f2715,f2664,f905,f2724])).

fof(f2724,plain,
    ( spl7_316
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_316])])).

fof(f905,plain,
    ( spl7_142
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_142])])).

fof(f2664,plain,
    ( spl7_540
  <=> ! [X0] :
        ( r2_hidden(X0,k1_wellord1(sK2,sK1))
        | ~ r2_hidden(X0,k1_wellord1(sK2,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_540])])).

fof(f2715,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK1))
    | ~ spl7_142
    | ~ spl7_540 ),
    inference(resolution,[],[f2665,f906])).

fof(f906,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl7_142 ),
    inference(avatar_component_clause,[],[f905])).

fof(f2665,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,sK0))
        | r2_hidden(X0,k1_wellord1(sK2,sK1)) )
    | ~ spl7_540 ),
    inference(avatar_component_clause,[],[f2664])).

fof(f2666,plain,
    ( ~ spl7_251
    | spl7_264
    | spl7_540
    | spl7_253 ),
    inference(avatar_split_clause,[],[f2660,f1413,f2664,f1261,f1177])).

fof(f1177,plain,
    ( spl7_251
  <=> ~ r3_xboole_0(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_251])])).

fof(f1261,plain,
    ( spl7_264
  <=> v1_xboole_0(k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_264])])).

fof(f2660,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_wellord1(sK2,sK1))
        | ~ r2_hidden(X0,k1_wellord1(sK2,sK0))
        | v1_xboole_0(k1_wellord1(sK2,sK1))
        | ~ r3_xboole_0(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) )
    | ~ spl7_253 ),
    inference(resolution,[],[f1414,f341])).

fof(f341,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(X6,X8)
      | r2_hidden(X7,X6)
      | ~ r2_hidden(X7,X8)
      | v1_xboole_0(X6)
      | ~ r3_xboole_0(X6,X8) ) ),
    inference(resolution,[],[f333,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',d9_xboole_0)).

fof(f333,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,X4)
      | v1_xboole_0(X4)
      | r2_hidden(X2,X4)
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f311,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',t3_subset)).

fof(f311,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | ~ r2_hidden(X8,X6)
      | v1_xboole_0(X7)
      | r2_hidden(X8,X7) ) ),
    inference(resolution,[],[f150,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',t2_subset)).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',t4_subset)).

fof(f1414,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | ~ spl7_253 ),
    inference(avatar_component_clause,[],[f1413])).

fof(f2578,plain,
    ( ~ spl7_142
    | ~ spl7_530 ),
    inference(avatar_contradiction_clause,[],[f2573])).

fof(f2573,plain,
    ( $false
    | ~ spl7_142
    | ~ spl7_530 ),
    inference(subsumption_resolution,[],[f906,f2560])).

fof(f2560,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_wellord1(sK2,sK0))
    | ~ spl7_530 ),
    inference(avatar_component_clause,[],[f2559])).

fof(f2559,plain,
    ( spl7_530
  <=> ! [X0] : ~ r2_hidden(X0,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_530])])).

fof(f2561,plain,
    ( ~ spl7_477
    | spl7_530
    | ~ spl7_12
    | spl7_479 ),
    inference(avatar_split_clause,[],[f2554,f2527,f181,f2559,f2152])).

fof(f2152,plain,
    ( spl7_477
  <=> ~ r3_xboole_0(o_0_0_xboole_0,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_477])])).

fof(f181,plain,
    ( spl7_12
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f2527,plain,
    ( spl7_479
  <=> ~ r1_tarski(o_0_0_xboole_0,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_479])])).

fof(f2554,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,sK0))
        | ~ r3_xboole_0(o_0_0_xboole_0,k1_wellord1(sK2,sK0)) )
    | ~ spl7_12
    | ~ spl7_479 ),
    inference(resolution,[],[f2528,f303])).

fof(f303,plain,
    ( ! [X2,X1] :
        ( r1_tarski(o_0_0_xboole_0,X2)
        | ~ r2_hidden(X1,X2)
        | ~ r3_xboole_0(o_0_0_xboole_0,X2) )
    | ~ spl7_12 ),
    inference(resolution,[],[f260,f140])).

fof(f260,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X2,o_0_0_xboole_0)
        | ~ r2_hidden(X1,X2) )
    | ~ spl7_12 ),
    inference(resolution,[],[f258,f144])).

fof(f258,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl7_12 ),
    inference(resolution,[],[f151,f182])).

fof(f182,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f181])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',t5_subset)).

fof(f2528,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k1_wellord1(sK2,sK0))
    | ~ spl7_479 ),
    inference(avatar_component_clause,[],[f2527])).

fof(f2536,plain,
    ( ~ spl7_11
    | ~ spl7_9
    | ~ spl7_143
    | spl7_525 ),
    inference(avatar_split_clause,[],[f2535,f2521,f1410,f755,f743])).

fof(f743,plain,
    ( spl7_11
  <=> ~ v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f755,plain,
    ( spl7_9
  <=> ~ v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f1410,plain,
    ( spl7_143
  <=> ~ r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_143])])).

fof(f2535,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_525 ),
    inference(superposition,[],[f2522,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0)
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0)
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0)
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',t40_wellord1)).

fof(f2522,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))))
    | ~ spl7_525 ),
    inference(avatar_component_clause,[],[f2521])).

fof(f2529,plain,
    ( ~ spl7_215
    | ~ spl7_301
    | ~ spl7_525
    | ~ spl7_405
    | ~ spl7_479
    | ~ spl7_10
    | ~ spl7_166
    | ~ spl7_382 ),
    inference(avatar_split_clause,[],[f2519,f1709,f956,f177,f2527,f2524,f2521,f1407,f1095])).

fof(f2524,plain,
    ( spl7_405
  <=> ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_405])])).

fof(f1709,plain,
    ( spl7_382
  <=> k1_wellord1(sK2,sK1) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_382])])).

fof(f2519,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k1_wellord1(sK2,sK0))
    | ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,o_0_0_xboole_0))
    | ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))))
    | ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ spl7_10
    | ~ spl7_166
    | ~ spl7_382 ),
    inference(forward_demodulation,[],[f2518,f1710])).

fof(f1710,plain,
    ( k1_wellord1(sK2,sK1) = o_0_0_xboole_0
    | ~ spl7_382 ),
    inference(avatar_component_clause,[],[f1709])).

fof(f2518,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,o_0_0_xboole_0))
    | ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))))
    | ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ spl7_10
    | ~ spl7_166
    | ~ spl7_382 ),
    inference(forward_demodulation,[],[f2517,f957])).

fof(f2517,plain,
    ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,o_0_0_xboole_0))
    | ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))))
    | ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1),k1_wellord1(sK2,sK0))
    | ~ spl7_10
    | ~ spl7_166
    | ~ spl7_382 ),
    inference(forward_demodulation,[],[f2508,f1710])).

fof(f2158,plain,
    ( k1_wellord1(sK2,sK1) != o_0_0_xboole_0
    | r3_xboole_0(o_0_0_xboole_0,k1_wellord1(sK2,sK0))
    | ~ r3_xboole_0(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) ),
    introduced(theory_axiom,[])).

fof(f1816,plain,
    ( spl7_404
    | ~ spl7_0
    | ~ spl7_382 ),
    inference(avatar_split_clause,[],[f1786,f1709,f157,f1814])).

fof(f1814,plain,
    ( spl7_404
  <=> r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_404])])).

fof(f157,plain,
    ( spl7_0
  <=> r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f1786,plain,
    ( r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,o_0_0_xboole_0))
    | ~ spl7_0
    | ~ spl7_382 ),
    inference(superposition,[],[f158,f1710])).

fof(f158,plain,
    ( r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f157])).

fof(f1712,plain,
    ( spl7_382
    | ~ spl7_12
    | ~ spl7_264 ),
    inference(avatar_split_clause,[],[f1703,f1261,f181,f1709])).

fof(f1703,plain,
    ( k1_wellord1(sK2,sK1) = o_0_0_xboole_0
    | ~ spl7_12
    | ~ spl7_264 ),
    inference(resolution,[],[f1262,f244])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl7_12 ),
    inference(resolution,[],[f145,f182])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',t8_boole)).

fof(f1262,plain,
    ( v1_xboole_0(k1_wellord1(sK2,sK1))
    | ~ spl7_264 ),
    inference(avatar_component_clause,[],[f1261])).

fof(f1626,plain,
    ( ~ spl7_140
    | ~ spl7_352 ),
    inference(avatar_contradiction_clause,[],[f1623])).

fof(f1623,plain,
    ( $false
    | ~ spl7_140
    | ~ spl7_352 ),
    inference(subsumption_resolution,[],[f903,f1620])).

fof(f1620,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_wellord1(sK2,sK1))
    | ~ spl7_352 ),
    inference(avatar_component_clause,[],[f1619])).

fof(f1619,plain,
    ( spl7_352
  <=> ! [X0] : ~ r2_hidden(X0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_352])])).

fof(f903,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl7_140 ),
    inference(avatar_component_clause,[],[f902])).

fof(f902,plain,
    ( spl7_140
  <=> r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_140])])).

fof(f1621,plain,
    ( ~ spl7_279
    | spl7_352
    | ~ spl7_12
    | spl7_275 ),
    inference(avatar_split_clause,[],[f1611,f1301,f181,f1619,f1616])).

fof(f1616,plain,
    ( spl7_279
  <=> ~ r3_xboole_0(o_0_0_xboole_0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_279])])).

fof(f1301,plain,
    ( spl7_275
  <=> ~ r1_tarski(o_0_0_xboole_0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_275])])).

fof(f1611,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,sK1))
        | ~ r3_xboole_0(o_0_0_xboole_0,k1_wellord1(sK2,sK1)) )
    | ~ spl7_12
    | ~ spl7_275 ),
    inference(resolution,[],[f1302,f303])).

fof(f1302,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k1_wellord1(sK2,sK1))
    | ~ spl7_275 ),
    inference(avatar_component_clause,[],[f1301])).

fof(f1454,plain,
    ( ~ spl7_11
    | ~ spl7_9
    | spl7_301 ),
    inference(avatar_split_clause,[],[f1452,f1407,f755,f743])).

fof(f1452,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_301 ),
    inference(resolution,[],[f1408,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',t32_wellord1)).

fof(f1408,plain,
    ( ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ spl7_301 ),
    inference(avatar_component_clause,[],[f1407])).

fof(f1450,plain,
    ( ~ spl7_215
    | ~ spl7_317
    | ~ spl7_166 ),
    inference(avatar_split_clause,[],[f1403,f956,f1448,f1095])).

fof(f1448,plain,
    ( spl7_317
  <=> ~ r2_hidden(sK1,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_317])])).

fof(f1403,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK1))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ spl7_166 ),
    inference(superposition,[],[f155,f957])).

fof(f155,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f154])).

fof(f154,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
                | sK5(X0,X1,X2) = X1
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
                  & sK5(X0,X1,X2) != X1 )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f89,f90])).

fof(f90,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
          | sK5(X0,X1,X2) = X1
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
            & sK5(X0,X1,X2) != X1 )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',d1_wellord1)).

fof(f1355,plain,
    ( ~ spl7_11
    | spl7_215 ),
    inference(avatar_split_clause,[],[f1354,f1095,f743])).

fof(f1354,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl7_215 ),
    inference(resolution,[],[f1096,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',dt_k2_wellord1)).

fof(f1096,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ spl7_215 ),
    inference(avatar_component_clause,[],[f1095])).

fof(f1311,plain,
    ( spl7_278
    | ~ spl7_244
    | ~ spl7_254 ),
    inference(avatar_split_clause,[],[f1279,f1198,f1219,f1309])).

fof(f1309,plain,
    ( spl7_278
  <=> r3_xboole_0(o_0_0_xboole_0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_278])])).

fof(f1219,plain,
    ( spl7_244
  <=> r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_244])])).

fof(f1198,plain,
    ( spl7_254
  <=> k1_wellord1(sK2,sK0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_254])])).

fof(f1279,plain,
    ( r3_xboole_0(o_0_0_xboole_0,k1_wellord1(sK2,sK1))
    | ~ spl7_244
    | ~ spl7_254 ),
    inference(superposition,[],[f1220,f1199])).

fof(f1199,plain,
    ( k1_wellord1(sK2,sK0) = o_0_0_xboole_0
    | ~ spl7_254 ),
    inference(avatar_component_clause,[],[f1198])).

fof(f1220,plain,
    ( r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl7_244 ),
    inference(avatar_component_clause,[],[f1219])).

fof(f1303,plain,
    ( ~ spl7_275
    | spl7_213
    | ~ spl7_254 ),
    inference(avatar_split_clause,[],[f1276,f1198,f1092,f1301])).

fof(f1092,plain,
    ( spl7_213
  <=> ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_213])])).

fof(f1276,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k1_wellord1(sK2,sK1))
    | ~ spl7_213
    | ~ spl7_254 ),
    inference(superposition,[],[f1093,f1199])).

fof(f1093,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl7_213 ),
    inference(avatar_component_clause,[],[f1092])).

fof(f1247,plain,
    ( spl7_232
    | ~ spl7_140
    | ~ spl7_248 ),
    inference(avatar_split_clause,[],[f1238,f1173,f902,f1245])).

fof(f1245,plain,
    ( spl7_232
  <=> r2_hidden(sK0,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_232])])).

fof(f1173,plain,
    ( spl7_248
  <=> ! [X0] :
        ( r2_hidden(X0,k1_wellord1(sK2,sK0))
        | ~ r2_hidden(X0,k1_wellord1(sK2,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_248])])).

fof(f1238,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK0))
    | ~ spl7_140
    | ~ spl7_248 ),
    inference(resolution,[],[f1174,f903])).

fof(f1174,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,sK1))
        | r2_hidden(X0,k1_wellord1(sK2,sK0)) )
    | ~ spl7_248 ),
    inference(avatar_component_clause,[],[f1173])).

fof(f1230,plain,
    ( ~ spl7_11
    | ~ spl7_9
    | ~ spl7_141
    | spl7_207 ),
    inference(avatar_split_clause,[],[f1226,f1080,f1228,f755,f743])).

fof(f1228,plain,
    ( spl7_141
  <=> ~ r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_141])])).

fof(f1080,plain,
    ( spl7_207
  <=> ~ r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_207])])).

fof(f1226,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_207 ),
    inference(superposition,[],[f1081,f135])).

fof(f1081,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))))
    | ~ spl7_207 ),
    inference(avatar_component_clause,[],[f1080])).

fof(f1213,plain,
    ( ~ spl7_11
    | ~ spl7_9
    | spl7_251 ),
    inference(avatar_split_clause,[],[f1209,f1177,f755,f743])).

fof(f1209,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_251 ),
    inference(resolution,[],[f1178,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',t33_wellord1)).

fof(f1178,plain,
    ( ~ r3_xboole_0(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | ~ spl7_251 ),
    inference(avatar_component_clause,[],[f1177])).

fof(f1202,plain,
    ( spl7_254
    | ~ spl7_12
    | ~ spl7_246 ),
    inference(avatar_split_clause,[],[f1192,f1170,f181,f1198])).

fof(f1170,plain,
    ( spl7_246
  <=> v1_xboole_0(k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_246])])).

fof(f1192,plain,
    ( k1_wellord1(sK2,sK0) = o_0_0_xboole_0
    | ~ spl7_12
    | ~ spl7_246 ),
    inference(resolution,[],[f1171,f244])).

fof(f1171,plain,
    ( v1_xboole_0(k1_wellord1(sK2,sK0))
    | ~ spl7_246 ),
    inference(avatar_component_clause,[],[f1170])).

fof(f1187,plain,
    ( ~ spl7_11
    | ~ spl7_9
    | spl7_245 ),
    inference(avatar_split_clause,[],[f1183,f1167,f755,f743])).

fof(f1167,plain,
    ( spl7_245
  <=> ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_245])])).

fof(f1183,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_245 ),
    inference(resolution,[],[f1168,f147])).

fof(f1168,plain,
    ( ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl7_245 ),
    inference(avatar_component_clause,[],[f1167])).

fof(f1175,plain,
    ( ~ spl7_245
    | spl7_246
    | spl7_248
    | spl7_213 ),
    inference(avatar_split_clause,[],[f1163,f1092,f1173,f1170,f1167])).

fof(f1163,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_wellord1(sK2,sK0))
        | ~ r2_hidden(X0,k1_wellord1(sK2,sK1))
        | v1_xboole_0(k1_wellord1(sK2,sK0))
        | ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) )
    | ~ spl7_213 ),
    inference(resolution,[],[f1093,f341])).

fof(f1146,plain,
    ( ~ spl7_11
    | ~ spl7_9
    | spl7_211 ),
    inference(avatar_split_clause,[],[f1144,f1086,f755,f743])).

fof(f1086,plain,
    ( spl7_211
  <=> ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_211])])).

fof(f1144,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_211 ),
    inference(resolution,[],[f1087,f134])).

fof(f1087,plain,
    ( ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ spl7_211 ),
    inference(avatar_component_clause,[],[f1086])).

fof(f1139,plain,
    ( ~ spl7_11
    | spl7_209 ),
    inference(avatar_split_clause,[],[f1138,f1083,f743])).

fof(f1083,plain,
    ( spl7_209
  <=> ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_209])])).

fof(f1138,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl7_209 ),
    inference(resolution,[],[f1084,f133])).

fof(f1084,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ spl7_209 ),
    inference(avatar_component_clause,[],[f1083])).

fof(f1136,plain,
    ( ~ spl7_209
    | ~ spl7_233
    | ~ spl7_156 ),
    inference(avatar_split_clause,[],[f1076,f933,f1134,f1083])).

fof(f1134,plain,
    ( spl7_233
  <=> ~ r2_hidden(sK0,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_233])])).

fof(f933,plain,
    ( spl7_156
  <=> k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_156])])).

fof(f1076,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK0))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ spl7_156 ),
    inference(superposition,[],[f155,f934])).

fof(f934,plain,
    ( k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0)
    | ~ spl7_156 ),
    inference(avatar_component_clause,[],[f933])).

fof(f1097,plain,
    ( ~ spl7_207
    | ~ spl7_209
    | ~ spl7_211
    | ~ spl7_1
    | ~ spl7_213
    | ~ spl7_215
    | ~ spl7_10
    | ~ spl7_156 ),
    inference(avatar_split_clause,[],[f1078,f933,f177,f1095,f1092,f1089,f1086,f1083,f1080])).

fof(f1078,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))))
    | ~ spl7_10
    | ~ spl7_156 ),
    inference(forward_demodulation,[],[f1077,f934])).

fof(f1077,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0)))
    | ~ spl7_10
    | ~ spl7_156 ),
    inference(forward_demodulation,[],[f1067,f934])).

fof(f1067,plain,
    ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0),k1_wellord1(sK2,sK1))
    | ~ r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0)))
    | ~ spl7_10
    | ~ spl7_156 ),
    inference(superposition,[],[f556,f934])).

fof(f556,plain,
    ( ! [X0,X1] :
        ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(k2_wellord1(sK2,X1),X0)),k2_wellord1(sK2,X1))
        | ~ v2_wellord1(k2_wellord1(sK2,X1))
        | ~ v1_relat_1(k2_wellord1(sK2,X1))
        | ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,X1),X0),X1)
        | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(sK2,X1)))
        | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(k2_wellord1(sK2,X1),X0))) )
    | ~ spl7_10 ),
    inference(duplicate_literal_removal,[],[f555])).

fof(f555,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(sK2,X1)))
        | ~ v2_wellord1(k2_wellord1(sK2,X1))
        | ~ v1_relat_1(k2_wellord1(sK2,X1))
        | ~ r1_tarski(k1_wellord1(k2_wellord1(sK2,X1),X0),X1)
        | ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(k2_wellord1(sK2,X1),X0)),k2_wellord1(sK2,X1))
        | ~ v1_relat_1(k2_wellord1(sK2,X1))
        | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(k2_wellord1(sK2,X1),X0))) )
    | ~ spl7_10 ),
    inference(resolution,[],[f547,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',t50_wellord1)).

fof(f958,plain,
    ( ~ spl7_11
    | ~ spl7_9
    | spl7_166
    | ~ spl7_142 ),
    inference(avatar_split_clause,[],[f951,f905,f956,f755,f743])).

fof(f951,plain,
    ( k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1)
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_142 ),
    inference(resolution,[],[f906,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0)
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X0,k1_wellord1(X2,X1))
          & v2_wellord1(X2) )
       => k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',t35_wellord1)).

fof(f935,plain,
    ( ~ spl7_11
    | ~ spl7_9
    | spl7_156
    | ~ spl7_140 ),
    inference(avatar_split_clause,[],[f928,f902,f933,f755,f743])).

fof(f928,plain,
    ( k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0)
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_140 ),
    inference(resolution,[],[f903,f149])).

fof(f907,plain,
    ( spl7_2
    | spl7_140
    | spl7_142
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_132 ),
    inference(avatar_split_clause,[],[f894,f841,f169,f165,f905,f902,f899])).

fof(f899,plain,
    ( spl7_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f165,plain,
    ( spl7_4
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f169,plain,
    ( spl7_6
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f841,plain,
    ( spl7_132
  <=> ! [X1,X0] :
        ( r2_hidden(X0,k1_wellord1(sK2,X1))
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).

fof(f894,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | sK0 = sK1
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_132 ),
    inference(resolution,[],[f844,f170])).

fof(f170,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f169])).

fof(f844,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(sK1,k1_wellord1(sK2,X0))
        | r2_hidden(X0,k1_wellord1(sK2,sK1))
        | sK1 = X0 )
    | ~ spl7_4
    | ~ spl7_132 ),
    inference(resolution,[],[f842,f166])).

fof(f166,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f165])).

fof(f842,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | r2_hidden(X0,k1_wellord1(sK2,X1))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 )
    | ~ spl7_132 ),
    inference(avatar_component_clause,[],[f841])).

fof(f843,plain,
    ( ~ spl7_11
    | spl7_132
    | ~ spl7_130 ),
    inference(avatar_split_clause,[],[f839,f833,f841,f743])).

fof(f833,plain,
    ( spl7_130
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | X0 = X1
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f839,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_wellord1(sK2,X1))
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | ~ v1_relat_1(sK2) )
    | ~ spl7_130 ),
    inference(duplicate_literal_removal,[],[f836])).

fof(f836,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_wellord1(sK2,X1))
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | X0 = X1
        | ~ v1_relat_1(sK2) )
    | ~ spl7_130 ),
    inference(resolution,[],[f834,f152])).

fof(f152,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X1),X0)
      | r2_hidden(X4,k1_wellord1(X0,X1))
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f834,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | X0 = X1
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2)) )
    | ~ spl7_130 ),
    inference(avatar_component_clause,[],[f833])).

fof(f835,plain,
    ( ~ spl7_11
    | spl7_130
    | ~ spl7_120 ),
    inference(avatar_split_clause,[],[f831,f801,f833,f743])).

fof(f801,plain,
    ( spl7_120
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f831,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | X0 = X1
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | ~ v1_relat_1(sK2) )
    | ~ spl7_120 ),
    inference(duplicate_literal_removal,[],[f826])).

fof(f826,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | X0 = X1
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | X0 = X1
        | ~ v1_relat_1(sK2) )
    | ~ spl7_120 ),
    inference(resolution,[],[f802,f152])).

fof(f802,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 )
    | ~ spl7_120 ),
    inference(avatar_component_clause,[],[f801])).

fof(f825,plain,
    ( ~ spl7_11
    | ~ spl7_9
    | spl7_119 ),
    inference(avatar_split_clause,[],[f808,f798,f755,f743])).

fof(f798,plain,
    ( spl7_119
  <=> ~ v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).

fof(f808,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_119 ),
    inference(resolution,[],[f799,f117])).

fof(f117,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',d4_wellord1)).

fof(f799,plain,
    ( ~ v6_relat_2(sK2)
    | ~ spl7_119 ),
    inference(avatar_component_clause,[],[f798])).

fof(f803,plain,
    ( ~ spl7_119
    | spl7_120
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f794,f177,f801,f798])).

fof(f794,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ v6_relat_2(sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2) )
    | ~ spl7_10 ),
    inference(resolution,[],[f108,f178])).

fof(f108,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X3),X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
            & sK3(X0) != sK4(X0)
            & r2_hidden(sK4(X0),k3_relat_1(X0))
            & r2_hidden(sK3(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f82,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
        & sK3(X0) != sK4(X0)
        & r2_hidden(sK4(X0),k3_relat_1(X0))
        & r2_hidden(sK3(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',l4_wellord1)).

fof(f183,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f103,f181])).

fof(f103,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',dt_o_0_0_xboole_0)).

fof(f179,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f97,f177])).

fof(f97,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,
    ( r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    & sK0 != sK1
    & r2_hidden(sK1,k3_relat_1(sK2))
    & r2_hidden(sK0,k3_relat_1(sK2))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f79])).

fof(f79,plain,
    ( ? [X0,X1,X2] :
        ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
        & X0 != X1
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
      & sK0 != sK1
      & r2_hidden(sK1,k3_relat_1(sK2))
      & r2_hidden(sK0,k3_relat_1(sK2))
      & v2_wellord1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0,X1,X2] :
      ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
      & X0 != X1
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
      & X0 != X1
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ~ ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
            & X0 != X1
            & r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
          & X0 != X1
          & r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t58_wellord1.p',t58_wellord1)).

fof(f175,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f98,f173])).

fof(f173,plain,
    ( spl7_8
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f98,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f80])).

fof(f171,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f99,f169])).

fof(f99,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f80])).

fof(f167,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f100,f165])).

fof(f100,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f80])).

fof(f163,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f101,f161])).

fof(f161,plain,
    ( spl7_3
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f101,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f80])).

fof(f159,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f102,f157])).

fof(f102,plain,(
    r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f80])).
%------------------------------------------------------------------------------
