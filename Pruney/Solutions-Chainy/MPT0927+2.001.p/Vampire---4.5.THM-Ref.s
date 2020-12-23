%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 463 expanded)
%              Number of leaves         :   55 ( 222 expanded)
%              Depth                    :   10
%              Number of atoms          :  815 (2043 expanded)
%              Number of equality atoms :  169 ( 316 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f759,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f75,f79,f89,f94,f104,f109,f113,f117,f124,f136,f148,f154,f163,f169,f186,f191,f197,f202,f208,f244,f366,f484,f539,f547,f555,f564,f573,f576,f585,f595,f604,f612,f636,f696,f746,f749,f753,f757])).

fof(f757,plain,
    ( ~ spl10_21
    | spl10_26
    | ~ spl10_91 ),
    inference(avatar_contradiction_clause,[],[f756])).

fof(f756,plain,
    ( $false
    | ~ spl10_21
    | spl10_26
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f755,f162])).

fof(f162,plain,
    ( r2_hidden(k2_mcart_1(sK8),sK7)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl10_21
  <=> r2_hidden(k2_mcart_1(sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f755,plain,
    ( ~ r2_hidden(k2_mcart_1(sK8),sK7)
    | spl10_26
    | ~ spl10_91 ),
    inference(forward_demodulation,[],[f185,f538])).

fof(f538,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | ~ spl10_91 ),
    inference(avatar_component_clause,[],[f536])).

fof(f536,plain,
    ( spl10_91
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_91])])).

fof(f185,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | spl10_26 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl10_26
  <=> r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f753,plain,
    ( spl10_25
    | ~ spl10_27
    | ~ spl10_96 ),
    inference(avatar_contradiction_clause,[],[f752])).

fof(f752,plain,
    ( $false
    | spl10_25
    | ~ spl10_27
    | ~ spl10_96 ),
    inference(subsumption_resolution,[],[f751,f190])).

fof(f190,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl10_27
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f751,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)
    | spl10_25
    | ~ spl10_96 ),
    inference(forward_demodulation,[],[f181,f584])).

fof(f584,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl10_96 ),
    inference(avatar_component_clause,[],[f582])).

fof(f582,plain,
    ( spl10_96
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).

fof(f181,plain,
    ( ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | spl10_25 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl10_25
  <=> r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f749,plain,
    ( spl10_24
    | ~ spl10_29
    | ~ spl10_112 ),
    inference(avatar_contradiction_clause,[],[f748])).

fof(f748,plain,
    ( $false
    | spl10_24
    | ~ spl10_29
    | ~ spl10_112 ),
    inference(subsumption_resolution,[],[f747,f201])).

fof(f201,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl10_29
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f747,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | spl10_24
    | ~ spl10_112 ),
    inference(forward_demodulation,[],[f177,f695])).

fof(f695,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl10_112 ),
    inference(avatar_component_clause,[],[f693])).

fof(f693,plain,
    ( spl10_112
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_112])])).

fof(f177,plain,
    ( ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | spl10_24 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl10_24
  <=> r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f746,plain,
    ( ~ spl10_9
    | ~ spl10_19
    | spl10_23
    | spl10_87
    | spl10_88
    | spl10_89
    | spl10_90
    | ~ spl10_101 ),
    inference(avatar_contradiction_clause,[],[f745])).

fof(f745,plain,
    ( $false
    | ~ spl10_9
    | ~ spl10_19
    | spl10_23
    | spl10_87
    | spl10_88
    | spl10_89
    | spl10_90
    | ~ spl10_101 ),
    inference(subsumption_resolution,[],[f744,f147])).

fof(f147,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl10_19
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f744,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | ~ spl10_9
    | spl10_23
    | spl10_87
    | spl10_88
    | spl10_89
    | spl10_90
    | ~ spl10_101 ),
    inference(backward_demodulation,[],[f173,f743])).

fof(f743,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl10_9
    | spl10_87
    | spl10_88
    | spl10_89
    | spl10_90
    | ~ spl10_101 ),
    inference(subsumption_resolution,[],[f742,f521])).

fof(f521,plain,
    ( k1_xboole_0 != sK0
    | spl10_87 ),
    inference(avatar_component_clause,[],[f520])).

fof(f520,plain,
    ( spl10_87
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_87])])).

fof(f742,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK0
    | ~ spl10_9
    | spl10_88
    | spl10_89
    | spl10_90
    | ~ spl10_101 ),
    inference(subsumption_resolution,[],[f741,f525])).

fof(f525,plain,
    ( k1_xboole_0 != sK1
    | spl10_88 ),
    inference(avatar_component_clause,[],[f524])).

fof(f524,plain,
    ( spl10_88
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f741,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl10_9
    | spl10_89
    | spl10_90
    | ~ spl10_101 ),
    inference(subsumption_resolution,[],[f740,f529])).

fof(f529,plain,
    ( k1_xboole_0 != sK2
    | spl10_89 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl10_89
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_89])])).

fof(f740,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl10_9
    | spl10_90
    | ~ spl10_101 ),
    inference(subsumption_resolution,[],[f739,f533])).

fof(f533,plain,
    ( k1_xboole_0 != sK3
    | spl10_90 ),
    inference(avatar_component_clause,[],[f532])).

fof(f532,plain,
    ( spl10_90
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).

fof(f739,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl10_9
    | ~ spl10_101 ),
    inference(resolution,[],[f635,f93])).

fof(f93,plain,
    ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl10_9
  <=> m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f635,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
        | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl10_101 ),
    inference(avatar_component_clause,[],[f634])).

fof(f634,plain,
    ( spl10_101
  <=> ! [X1,X3,X0,X2,X4] :
        ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
        | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_101])])).

fof(f173,plain,
    ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | spl10_23 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl10_23
  <=> r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f696,plain,
    ( spl10_112
    | ~ spl10_9
    | ~ spl10_80
    | spl10_87
    | spl10_88
    | spl10_89
    | spl10_90 ),
    inference(avatar_split_clause,[],[f691,f532,f528,f524,f520,f482,f91,f693])).

fof(f482,plain,
    ( spl10_80
  <=> ! [X1,X3,X0,X2,X4] :
        ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
        | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f691,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl10_9
    | ~ spl10_80
    | spl10_87
    | spl10_88
    | spl10_89
    | spl10_90 ),
    inference(subsumption_resolution,[],[f690,f521])).

fof(f690,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK0
    | ~ spl10_9
    | ~ spl10_80
    | spl10_88
    | spl10_89
    | spl10_90 ),
    inference(subsumption_resolution,[],[f689,f525])).

fof(f689,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl10_9
    | ~ spl10_80
    | spl10_89
    | spl10_90 ),
    inference(subsumption_resolution,[],[f688,f529])).

fof(f688,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl10_9
    | ~ spl10_80
    | spl10_90 ),
    inference(subsumption_resolution,[],[f687,f533])).

fof(f687,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl10_9
    | ~ spl10_80 ),
    inference(resolution,[],[f483,f93])).

fof(f483,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
        | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl10_80 ),
    inference(avatar_component_clause,[],[f482])).

fof(f636,plain,(
    spl10_101 ),
    inference(avatar_split_clause,[],[f50,f634])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
            & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f612,plain,
    ( ~ spl10_13
    | spl10_28
    | ~ spl10_94 ),
    inference(avatar_contradiction_clause,[],[f611])).

fof(f611,plain,
    ( $false
    | ~ spl10_13
    | spl10_28
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f610,f196])).

fof(f196,plain,
    ( ~ v1_xboole_0(sK6)
    | spl10_28 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl10_28
  <=> v1_xboole_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f610,plain,
    ( v1_xboole_0(sK6)
    | ~ spl10_13
    | ~ spl10_94 ),
    inference(resolution,[],[f563,f112])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl10_13
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f563,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_94 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl10_94
  <=> m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f604,plain,
    ( ~ spl10_13
    | spl10_30
    | ~ spl10_93 ),
    inference(avatar_contradiction_clause,[],[f603])).

fof(f603,plain,
    ( $false
    | ~ spl10_13
    | spl10_30
    | ~ spl10_93 ),
    inference(subsumption_resolution,[],[f602,f207])).

fof(f207,plain,
    ( ~ v1_xboole_0(sK5)
    | spl10_30 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl10_30
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f602,plain,
    ( v1_xboole_0(sK5)
    | ~ spl10_13
    | ~ spl10_93 ),
    inference(resolution,[],[f554,f112])).

fof(f554,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_93 ),
    inference(avatar_component_clause,[],[f552])).

fof(f552,plain,
    ( spl10_93
  <=> m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_93])])).

fof(f595,plain,
    ( ~ spl10_13
    | spl10_20
    | ~ spl10_92 ),
    inference(avatar_contradiction_clause,[],[f594])).

fof(f594,plain,
    ( $false
    | ~ spl10_13
    | spl10_20
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f593,f153])).

fof(f153,plain,
    ( ~ v1_xboole_0(sK4)
    | spl10_20 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl10_20
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f593,plain,
    ( v1_xboole_0(sK4)
    | ~ spl10_13
    | ~ spl10_92 ),
    inference(resolution,[],[f546,f112])).

fof(f546,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_92 ),
    inference(avatar_component_clause,[],[f544])).

fof(f544,plain,
    ( spl10_92
  <=> m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).

fof(f585,plain,
    ( spl10_96
    | ~ spl10_9
    | ~ spl10_58
    | spl10_87
    | spl10_88
    | spl10_89
    | spl10_90 ),
    inference(avatar_split_clause,[],[f578,f532,f528,f524,f520,f364,f91,f582])).

fof(f364,plain,
    ( spl10_58
  <=> ! [X1,X3,X0,X2,X4] :
        ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
        | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f578,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl10_9
    | ~ spl10_58
    | spl10_87
    | spl10_88
    | spl10_89
    | spl10_90 ),
    inference(subsumption_resolution,[],[f577,f533])).

fof(f577,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = sK3
    | ~ spl10_9
    | ~ spl10_58
    | spl10_87
    | spl10_88
    | spl10_89 ),
    inference(subsumption_resolution,[],[f565,f529])).

fof(f565,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | ~ spl10_9
    | ~ spl10_58
    | spl10_87
    | spl10_88 ),
    inference(subsumption_resolution,[],[f556,f525])).

fof(f556,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ spl10_9
    | ~ spl10_58
    | spl10_87 ),
    inference(subsumption_resolution,[],[f423,f521])).

fof(f423,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl10_9
    | ~ spl10_58 ),
    inference(resolution,[],[f365,f93])).

fof(f365,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
        | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f364])).

fof(f576,plain,
    ( ~ spl10_13
    | spl10_22
    | ~ spl10_95 ),
    inference(avatar_contradiction_clause,[],[f575])).

fof(f575,plain,
    ( $false
    | ~ spl10_13
    | spl10_22
    | ~ spl10_95 ),
    inference(subsumption_resolution,[],[f574,f168])).

fof(f168,plain,
    ( ~ v1_xboole_0(sK7)
    | spl10_22 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl10_22
  <=> v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f574,plain,
    ( v1_xboole_0(sK7)
    | ~ spl10_13
    | ~ spl10_95 ),
    inference(resolution,[],[f572,f112])).

fof(f572,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_95 ),
    inference(avatar_component_clause,[],[f570])).

fof(f570,plain,
    ( spl10_95
  <=> m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_95])])).

fof(f573,plain,
    ( spl10_95
    | ~ spl10_5
    | ~ spl10_90 ),
    inference(avatar_split_clause,[],[f566,f532,f72,f570])).

fof(f72,plain,
    ( spl10_5
  <=> m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f566,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_5
    | ~ spl10_90 ),
    inference(backward_demodulation,[],[f74,f534])).

fof(f534,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_90 ),
    inference(avatar_component_clause,[],[f532])).

fof(f74,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK3))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f564,plain,
    ( spl10_94
    | ~ spl10_4
    | ~ spl10_89 ),
    inference(avatar_split_clause,[],[f557,f528,f67,f561])).

fof(f67,plain,
    ( spl10_4
  <=> m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f557,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_4
    | ~ spl10_89 ),
    inference(backward_demodulation,[],[f69,f530])).

fof(f530,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_89 ),
    inference(avatar_component_clause,[],[f528])).

fof(f69,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK2))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f555,plain,
    ( spl10_93
    | ~ spl10_3
    | ~ spl10_88 ),
    inference(avatar_split_clause,[],[f548,f524,f62,f552])).

fof(f62,plain,
    ( spl10_3
  <=> m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f548,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_3
    | ~ spl10_88 ),
    inference(backward_demodulation,[],[f64,f526])).

fof(f526,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_88 ),
    inference(avatar_component_clause,[],[f524])).

fof(f64,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK1))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f547,plain,
    ( spl10_92
    | ~ spl10_2
    | ~ spl10_87 ),
    inference(avatar_split_clause,[],[f540,f520,f57,f544])).

fof(f57,plain,
    ( spl10_2
  <=> m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f540,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_2
    | ~ spl10_87 ),
    inference(backward_demodulation,[],[f59,f522])).

fof(f522,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_87 ),
    inference(avatar_component_clause,[],[f520])).

fof(f59,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK0))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f539,plain,
    ( spl10_87
    | spl10_88
    | spl10_89
    | spl10_90
    | spl10_91
    | ~ spl10_9
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f302,f242,f91,f536,f532,f528,f524,f520])).

fof(f242,plain,
    ( spl10_37
  <=> ! [X1,X3,X0,X2,X4] :
        ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
        | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f302,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl10_9
    | ~ spl10_37 ),
    inference(resolution,[],[f243,f93])).

fof(f243,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
        | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f242])).

fof(f484,plain,(
    spl10_80 ),
    inference(avatar_split_clause,[],[f49,f482])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f366,plain,(
    spl10_58 ),
    inference(avatar_split_clause,[],[f48,f364])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f244,plain,(
    spl10_37 ),
    inference(avatar_split_clause,[],[f47,f242])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f208,plain,
    ( ~ spl10_30
    | ~ spl10_6
    | ~ spl10_29 ),
    inference(avatar_split_clause,[],[f203,f199,f77,f205])).

fof(f77,plain,
    ( spl10_6
  <=> ! [X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f203,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl10_6
    | ~ spl10_29 ),
    inference(resolution,[],[f201,f78])).

fof(f78,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f202,plain,
    ( spl10_29
    | ~ spl10_14
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f158,f133,f115,f199])).

fof(f115,plain,
    ( spl10_14
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k2_mcart_1(X0),X2)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f133,plain,
    ( spl10_17
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f158,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | ~ spl10_14
    | ~ spl10_17 ),
    inference(resolution,[],[f116,f135])).

fof(f135,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f133])).

fof(f116,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | r2_hidden(k2_mcart_1(X0),X2) )
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f115])).

fof(f197,plain,
    ( ~ spl10_28
    | ~ spl10_6
    | ~ spl10_27 ),
    inference(avatar_split_clause,[],[f192,f188,f77,f194])).

fof(f192,plain,
    ( ~ v1_xboole_0(sK6)
    | ~ spl10_6
    | ~ spl10_27 ),
    inference(resolution,[],[f190,f78])).

fof(f191,plain,
    ( spl10_27
    | ~ spl10_14
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f157,f121,f115,f188])).

fof(f121,plain,
    ( spl10_15
  <=> r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f157,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)
    | ~ spl10_14
    | ~ spl10_15 ),
    inference(resolution,[],[f116,f123])).

fof(f123,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f121])).

fof(f186,plain,
    ( ~ spl10_23
    | ~ spl10_24
    | ~ spl10_25
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f31,f183,f179,f175,f171])).

fof(f31,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
      | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
      | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
      | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) )
    & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    & m1_subset_1(sK7,k1_zfmisc_1(sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f11,f19,f18,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ? [X8] :
                        ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                          | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                          | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                          | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                        & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                        & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                    & m1_subset_1(X7,k1_zfmisc_1(X3)) )
                & m1_subset_1(X6,k1_zfmisc_1(X2)) )
            & m1_subset_1(X5,k1_zfmisc_1(X1)) )
        & m1_subset_1(X4,k1_zfmisc_1(X0)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                      & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
              & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                      | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                      | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5)
                      | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                    & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7))
                    & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
                & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
            & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
        & m1_subset_1(X5,k1_zfmisc_1(sK1)) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                  & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7))
                  & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
              & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
          & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ? [X8] :
                ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                  | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                  | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                  | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7))
                & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
            & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
        & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
   => ( ? [X7] :
          ( ? [X8] :
              ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
                | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
              & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7))
              & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
          & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
      & m1_subset_1(sK6,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X7] :
        ( ? [X8] :
            ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
              | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
              | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
              | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
            & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7))
            & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
        & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
   => ( ? [X8] :
          ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7)
            | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
            | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
            | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
          & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
          & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
      & m1_subset_1(sK7,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X8] :
        ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7)
          | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
          | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
          | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
        & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
        & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
   => ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
        | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
        | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
        | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) )
      & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
      & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
      & m1_subset_1(X4,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
      & m1_subset_1(X4,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(X0))
       => ! [X5] :
            ( m1_subset_1(X5,k1_zfmisc_1(X1))
           => ! [X6] :
                ( m1_subset_1(X6,k1_zfmisc_1(X2))
               => ! [X7] :
                    ( m1_subset_1(X7,k1_zfmisc_1(X3))
                   => ! [X8] :
                        ( m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
                       => ( r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                         => ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                            & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                            & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                            & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(X0))
     => ! [X5] :
          ( m1_subset_1(X5,k1_zfmisc_1(X1))
         => ! [X6] :
              ( m1_subset_1(X6,k1_zfmisc_1(X2))
             => ! [X7] :
                  ( m1_subset_1(X7,k1_zfmisc_1(X3))
                 => ! [X8] :
                      ( m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
                     => ( r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                       => ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                          & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                          & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                          & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_mcart_1)).

fof(f169,plain,
    ( ~ spl10_22
    | ~ spl10_6
    | ~ spl10_21 ),
    inference(avatar_split_clause,[],[f164,f160,f77,f166])).

fof(f164,plain,
    ( ~ v1_xboole_0(sK7)
    | ~ spl10_6
    | ~ spl10_21 ),
    inference(resolution,[],[f162,f78])).

fof(f163,plain,
    ( spl10_21
    | ~ spl10_8
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f156,f115,f86,f160])).

fof(f86,plain,
    ( spl10_8
  <=> r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f156,plain,
    ( r2_hidden(k2_mcart_1(sK8),sK7)
    | ~ spl10_8
    | ~ spl10_14 ),
    inference(resolution,[],[f116,f88])).

fof(f88,plain,
    ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f154,plain,
    ( ~ spl10_20
    | ~ spl10_6
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f149,f145,f77,f151])).

fof(f149,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl10_6
    | ~ spl10_19 ),
    inference(resolution,[],[f147,f78])).

fof(f148,plain,
    ( spl10_19
    | ~ spl10_12
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f137,f133,f107,f145])).

fof(f107,plain,
    ( spl10_12
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k1_mcart_1(X0),X1)
        | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f137,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | ~ spl10_12
    | ~ spl10_17 ),
    inference(resolution,[],[f135,f108])).

fof(f108,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | r2_hidden(k1_mcart_1(X0),X1) )
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f136,plain,
    ( spl10_17
    | ~ spl10_12
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f125,f121,f107,f133])).

fof(f125,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))
    | ~ spl10_12
    | ~ spl10_15 ),
    inference(resolution,[],[f123,f108])).

fof(f124,plain,
    ( spl10_15
    | ~ spl10_8
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f119,f107,f86,f121])).

fof(f119,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ spl10_8
    | ~ spl10_12 ),
    inference(resolution,[],[f108,f88])).

fof(f117,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f38,f115])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f113,plain,
    ( spl10_13
    | ~ spl10_1
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f105,f102,f52,f111])).

fof(f52,plain,
    ( spl10_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f102,plain,
    ( spl10_11
  <=> ! [X1,X0] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl10_1
    | ~ spl10_11 ),
    inference(resolution,[],[f103,f54])).

fof(f54,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1) )
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f109,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f37,f107])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f104,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f33,f102])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f94,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f46,f91])).

fof(f46,plain,(
    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f29,f44])).

fof(f29,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f89,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f45,f86])).

fof(f45,plain,(
    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f30,f44])).

fof(f30,plain,(
    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f20])).

fof(f79,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f34,f77])).

fof(f34,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK9(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f22,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f75,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f28,f72])).

fof(f28,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f25,f57])).

fof(f25,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f32,f52])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:55:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.41  % (4383)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.44  % (4383)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f759,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f75,f79,f89,f94,f104,f109,f113,f117,f124,f136,f148,f154,f163,f169,f186,f191,f197,f202,f208,f244,f366,f484,f539,f547,f555,f564,f573,f576,f585,f595,f604,f612,f636,f696,f746,f749,f753,f757])).
% 0.21/0.44  fof(f757,plain,(
% 0.21/0.44    ~spl10_21 | spl10_26 | ~spl10_91),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f756])).
% 0.21/0.44  fof(f756,plain,(
% 0.21/0.44    $false | (~spl10_21 | spl10_26 | ~spl10_91)),
% 0.21/0.44    inference(subsumption_resolution,[],[f755,f162])).
% 0.21/0.44  fof(f162,plain,(
% 0.21/0.44    r2_hidden(k2_mcart_1(sK8),sK7) | ~spl10_21),
% 0.21/0.44    inference(avatar_component_clause,[],[f160])).
% 0.21/0.44  fof(f160,plain,(
% 0.21/0.44    spl10_21 <=> r2_hidden(k2_mcart_1(sK8),sK7)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.21/0.44  fof(f755,plain,(
% 0.21/0.44    ~r2_hidden(k2_mcart_1(sK8),sK7) | (spl10_26 | ~spl10_91)),
% 0.21/0.44    inference(forward_demodulation,[],[f185,f538])).
% 0.21/0.44  fof(f538,plain,(
% 0.21/0.44    k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) | ~spl10_91),
% 0.21/0.44    inference(avatar_component_clause,[],[f536])).
% 0.21/0.44  fof(f536,plain,(
% 0.21/0.44    spl10_91 <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_91])])).
% 0.21/0.44  fof(f185,plain,(
% 0.21/0.44    ~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | spl10_26),
% 0.21/0.44    inference(avatar_component_clause,[],[f183])).
% 0.21/0.44  fof(f183,plain,(
% 0.21/0.44    spl10_26 <=> r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 0.21/0.44  fof(f753,plain,(
% 0.21/0.44    spl10_25 | ~spl10_27 | ~spl10_96),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f752])).
% 0.21/0.44  fof(f752,plain,(
% 0.21/0.44    $false | (spl10_25 | ~spl10_27 | ~spl10_96)),
% 0.21/0.44    inference(subsumption_resolution,[],[f751,f190])).
% 0.21/0.44  fof(f190,plain,(
% 0.21/0.44    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) | ~spl10_27),
% 0.21/0.44    inference(avatar_component_clause,[],[f188])).
% 0.21/0.44  fof(f188,plain,(
% 0.21/0.44    spl10_27 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 0.21/0.44  fof(f751,plain,(
% 0.21/0.44    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) | (spl10_25 | ~spl10_96)),
% 0.21/0.44    inference(forward_demodulation,[],[f181,f584])).
% 0.21/0.44  fof(f584,plain,(
% 0.21/0.44    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | ~spl10_96),
% 0.21/0.44    inference(avatar_component_clause,[],[f582])).
% 0.21/0.44  fof(f582,plain,(
% 0.21/0.44    spl10_96 <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).
% 0.21/0.44  fof(f181,plain,(
% 0.21/0.44    ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | spl10_25),
% 0.21/0.44    inference(avatar_component_clause,[],[f179])).
% 0.21/0.44  fof(f179,plain,(
% 0.21/0.44    spl10_25 <=> r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 0.21/0.44  fof(f749,plain,(
% 0.21/0.44    spl10_24 | ~spl10_29 | ~spl10_112),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f748])).
% 0.21/0.44  fof(f748,plain,(
% 0.21/0.44    $false | (spl10_24 | ~spl10_29 | ~spl10_112)),
% 0.21/0.44    inference(subsumption_resolution,[],[f747,f201])).
% 0.21/0.44  fof(f201,plain,(
% 0.21/0.44    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | ~spl10_29),
% 0.21/0.44    inference(avatar_component_clause,[],[f199])).
% 0.21/0.44  fof(f199,plain,(
% 0.21/0.44    spl10_29 <=> r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 0.21/0.44  fof(f747,plain,(
% 0.21/0.44    ~r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | (spl10_24 | ~spl10_112)),
% 0.21/0.44    inference(forward_demodulation,[],[f177,f695])).
% 0.21/0.44  fof(f695,plain,(
% 0.21/0.44    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | ~spl10_112),
% 0.21/0.44    inference(avatar_component_clause,[],[f693])).
% 0.21/0.44  fof(f693,plain,(
% 0.21/0.44    spl10_112 <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_112])])).
% 0.21/0.44  fof(f177,plain,(
% 0.21/0.44    ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | spl10_24),
% 0.21/0.44    inference(avatar_component_clause,[],[f175])).
% 0.21/0.44  fof(f175,plain,(
% 0.21/0.44    spl10_24 <=> r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 0.21/0.44  fof(f746,plain,(
% 0.21/0.44    ~spl10_9 | ~spl10_19 | spl10_23 | spl10_87 | spl10_88 | spl10_89 | spl10_90 | ~spl10_101),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f745])).
% 0.21/0.44  fof(f745,plain,(
% 0.21/0.44    $false | (~spl10_9 | ~spl10_19 | spl10_23 | spl10_87 | spl10_88 | spl10_89 | spl10_90 | ~spl10_101)),
% 0.21/0.44    inference(subsumption_resolution,[],[f744,f147])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | ~spl10_19),
% 0.21/0.44    inference(avatar_component_clause,[],[f145])).
% 0.21/0.44  fof(f145,plain,(
% 0.21/0.44    spl10_19 <=> r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.21/0.44  fof(f744,plain,(
% 0.21/0.44    ~r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | (~spl10_9 | spl10_23 | spl10_87 | spl10_88 | spl10_89 | spl10_90 | ~spl10_101)),
% 0.21/0.44    inference(backward_demodulation,[],[f173,f743])).
% 0.21/0.44  fof(f743,plain,(
% 0.21/0.44    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | (~spl10_9 | spl10_87 | spl10_88 | spl10_89 | spl10_90 | ~spl10_101)),
% 0.21/0.44    inference(subsumption_resolution,[],[f742,f521])).
% 0.21/0.44  fof(f521,plain,(
% 0.21/0.44    k1_xboole_0 != sK0 | spl10_87),
% 0.21/0.44    inference(avatar_component_clause,[],[f520])).
% 0.21/0.44  fof(f520,plain,(
% 0.21/0.44    spl10_87 <=> k1_xboole_0 = sK0),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_87])])).
% 0.21/0.44  fof(f742,plain,(
% 0.21/0.44    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK0 | (~spl10_9 | spl10_88 | spl10_89 | spl10_90 | ~spl10_101)),
% 0.21/0.44    inference(subsumption_resolution,[],[f741,f525])).
% 0.21/0.44  fof(f525,plain,(
% 0.21/0.44    k1_xboole_0 != sK1 | spl10_88),
% 0.21/0.44    inference(avatar_component_clause,[],[f524])).
% 0.21/0.44  fof(f524,plain,(
% 0.21/0.44    spl10_88 <=> k1_xboole_0 = sK1),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).
% 0.21/0.44  fof(f741,plain,(
% 0.21/0.44    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl10_9 | spl10_89 | spl10_90 | ~spl10_101)),
% 0.21/0.44    inference(subsumption_resolution,[],[f740,f529])).
% 0.21/0.44  fof(f529,plain,(
% 0.21/0.44    k1_xboole_0 != sK2 | spl10_89),
% 0.21/0.44    inference(avatar_component_clause,[],[f528])).
% 0.21/0.44  fof(f528,plain,(
% 0.21/0.44    spl10_89 <=> k1_xboole_0 = sK2),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_89])])).
% 0.21/0.44  fof(f740,plain,(
% 0.21/0.44    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl10_9 | spl10_90 | ~spl10_101)),
% 0.21/0.44    inference(subsumption_resolution,[],[f739,f533])).
% 0.21/0.44  fof(f533,plain,(
% 0.21/0.44    k1_xboole_0 != sK3 | spl10_90),
% 0.21/0.44    inference(avatar_component_clause,[],[f532])).
% 0.21/0.44  fof(f532,plain,(
% 0.21/0.44    spl10_90 <=> k1_xboole_0 = sK3),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).
% 0.21/0.44  fof(f739,plain,(
% 0.21/0.44    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl10_9 | ~spl10_101)),
% 0.21/0.44    inference(resolution,[],[f635,f93])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~spl10_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f91])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    spl10_9 <=> m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.44  fof(f635,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl10_101),
% 0.21/0.44    inference(avatar_component_clause,[],[f634])).
% 0.21/0.44  fof(f634,plain,(
% 0.21/0.44    spl10_101 <=> ! [X1,X3,X0,X2,X4] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_101])])).
% 0.21/0.44  fof(f173,plain,(
% 0.21/0.44    ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | spl10_23),
% 0.21/0.44    inference(avatar_component_clause,[],[f171])).
% 0.21/0.44  fof(f171,plain,(
% 0.21/0.44    spl10_23 <=> r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 0.21/0.44  fof(f696,plain,(
% 0.21/0.44    spl10_112 | ~spl10_9 | ~spl10_80 | spl10_87 | spl10_88 | spl10_89 | spl10_90),
% 0.21/0.44    inference(avatar_split_clause,[],[f691,f532,f528,f524,f520,f482,f91,f693])).
% 0.21/0.44  fof(f482,plain,(
% 0.21/0.44    spl10_80 <=> ! [X1,X3,X0,X2,X4] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).
% 0.21/0.44  fof(f691,plain,(
% 0.21/0.44    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | (~spl10_9 | ~spl10_80 | spl10_87 | spl10_88 | spl10_89 | spl10_90)),
% 0.21/0.44    inference(subsumption_resolution,[],[f690,f521])).
% 0.21/0.44  fof(f690,plain,(
% 0.21/0.44    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK0 | (~spl10_9 | ~spl10_80 | spl10_88 | spl10_89 | spl10_90)),
% 0.21/0.44    inference(subsumption_resolution,[],[f689,f525])).
% 0.21/0.44  fof(f689,plain,(
% 0.21/0.44    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl10_9 | ~spl10_80 | spl10_89 | spl10_90)),
% 0.21/0.44    inference(subsumption_resolution,[],[f688,f529])).
% 0.21/0.44  fof(f688,plain,(
% 0.21/0.44    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl10_9 | ~spl10_80 | spl10_90)),
% 0.21/0.44    inference(subsumption_resolution,[],[f687,f533])).
% 0.21/0.44  fof(f687,plain,(
% 0.21/0.44    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl10_9 | ~spl10_80)),
% 0.21/0.44    inference(resolution,[],[f483,f93])).
% 0.21/0.44  fof(f483,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl10_80),
% 0.21/0.44    inference(avatar_component_clause,[],[f482])).
% 0.21/0.44  fof(f636,plain,(
% 0.21/0.44    spl10_101),
% 0.21/0.44    inference(avatar_split_clause,[],[f50,f634])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(definition_unfolding,[],[f40,f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f39,f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.21/0.44  fof(f612,plain,(
% 0.21/0.44    ~spl10_13 | spl10_28 | ~spl10_94),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f611])).
% 0.21/0.44  fof(f611,plain,(
% 0.21/0.44    $false | (~spl10_13 | spl10_28 | ~spl10_94)),
% 0.21/0.44    inference(subsumption_resolution,[],[f610,f196])).
% 0.21/0.44  fof(f196,plain,(
% 0.21/0.44    ~v1_xboole_0(sK6) | spl10_28),
% 0.21/0.44    inference(avatar_component_clause,[],[f194])).
% 0.21/0.44  fof(f194,plain,(
% 0.21/0.44    spl10_28 <=> v1_xboole_0(sK6)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).
% 0.21/0.44  fof(f610,plain,(
% 0.21/0.44    v1_xboole_0(sK6) | (~spl10_13 | ~spl10_94)),
% 0.21/0.44    inference(resolution,[],[f563,f112])).
% 0.21/0.44  fof(f112,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl10_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f111])).
% 0.21/0.44  fof(f111,plain,(
% 0.21/0.44    spl10_13 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.21/0.44  fof(f563,plain,(
% 0.21/0.44    m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) | ~spl10_94),
% 0.21/0.44    inference(avatar_component_clause,[],[f561])).
% 0.21/0.44  fof(f561,plain,(
% 0.21/0.44    spl10_94 <=> m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).
% 0.21/0.44  fof(f604,plain,(
% 0.21/0.44    ~spl10_13 | spl10_30 | ~spl10_93),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f603])).
% 0.21/0.44  fof(f603,plain,(
% 0.21/0.44    $false | (~spl10_13 | spl10_30 | ~spl10_93)),
% 0.21/0.44    inference(subsumption_resolution,[],[f602,f207])).
% 0.21/0.44  fof(f207,plain,(
% 0.21/0.44    ~v1_xboole_0(sK5) | spl10_30),
% 0.21/0.44    inference(avatar_component_clause,[],[f205])).
% 0.21/0.44  fof(f205,plain,(
% 0.21/0.44    spl10_30 <=> v1_xboole_0(sK5)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 0.21/0.44  fof(f602,plain,(
% 0.21/0.44    v1_xboole_0(sK5) | (~spl10_13 | ~spl10_93)),
% 0.21/0.44    inference(resolution,[],[f554,f112])).
% 0.21/0.44  fof(f554,plain,(
% 0.21/0.44    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | ~spl10_93),
% 0.21/0.44    inference(avatar_component_clause,[],[f552])).
% 0.21/0.44  fof(f552,plain,(
% 0.21/0.44    spl10_93 <=> m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_93])])).
% 0.21/0.44  fof(f595,plain,(
% 0.21/0.44    ~spl10_13 | spl10_20 | ~spl10_92),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f594])).
% 0.21/0.44  fof(f594,plain,(
% 0.21/0.44    $false | (~spl10_13 | spl10_20 | ~spl10_92)),
% 0.21/0.44    inference(subsumption_resolution,[],[f593,f153])).
% 0.21/0.44  fof(f153,plain,(
% 0.21/0.44    ~v1_xboole_0(sK4) | spl10_20),
% 0.21/0.44    inference(avatar_component_clause,[],[f151])).
% 0.21/0.44  fof(f151,plain,(
% 0.21/0.44    spl10_20 <=> v1_xboole_0(sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.21/0.44  fof(f593,plain,(
% 0.21/0.44    v1_xboole_0(sK4) | (~spl10_13 | ~spl10_92)),
% 0.21/0.44    inference(resolution,[],[f546,f112])).
% 0.21/0.44  fof(f546,plain,(
% 0.21/0.44    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | ~spl10_92),
% 0.21/0.44    inference(avatar_component_clause,[],[f544])).
% 0.21/0.44  fof(f544,plain,(
% 0.21/0.44    spl10_92 <=> m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).
% 0.21/0.44  fof(f585,plain,(
% 0.21/0.44    spl10_96 | ~spl10_9 | ~spl10_58 | spl10_87 | spl10_88 | spl10_89 | spl10_90),
% 0.21/0.44    inference(avatar_split_clause,[],[f578,f532,f528,f524,f520,f364,f91,f582])).
% 0.21/0.44  fof(f364,plain,(
% 0.21/0.44    spl10_58 <=> ! [X1,X3,X0,X2,X4] : (k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).
% 0.21/0.44  fof(f578,plain,(
% 0.21/0.44    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | (~spl10_9 | ~spl10_58 | spl10_87 | spl10_88 | spl10_89 | spl10_90)),
% 0.21/0.44    inference(subsumption_resolution,[],[f577,f533])).
% 0.21/0.44  fof(f577,plain,(
% 0.21/0.44    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | k1_xboole_0 = sK3 | (~spl10_9 | ~spl10_58 | spl10_87 | spl10_88 | spl10_89)),
% 0.21/0.44    inference(subsumption_resolution,[],[f565,f529])).
% 0.21/0.44  fof(f565,plain,(
% 0.21/0.44    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | (~spl10_9 | ~spl10_58 | spl10_87 | spl10_88)),
% 0.21/0.44    inference(subsumption_resolution,[],[f556,f525])).
% 0.21/0.44  fof(f556,plain,(
% 0.21/0.44    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | (~spl10_9 | ~spl10_58 | spl10_87)),
% 0.21/0.44    inference(subsumption_resolution,[],[f423,f521])).
% 0.21/0.44  fof(f423,plain,(
% 0.21/0.44    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl10_9 | ~spl10_58)),
% 0.21/0.44    inference(resolution,[],[f365,f93])).
% 0.21/0.44  fof(f365,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl10_58),
% 0.21/0.44    inference(avatar_component_clause,[],[f364])).
% 0.21/0.44  fof(f576,plain,(
% 0.21/0.44    ~spl10_13 | spl10_22 | ~spl10_95),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f575])).
% 0.21/0.44  fof(f575,plain,(
% 0.21/0.44    $false | (~spl10_13 | spl10_22 | ~spl10_95)),
% 0.21/0.44    inference(subsumption_resolution,[],[f574,f168])).
% 0.21/0.44  fof(f168,plain,(
% 0.21/0.44    ~v1_xboole_0(sK7) | spl10_22),
% 0.21/0.44    inference(avatar_component_clause,[],[f166])).
% 0.21/0.44  fof(f166,plain,(
% 0.21/0.44    spl10_22 <=> v1_xboole_0(sK7)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.21/0.44  fof(f574,plain,(
% 0.21/0.44    v1_xboole_0(sK7) | (~spl10_13 | ~spl10_95)),
% 0.21/0.44    inference(resolution,[],[f572,f112])).
% 0.21/0.44  fof(f572,plain,(
% 0.21/0.44    m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) | ~spl10_95),
% 0.21/0.44    inference(avatar_component_clause,[],[f570])).
% 0.21/0.44  fof(f570,plain,(
% 0.21/0.44    spl10_95 <=> m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_95])])).
% 0.21/0.44  fof(f573,plain,(
% 0.21/0.44    spl10_95 | ~spl10_5 | ~spl10_90),
% 0.21/0.44    inference(avatar_split_clause,[],[f566,f532,f72,f570])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    spl10_5 <=> m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.44  fof(f566,plain,(
% 0.21/0.44    m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) | (~spl10_5 | ~spl10_90)),
% 0.21/0.44    inference(backward_demodulation,[],[f74,f534])).
% 0.21/0.44  fof(f534,plain,(
% 0.21/0.44    k1_xboole_0 = sK3 | ~spl10_90),
% 0.21/0.44    inference(avatar_component_clause,[],[f532])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    m1_subset_1(sK7,k1_zfmisc_1(sK3)) | ~spl10_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f72])).
% 0.21/0.44  fof(f564,plain,(
% 0.21/0.44    spl10_94 | ~spl10_4 | ~spl10_89),
% 0.21/0.44    inference(avatar_split_clause,[],[f557,f528,f67,f561])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    spl10_4 <=> m1_subset_1(sK6,k1_zfmisc_1(sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.44  fof(f557,plain,(
% 0.21/0.44    m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) | (~spl10_4 | ~spl10_89)),
% 0.21/0.44    inference(backward_demodulation,[],[f69,f530])).
% 0.21/0.44  fof(f530,plain,(
% 0.21/0.44    k1_xboole_0 = sK2 | ~spl10_89),
% 0.21/0.44    inference(avatar_component_clause,[],[f528])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    m1_subset_1(sK6,k1_zfmisc_1(sK2)) | ~spl10_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f67])).
% 0.21/0.44  fof(f555,plain,(
% 0.21/0.44    spl10_93 | ~spl10_3 | ~spl10_88),
% 0.21/0.44    inference(avatar_split_clause,[],[f548,f524,f62,f552])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    spl10_3 <=> m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.44  fof(f548,plain,(
% 0.21/0.44    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | (~spl10_3 | ~spl10_88)),
% 0.21/0.44    inference(backward_demodulation,[],[f64,f526])).
% 0.21/0.44  fof(f526,plain,(
% 0.21/0.44    k1_xboole_0 = sK1 | ~spl10_88),
% 0.21/0.44    inference(avatar_component_clause,[],[f524])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    m1_subset_1(sK5,k1_zfmisc_1(sK1)) | ~spl10_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f62])).
% 0.21/0.44  fof(f547,plain,(
% 0.21/0.44    spl10_92 | ~spl10_2 | ~spl10_87),
% 0.21/0.44    inference(avatar_split_clause,[],[f540,f520,f57,f544])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    spl10_2 <=> m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.44  fof(f540,plain,(
% 0.21/0.44    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | (~spl10_2 | ~spl10_87)),
% 0.21/0.44    inference(backward_demodulation,[],[f59,f522])).
% 0.21/0.44  fof(f522,plain,(
% 0.21/0.44    k1_xboole_0 = sK0 | ~spl10_87),
% 0.21/0.44    inference(avatar_component_clause,[],[f520])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    m1_subset_1(sK4,k1_zfmisc_1(sK0)) | ~spl10_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f57])).
% 0.21/0.44  fof(f539,plain,(
% 0.21/0.44    spl10_87 | spl10_88 | spl10_89 | spl10_90 | spl10_91 | ~spl10_9 | ~spl10_37),
% 0.21/0.44    inference(avatar_split_clause,[],[f302,f242,f91,f536,f532,f528,f524,f520])).
% 0.21/0.44  fof(f242,plain,(
% 0.21/0.44    spl10_37 <=> ! [X1,X3,X0,X2,X4] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).
% 0.21/0.44  fof(f302,plain,(
% 0.21/0.44    k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl10_9 | ~spl10_37)),
% 0.21/0.44    inference(resolution,[],[f243,f93])).
% 0.21/0.44  fof(f243,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl10_37),
% 0.21/0.44    inference(avatar_component_clause,[],[f242])).
% 0.21/0.44  fof(f484,plain,(
% 0.21/0.44    spl10_80),
% 0.21/0.44    inference(avatar_split_clause,[],[f49,f482])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(definition_unfolding,[],[f41,f44])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f366,plain,(
% 0.21/0.44    spl10_58),
% 0.21/0.44    inference(avatar_split_clause,[],[f48,f364])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(definition_unfolding,[],[f42,f44])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f244,plain,(
% 0.21/0.44    spl10_37),
% 0.21/0.44    inference(avatar_split_clause,[],[f47,f242])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(definition_unfolding,[],[f43,f44])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f208,plain,(
% 0.21/0.44    ~spl10_30 | ~spl10_6 | ~spl10_29),
% 0.21/0.44    inference(avatar_split_clause,[],[f203,f199,f77,f205])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    spl10_6 <=> ! [X0,X2] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.44  fof(f203,plain,(
% 0.21/0.44    ~v1_xboole_0(sK5) | (~spl10_6 | ~spl10_29)),
% 0.21/0.44    inference(resolution,[],[f201,f78])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) ) | ~spl10_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f77])).
% 0.21/0.44  fof(f202,plain,(
% 0.21/0.44    spl10_29 | ~spl10_14 | ~spl10_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f158,f133,f115,f199])).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    spl10_14 <=> ! [X1,X0,X2] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.21/0.44  fof(f133,plain,(
% 0.21/0.44    spl10_17 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.44  fof(f158,plain,(
% 0.21/0.44    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | (~spl10_14 | ~spl10_17)),
% 0.21/0.44    inference(resolution,[],[f116,f135])).
% 0.21/0.44  fof(f135,plain,(
% 0.21/0.44    r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) | ~spl10_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f133])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) ) | ~spl10_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f115])).
% 0.21/0.44  fof(f197,plain,(
% 0.21/0.44    ~spl10_28 | ~spl10_6 | ~spl10_27),
% 0.21/0.44    inference(avatar_split_clause,[],[f192,f188,f77,f194])).
% 0.21/0.44  fof(f192,plain,(
% 0.21/0.44    ~v1_xboole_0(sK6) | (~spl10_6 | ~spl10_27)),
% 0.21/0.44    inference(resolution,[],[f190,f78])).
% 0.21/0.44  fof(f191,plain,(
% 0.21/0.44    spl10_27 | ~spl10_14 | ~spl10_15),
% 0.21/0.44    inference(avatar_split_clause,[],[f157,f121,f115,f188])).
% 0.21/0.44  fof(f121,plain,(
% 0.21/0.44    spl10_15 <=> r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.21/0.44  fof(f157,plain,(
% 0.21/0.44    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) | (~spl10_14 | ~spl10_15)),
% 0.21/0.44    inference(resolution,[],[f116,f123])).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | ~spl10_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f121])).
% 0.21/0.44  fof(f186,plain,(
% 0.21/0.44    ~spl10_23 | ~spl10_24 | ~spl10_25 | ~spl10_26),
% 0.21/0.44    inference(avatar_split_clause,[],[f31,f183,f179,f175,f171])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    (((((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)) & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(sK7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f11,f19,f18,f17,f16,f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0))) => (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(sK0)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK1))) => (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) => (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) => (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(sK7,k1_zfmisc_1(sK3)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) => ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)) & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(flattening,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 0.21/0.44    inference(negated_conjecture,[],[f8])).
% 0.21/0.44  fof(f8,conjecture,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_mcart_1)).
% 0.21/0.44  fof(f169,plain,(
% 0.21/0.44    ~spl10_22 | ~spl10_6 | ~spl10_21),
% 0.21/0.44    inference(avatar_split_clause,[],[f164,f160,f77,f166])).
% 0.21/0.44  fof(f164,plain,(
% 0.21/0.44    ~v1_xboole_0(sK7) | (~spl10_6 | ~spl10_21)),
% 0.21/0.44    inference(resolution,[],[f162,f78])).
% 0.21/0.44  fof(f163,plain,(
% 0.21/0.44    spl10_21 | ~spl10_8 | ~spl10_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f156,f115,f86,f160])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    spl10_8 <=> r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.44  fof(f156,plain,(
% 0.21/0.44    r2_hidden(k2_mcart_1(sK8),sK7) | (~spl10_8 | ~spl10_14)),
% 0.21/0.44    inference(resolution,[],[f116,f88])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | ~spl10_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f86])).
% 0.21/0.44  fof(f154,plain,(
% 0.21/0.44    ~spl10_20 | ~spl10_6 | ~spl10_19),
% 0.21/0.44    inference(avatar_split_clause,[],[f149,f145,f77,f151])).
% 0.21/0.44  fof(f149,plain,(
% 0.21/0.44    ~v1_xboole_0(sK4) | (~spl10_6 | ~spl10_19)),
% 0.21/0.44    inference(resolution,[],[f147,f78])).
% 0.21/0.44  fof(f148,plain,(
% 0.21/0.44    spl10_19 | ~spl10_12 | ~spl10_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f137,f133,f107,f145])).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    spl10_12 <=> ! [X1,X0,X2] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.21/0.44  fof(f137,plain,(
% 0.21/0.44    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | (~spl10_12 | ~spl10_17)),
% 0.21/0.44    inference(resolution,[],[f135,f108])).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) ) | ~spl10_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f107])).
% 0.21/0.44  fof(f136,plain,(
% 0.21/0.44    spl10_17 | ~spl10_12 | ~spl10_15),
% 0.21/0.44    inference(avatar_split_clause,[],[f125,f121,f107,f133])).
% 0.21/0.44  fof(f125,plain,(
% 0.21/0.44    r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) | (~spl10_12 | ~spl10_15)),
% 0.21/0.44    inference(resolution,[],[f123,f108])).
% 0.21/0.44  fof(f124,plain,(
% 0.21/0.44    spl10_15 | ~spl10_8 | ~spl10_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f119,f107,f86,f121])).
% 0.21/0.44  fof(f119,plain,(
% 0.21/0.44    r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | (~spl10_8 | ~spl10_12)),
% 0.21/0.44    inference(resolution,[],[f108,f88])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    spl10_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f38,f115])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.44  fof(f113,plain,(
% 0.21/0.44    spl10_13 | ~spl10_1 | ~spl10_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f105,f102,f52,f111])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    spl10_1 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    spl10_11 <=> ! [X1,X0] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | (~spl10_1 | ~spl10_11)),
% 0.21/0.44    inference(resolution,[],[f103,f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0) | ~spl10_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f52])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) ) | ~spl10_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f102])).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    spl10_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f37,f107])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f104,plain,(
% 0.21/0.44    spl10_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f33,f102])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    spl10_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f46,f91])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.21/0.44    inference(definition_unfolding,[],[f29,f44])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    spl10_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f45,f86])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.21/0.44    inference(definition_unfolding,[],[f30,f44])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    spl10_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f34,f77])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK9(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f22,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK9(X0),X0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.44    inference(rectify,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.44    inference(nnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    spl10_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f28,f72])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    spl10_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f27,f67])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    m1_subset_1(sK6,k1_zfmisc_1(sK2))),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    spl10_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f26,f62])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    spl10_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f25,f57])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl10_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f32,f52])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (4383)------------------------------
% 0.21/0.44  % (4383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (4383)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (4383)Memory used [KB]: 6780
% 0.21/0.44  % (4383)Time elapsed: 0.031 s
% 0.21/0.44  % (4383)------------------------------
% 0.21/0.44  % (4383)------------------------------
% 0.21/0.45  % (4375)Success in time 0.082 s
%------------------------------------------------------------------------------
