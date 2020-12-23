%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 161 expanded)
%              Number of leaves         :   27 (  77 expanded)
%              Depth                    :    6
%              Number of atoms          :  256 ( 417 expanded)
%              Number of equality atoms :   28 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f48,f52,f56,f60,f64,f68,f73,f85,f91,f103,f125,f135,f145,f162,f168,f172])).

fof(f172,plain,
    ( ~ spl3_5
    | ~ spl3_9
    | ~ spl3_10
    | spl3_26 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_10
    | spl3_26 ),
    inference(subsumption_resolution,[],[f170,f72])).

fof(f72,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_10
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f170,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl3_5
    | ~ spl3_9
    | spl3_26 ),
    inference(subsumption_resolution,[],[f169,f51])).

fof(f51,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f169,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,sK0)
    | ~ spl3_9
    | spl3_26 ),
    inference(resolution,[],[f167,f67])).

fof(f67,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_9
  <=> ! [X1,X3,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f167,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl3_26
  <=> r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f168,plain,
    ( ~ spl3_26
    | spl3_21
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f163,f159,f132,f165])).

fof(f132,plain,
    ( spl3_21
  <=> r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f159,plain,
    ( spl3_25
  <=> k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f163,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl3_21
    | ~ spl3_25 ),
    inference(backward_demodulation,[],[f134,f161])).

fof(f161,plain,
    ( k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f159])).

fof(f134,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f132])).

fof(f162,plain,
    ( spl3_25
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f148,f142,f54,f159])).

fof(f54,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f142,plain,
    ( spl3_22
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f148,plain,
    ( k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(resolution,[],[f144,f55])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f144,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f142])).

% (21587)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
fof(f145,plain,
    ( spl3_22
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f140,f122,f58,f41,f36,f142])).

fof(f36,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f41,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f58,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f122,plain,
    ( spl3_19
  <=> k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f140,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f139,f43])).

fof(f43,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f139,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f138,f38])).

fof(f38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f138,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(superposition,[],[f59,f124])).

fof(f124,plain,
    ( k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f122])).

fof(f59,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f135,plain,
    ( ~ spl3_21
    | spl3_13
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f130,f122,f88,f132])).

fof(f88,plain,
    ( spl3_13
  <=> r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f130,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl3_13
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f90,f124])).

fof(f90,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f88])).

fof(f125,plain,
    ( spl3_19
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f113,f101,f41,f122])).

fof(f101,plain,
    ( spl3_15
  <=> ! [X0] :
        ( k4_subset_1(sK0,X0,sK2) = k2_xboole_0(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f113,plain,
    ( k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(resolution,[],[f102,f43])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,X0,sK2) = k2_xboole_0(X0,sK2) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f97,f62,f36,f101])).

fof(f62,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f97,plain,
    ( ! [X0] :
        ( k4_subset_1(sK0,X0,sK2) = k2_xboole_0(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f63,f38])).

fof(f63,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f91,plain,
    ( ~ spl3_13
    | spl3_1
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f86,f82,f31,f88])).

fof(f31,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f82,plain,
    ( spl3_12
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f86,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl3_1
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f33,f84])).

fof(f84,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f33,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f85,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f75,f54,f41,f82])).

fof(f75,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f55,f43])).

fof(f73,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f69,f50,f46,f71])).

fof(f46,plain,
    ( spl3_4
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f69,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f51,f47])).

fof(f47,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f68,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).

fof(f64,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f60,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f58])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f56,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f52,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f48,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f44,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(f39,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f36])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f31])).

fof(f23,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:31:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (21586)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.43  % (21585)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.43  % (21586)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f173,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f34,f39,f44,f48,f52,f56,f60,f64,f68,f73,f85,f91,f103,f125,f135,f145,f162,f168,f172])).
% 0.21/0.43  fof(f172,plain,(
% 0.21/0.43    ~spl3_5 | ~spl3_9 | ~spl3_10 | spl3_26),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.43  fof(f171,plain,(
% 0.21/0.43    $false | (~spl3_5 | ~spl3_9 | ~spl3_10 | spl3_26)),
% 0.21/0.43    inference(subsumption_resolution,[],[f170,f72])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl3_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f71])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    spl3_10 <=> ! [X0] : r1_tarski(X0,X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.43  fof(f170,plain,(
% 0.21/0.43    ~r1_tarski(sK0,sK0) | (~spl3_5 | ~spl3_9 | spl3_26)),
% 0.21/0.43    inference(subsumption_resolution,[],[f169,f51])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f50])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    spl3_5 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.43  fof(f169,plain,(
% 0.21/0.43    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,sK0) | (~spl3_9 | spl3_26)),
% 0.21/0.43    inference(resolution,[],[f167,f67])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f66])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    spl3_9 <=> ! [X1,X3,X0,X2] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.43  fof(f167,plain,(
% 0.21/0.43    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) | spl3_26),
% 0.21/0.43    inference(avatar_component_clause,[],[f165])).
% 0.21/0.43  fof(f165,plain,(
% 0.21/0.43    spl3_26 <=> r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.43  fof(f168,plain,(
% 0.21/0.43    ~spl3_26 | spl3_21 | ~spl3_25),
% 0.21/0.43    inference(avatar_split_clause,[],[f163,f159,f132,f165])).
% 0.21/0.43  fof(f132,plain,(
% 0.21/0.43    spl3_21 <=> r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.43  fof(f159,plain,(
% 0.21/0.43    spl3_25 <=> k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.43  fof(f163,plain,(
% 0.21/0.43    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) | (spl3_21 | ~spl3_25)),
% 0.21/0.43    inference(backward_demodulation,[],[f134,f161])).
% 0.21/0.43  fof(f161,plain,(
% 0.21/0.43    k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_25),
% 0.21/0.43    inference(avatar_component_clause,[],[f159])).
% 0.21/0.43  fof(f134,plain,(
% 0.21/0.43    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) | spl3_21),
% 0.21/0.43    inference(avatar_component_clause,[],[f132])).
% 0.21/0.43  fof(f162,plain,(
% 0.21/0.43    spl3_25 | ~spl3_6 | ~spl3_22),
% 0.21/0.43    inference(avatar_split_clause,[],[f148,f142,f54,f159])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl3_6 <=> ! [X1,X0] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.43  fof(f142,plain,(
% 0.21/0.43    spl3_22 <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.43  fof(f148,plain,(
% 0.21/0.43    k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_6 | ~spl3_22)),
% 0.21/0.43    inference(resolution,[],[f144,f55])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) ) | ~spl3_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f54])).
% 0.21/0.43  fof(f144,plain,(
% 0.21/0.43    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~spl3_22),
% 0.21/0.43    inference(avatar_component_clause,[],[f142])).
% 0.21/0.43  % (21587)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.43  fof(f145,plain,(
% 0.21/0.43    spl3_22 | ~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_19),
% 0.21/0.43    inference(avatar_split_clause,[],[f140,f122,f58,f41,f36,f142])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl3_7 <=> ! [X1,X0,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.43  fof(f122,plain,(
% 0.21/0.43    spl3_19 <=> k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.43  fof(f140,plain,(
% 0.21/0.43    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | (~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_19)),
% 0.21/0.43    inference(subsumption_resolution,[],[f139,f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f41])).
% 0.21/0.43  fof(f139,plain,(
% 0.21/0.43    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl3_2 | ~spl3_7 | ~spl3_19)),
% 0.21/0.43    inference(subsumption_resolution,[],[f138,f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f36])).
% 0.21/0.43  fof(f138,plain,(
% 0.21/0.43    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl3_7 | ~spl3_19)),
% 0.21/0.43    inference(superposition,[],[f59,f124])).
% 0.21/0.43  fof(f124,plain,(
% 0.21/0.43    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2) | ~spl3_19),
% 0.21/0.43    inference(avatar_component_clause,[],[f122])).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f58])).
% 0.21/0.43  fof(f135,plain,(
% 0.21/0.43    ~spl3_21 | spl3_13 | ~spl3_19),
% 0.21/0.43    inference(avatar_split_clause,[],[f130,f122,f88,f132])).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    spl3_13 <=> r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.43  fof(f130,plain,(
% 0.21/0.43    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) | (spl3_13 | ~spl3_19)),
% 0.21/0.43    inference(backward_demodulation,[],[f90,f124])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) | spl3_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f88])).
% 0.21/0.43  fof(f125,plain,(
% 0.21/0.43    spl3_19 | ~spl3_3 | ~spl3_15),
% 0.21/0.43    inference(avatar_split_clause,[],[f113,f101,f41,f122])).
% 0.21/0.43  fof(f101,plain,(
% 0.21/0.43    spl3_15 <=> ! [X0] : (k4_subset_1(sK0,X0,sK2) = k2_xboole_0(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2) | (~spl3_3 | ~spl3_15)),
% 0.21/0.43    inference(resolution,[],[f102,f43])).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK2) = k2_xboole_0(X0,sK2)) ) | ~spl3_15),
% 0.21/0.43    inference(avatar_component_clause,[],[f101])).
% 0.21/0.43  fof(f103,plain,(
% 0.21/0.43    spl3_15 | ~spl3_2 | ~spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f97,f62,f36,f101])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    spl3_8 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.43  fof(f97,plain,(
% 0.21/0.43    ( ! [X0] : (k4_subset_1(sK0,X0,sK2) = k2_xboole_0(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | (~spl3_2 | ~spl3_8)),
% 0.21/0.43    inference(resolution,[],[f63,f38])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f62])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    ~spl3_13 | spl3_1 | ~spl3_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f86,f82,f31,f88])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    spl3_1 <=> r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    spl3_12 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) | (spl3_1 | ~spl3_12)),
% 0.21/0.43    inference(backward_demodulation,[],[f33,f84])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f82])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) | spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f31])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    spl3_12 | ~spl3_3 | ~spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f75,f54,f41,f82])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | (~spl3_3 | ~spl3_6)),
% 0.21/0.43    inference(resolution,[],[f55,f43])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    spl3_10 | ~spl3_4 | ~spl3_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f69,f50,f46,f71])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    spl3_4 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl3_4 | ~spl3_5)),
% 0.21/0.43    inference(superposition,[],[f51,f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl3_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f46])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    spl3_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f29,f66])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f62])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(flattening,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f58])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(flattening,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f26,f54])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    spl3_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f25,f50])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    spl3_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f46])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.43    inference(rectify,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f21,f41])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f19,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ? [X2] : (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f36])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ~spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f31])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (21586)------------------------------
% 0.21/0.43  % (21586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (21586)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (21586)Memory used [KB]: 6140
% 0.21/0.43  % (21586)Time elapsed: 0.009 s
% 0.21/0.43  % (21586)------------------------------
% 0.21/0.43  % (21586)------------------------------
% 0.21/0.43  % (21575)Success in time 0.069 s
%------------------------------------------------------------------------------
