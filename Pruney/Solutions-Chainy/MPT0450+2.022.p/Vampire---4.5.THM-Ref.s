%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 151 expanded)
%              Number of leaves         :   28 (  71 expanded)
%              Depth                    :    6
%              Number of atoms          :  252 ( 415 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f57,f65,f69,f88,f98,f103,f109,f113,f134,f143,f148,f160,f167,f175,f188])).

fof(f188,plain,
    ( ~ spl2_2
    | ~ spl2_16
    | spl2_19
    | ~ spl2_20
    | ~ spl2_23 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_16
    | spl2_19
    | ~ spl2_20
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f149,f179])).

fof(f179,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(X0,sK1))
    | ~ spl2_2
    | ~ spl2_20
    | ~ spl2_23 ),
    inference(unit_resulting_resolution,[],[f47,f142,f174])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | v1_relat_1(X0) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f142,plain,
    ( ! [X2,X0] : r1_tarski(k3_xboole_0(X2,X0),X0)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl2_20
  <=> ! [X0,X2] : r1_tarski(k3_xboole_0(X2,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f47,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f149,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_16
    | spl2_19
    | ~ spl2_20 ),
    inference(unit_resulting_resolution,[],[f47,f133,f142,f112])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f133,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))
    | spl2_19 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl2_19
  <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f175,plain,
    ( spl2_23
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f89,f67,f63,f173])).

fof(f63,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f67,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(resolution,[],[f68,f64])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f167,plain,
    ( ~ spl2_1
    | ~ spl2_7
    | spl2_21
    | ~ spl2_22 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_7
    | spl2_21
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f147,f161])).

fof(f161,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0))
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f42,f159,f68])).

fof(f159,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl2_22
  <=> ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f42,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f147,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_21 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl2_21
  <=> v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f160,plain,
    ( spl2_22
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f83,f63,f55,f158])).

fof(f55,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f83,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f56,f64])).

fof(f56,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f148,plain,
    ( ~ spl2_21
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_16
    | spl2_18 ),
    inference(avatar_split_clause,[],[f135,f127,f111,f55,f40,f145])).

fof(f127,plain,
    ( spl2_18
  <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f135,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_16
    | spl2_18 ),
    inference(unit_resulting_resolution,[],[f42,f56,f129,f112])).

fof(f129,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))
    | spl2_18 ),
    inference(avatar_component_clause,[],[f127])).

fof(f143,plain,
    ( spl2_20
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f105,f101,f86,f141])).

fof(f86,plain,
    ( spl2_11
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f101,plain,
    ( spl2_14
  <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f105,plain,
    ( ! [X2,X0] : r1_tarski(k3_xboole_0(X2,X0),X0)
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(superposition,[],[f102,f87])).

fof(f87,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f86])).

fof(f102,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f101])).

fof(f134,plain,
    ( ~ spl2_18
    | ~ spl2_19
    | spl2_3
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f120,f107,f50,f131,f127])).

fof(f50,plain,
    ( spl2_3
  <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f107,plain,
    ( spl2_15
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f120,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))
    | spl2_3
    | ~ spl2_15 ),
    inference(resolution,[],[f108,f52])).

fof(f52,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f108,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f107])).

fof(f113,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f27,f111])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f109,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f38,f107])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f103,plain,
    ( spl2_14
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f99,f96,f101])).

fof(f96,plain,
    ( spl2_13
  <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f99,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f97,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f97,plain,
    ( ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f36,f96])).

fof(f36,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f88,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f33,f86])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f69,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f65,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f35,f63])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f57,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f29,f55])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f53,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f26,f50])).

fof(f26,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

fof(f48,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f25,f45])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f24,f40])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:49:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.46  % (6917)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (6912)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (6919)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (6912)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f43,f48,f53,f57,f65,f69,f88,f98,f103,f109,f113,f134,f143,f148,f160,f167,f175,f188])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    ~spl2_2 | ~spl2_16 | spl2_19 | ~spl2_20 | ~spl2_23),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f186])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    $false | (~spl2_2 | ~spl2_16 | spl2_19 | ~spl2_20 | ~spl2_23)),
% 0.20/0.47    inference(subsumption_resolution,[],[f149,f179])).
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k3_xboole_0(X0,sK1))) ) | (~spl2_2 | ~spl2_20 | ~spl2_23)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f47,f142,f174])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) ) | ~spl2_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f173])).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    spl2_23 <=> ! [X1,X0] : (v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    ( ! [X2,X0] : (r1_tarski(k3_xboole_0(X2,X0),X0)) ) | ~spl2_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f141])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    spl2_20 <=> ! [X0,X2] : r1_tarski(k3_xboole_0(X2,X0),X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    v1_relat_1(sK1) | ~spl2_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    spl2_2 <=> v1_relat_1(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_2 | ~spl2_16 | spl2_19 | ~spl2_20)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f47,f133,f142,f112])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f111])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    spl2_16 <=> ! [X1,X0] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) | spl2_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f131])).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    spl2_19 <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    spl2_23 | ~spl2_6 | ~spl2_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f89,f67,f63,f173])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    spl2_6 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl2_7 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1)) ) | (~spl2_6 | ~spl2_7)),
% 0.20/0.47    inference(resolution,[],[f68,f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f63])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f67])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    ~spl2_1 | ~spl2_7 | spl2_21 | ~spl2_22),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f166])).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    $false | (~spl2_1 | ~spl2_7 | spl2_21 | ~spl2_22)),
% 0.20/0.47    inference(subsumption_resolution,[],[f147,f161])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK0,X0))) ) | (~spl2_1 | ~spl2_7 | ~spl2_22)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f42,f159,f68])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl2_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f158])).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    spl2_22 <=> ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    v1_relat_1(sK0) | ~spl2_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    spl2_1 <=> v1_relat_1(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f145])).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    spl2_21 <=> v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.20/0.47  fof(f160,plain,(
% 0.20/0.47    spl2_22 | ~spl2_4 | ~spl2_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f83,f63,f55,f158])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    spl2_4 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f56,f64])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f55])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    ~spl2_21 | ~spl2_1 | ~spl2_4 | ~spl2_16 | spl2_18),
% 0.20/0.47    inference(avatar_split_clause,[],[f135,f127,f111,f55,f40,f145])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    spl2_18 <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_1 | ~spl2_4 | ~spl2_16 | spl2_18)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f42,f56,f129,f112])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) | spl2_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f127])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    spl2_20 | ~spl2_11 | ~spl2_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f105,f101,f86,f141])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl2_11 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    spl2_14 <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    ( ! [X2,X0] : (r1_tarski(k3_xboole_0(X2,X0),X0)) ) | (~spl2_11 | ~spl2_14)),
% 0.20/0.47    inference(superposition,[],[f102,f87])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f86])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))) ) | ~spl2_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f101])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    ~spl2_18 | ~spl2_19 | spl2_3 | ~spl2_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f120,f107,f50,f131,f127])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    spl2_3 <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    spl2_15 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) | ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) | (spl2_3 | ~spl2_15)),
% 0.20/0.47    inference(resolution,[],[f108,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) | spl2_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f50])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f107])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    spl2_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f27,f111])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    spl2_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f38,f107])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    spl2_14 | ~spl2_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f99,f96,f101])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    spl2_13 <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))) ) | ~spl2_13),
% 0.20/0.47    inference(forward_demodulation,[],[f97,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) ) | ~spl2_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f96])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    spl2_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f36,f96])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    spl2_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f33,f86])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl2_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f28,f67])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    spl2_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f35,f63])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    spl2_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f29,f55])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ~spl2_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f26,f50])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f12])).
% 0.20/0.47  fof(f12,conjecture,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    spl2_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f25,f45])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    spl2_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f24,f40])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    v1_relat_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (6912)------------------------------
% 0.20/0.47  % (6912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (6912)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (6912)Memory used [KB]: 6140
% 0.20/0.47  % (6912)Time elapsed: 0.054 s
% 0.20/0.47  % (6912)------------------------------
% 0.20/0.47  % (6912)------------------------------
% 0.20/0.47  % (6921)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (6913)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (6907)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (6920)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (6906)Success in time 0.123 s
%------------------------------------------------------------------------------
