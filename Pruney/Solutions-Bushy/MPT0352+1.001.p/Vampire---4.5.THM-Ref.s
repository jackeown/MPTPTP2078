%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0352+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 181 expanded)
%              Number of leaves         :   24 (  81 expanded)
%              Depth                    :    9
%              Number of atoms          :  291 ( 595 expanded)
%              Number of equality atoms :   29 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f345,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f57,f59,f71,f84,f93,f97,f123,f131,f139,f144,f234,f277,f282,f306,f336,f343])).

fof(f343,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | spl3_5
    | ~ spl3_15
    | ~ spl3_29 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_4
    | spl3_5
    | ~ spl3_15
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f55,f341])).

fof(f341,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_15
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f339,f130])).

fof(f130,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl3_15
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f339,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_29 ),
    inference(unit_resulting_resolution,[],[f37,f52,f276])).

fof(f276,plain,
    ( ! [X2,X3,X1] :
        ( r1_tarski(k4_xboole_0(X1,X3),k3_subset_1(X1,X2))
        | ~ r1_tarski(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl3_29
  <=> ! [X1,X3,X2] :
        ( r1_tarski(k4_xboole_0(X1,X3),k3_subset_1(X1,X2))
        | ~ r1_tarski(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f52,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_4
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f37,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f55,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_5
  <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f336,plain,
    ( spl3_4
    | ~ spl3_5
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | spl3_4
    | ~ spl3_5
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f51,f334])).

fof(f334,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_5
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f333,f138])).

fof(f138,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl3_16
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f333,plain,
    ( r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),sK2)
    | ~ spl3_5
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f327,f252])).

fof(f252,plain,
    ( sK2 = k4_xboole_0(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f240,f143])).

fof(f143,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl3_17
  <=> sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f240,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_15
    | ~ spl3_27 ),
    inference(superposition,[],[f233,f130])).

fof(f233,plain,
    ( ! [X0,X1] : k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl3_27
  <=> ! [X1,X0] : k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f327,plain,
    ( r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k4_xboole_0(sK0,k3_subset_1(sK0,sK2)))
    | ~ spl3_5
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(unit_resulting_resolution,[],[f56,f281,f305])).

fof(f305,plain,
    ( ! [X6,X4,X5] :
        ( r1_tarski(k3_subset_1(X4,X5),k4_xboole_0(X4,X6))
        | ~ r1_tarski(X6,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(X4)) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl3_31
  <=> ! [X5,X4,X6] :
        ( r1_tarski(k3_subset_1(X4,X5),k4_xboole_0(X4,X6))
        | ~ r1_tarski(X6,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f281,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl3_30
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f56,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f51,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f306,plain,
    ( spl3_31
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f110,f91,f82,f304])).

fof(f82,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f91,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f110,plain,
    ( ! [X6,X4,X5] :
        ( r1_tarski(k3_subset_1(X4,X5),k4_xboole_0(X4,X6))
        | ~ r1_tarski(X6,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(X4)) )
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(superposition,[],[f83,f92])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f91])).

fof(f83,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f282,plain,
    ( spl3_30
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f126,f120,f69,f279])).

fof(f69,plain,
    ( spl3_8
  <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f120,plain,
    ( spl3_14
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f126,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(superposition,[],[f70,f122])).

fof(f122,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f70,plain,
    ( ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f277,plain,
    ( spl3_29
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f109,f91,f82,f275])).

fof(f109,plain,
    ( ! [X2,X3,X1] :
        ( r1_tarski(k4_xboole_0(X1,X3),k3_subset_1(X1,X2))
        | ~ r1_tarski(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(superposition,[],[f83,f92])).

fof(f234,plain,
    ( spl3_27
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f106,f91,f69,f232])).

fof(f106,plain,
    ( ! [X0,X1] : k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f70,f92])).

fof(f144,plain,
    ( spl3_17
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f117,f95,f40,f141])).

fof(f40,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f95,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f117,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f42,f96])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f139,plain,
    ( spl3_16
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f116,f95,f35,f136])).

fof(f116,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f37,f96])).

fof(f131,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f105,f91,f40,f128])).

fof(f105,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f42,f92])).

fof(f123,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f104,f91,f35,f120])).

fof(f104,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f37,f92])).

fof(f97,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f31,f95])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f93,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f30,f91])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f84,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f32,f82])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f71,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f28,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f59,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f58,f54,f50])).

fof(f58,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f24,f56])).

fof(f24,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | ~ r1_tarski(sK1,X2) )
        & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | r1_tarski(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | ~ r1_tarski(sK1,sK2) )
      & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | r1_tarski(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f57,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f23,f54,f50])).

fof(f23,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f40])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f21,f35])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

%------------------------------------------------------------------------------
