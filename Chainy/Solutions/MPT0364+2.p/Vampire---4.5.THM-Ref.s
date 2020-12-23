%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0364+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:26 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 142 expanded)
%              Number of leaves         :   18 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  206 ( 444 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2500,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1174,f1179,f1188,f1189,f1820,f2047,f2428,f2474])).

fof(f2474,plain,
    ( ~ spl25_2
    | ~ spl25_3
    | spl25_4
    | ~ spl25_12
    | ~ spl25_13 ),
    inference(avatar_contradiction_clause,[],[f2473])).

fof(f2473,plain,
    ( $false
    | ~ spl25_2
    | ~ spl25_3
    | spl25_4
    | ~ spl25_12
    | ~ spl25_13 ),
    inference(subsumption_resolution,[],[f2472,f2427])).

fof(f2427,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl25_13 ),
    inference(avatar_component_clause,[],[f2425])).

fof(f2425,plain,
    ( spl25_13
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_13])])).

fof(f2472,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl25_2
    | ~ spl25_3
    | spl25_4
    | ~ spl25_12 ),
    inference(backward_demodulation,[],[f1735,f2464])).

fof(f2464,plain,
    ( sK0 = k2_xboole_0(sK2,sK0)
    | ~ spl25_12 ),
    inference(unit_resulting_resolution,[],[f2046,f790])).

fof(f790,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f526])).

fof(f526,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f2046,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl25_12 ),
    inference(avatar_component_clause,[],[f2044])).

fof(f2044,plain,
    ( spl25_12
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_12])])).

fof(f1735,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl25_2
    | ~ spl25_3
    | spl25_4 ),
    inference(forward_demodulation,[],[f1726,f1033])).

fof(f1033,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1726,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK2,k4_xboole_0(sK0,sK2)))
    | ~ spl25_2
    | ~ spl25_3
    | spl25_4 ),
    inference(backward_demodulation,[],[f1593,f1702])).

fof(f1702,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl25_2 ),
    inference(unit_resulting_resolution,[],[f1178,f856])).

fof(f856,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f581])).

fof(f581,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f458])).

fof(f458,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1178,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl25_2 ),
    inference(avatar_component_clause,[],[f1176])).

fof(f1176,plain,
    ( spl25_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_2])])).

fof(f1593,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2)))
    | ~ spl25_3
    | spl25_4 ),
    inference(unit_resulting_resolution,[],[f1186,f1183,f807])).

fof(f807,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f545])).

fof(f545,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f544])).

fof(f544,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f141])).

fof(f141,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f1183,plain,
    ( r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl25_3 ),
    inference(avatar_component_clause,[],[f1181])).

fof(f1181,plain,
    ( spl25_3
  <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_3])])).

fof(f1186,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl25_4 ),
    inference(avatar_component_clause,[],[f1185])).

fof(f1185,plain,
    ( spl25_4
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_4])])).

fof(f2428,plain,
    ( spl25_13
    | ~ spl25_1 ),
    inference(avatar_split_clause,[],[f2038,f1171,f2425])).

fof(f1171,plain,
    ( spl25_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_1])])).

fof(f2038,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl25_1 ),
    inference(forward_demodulation,[],[f2029,f1707])).

fof(f1707,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f1703,f1096])).

fof(f1096,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1703,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f868,f856])).

fof(f868,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f507])).

fof(f507,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f2029,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0))
    | ~ spl25_1 ),
    inference(unit_resulting_resolution,[],[f847,f868,f1173,f851])).

fof(f851,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f686])).

fof(f686,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f575])).

fof(f575,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f504])).

fof(f504,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(f1173,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl25_1 ),
    inference(avatar_component_clause,[],[f1171])).

fof(f847,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f2047,plain,
    ( spl25_12
    | ~ spl25_2 ),
    inference(avatar_split_clause,[],[f2037,f1176,f2044])).

fof(f2037,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl25_2 ),
    inference(forward_demodulation,[],[f2030,f1707])).

fof(f2030,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,k1_xboole_0))
    | ~ spl25_2 ),
    inference(unit_resulting_resolution,[],[f847,f868,f1178,f851])).

fof(f1820,plain,
    ( ~ spl25_2
    | spl25_3
    | ~ spl25_4 ),
    inference(avatar_contradiction_clause,[],[f1819])).

fof(f1819,plain,
    ( $false
    | ~ spl25_2
    | spl25_3
    | ~ spl25_4 ),
    inference(subsumption_resolution,[],[f1746,f1763])).

fof(f1763,plain,
    ( ! [X0] : r1_xboole_0(sK1,k4_xboole_0(X0,sK2))
    | ~ spl25_4 ),
    inference(unit_resulting_resolution,[],[f1187,f814])).

fof(f814,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f554])).

fof(f554,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f155])).

fof(f155,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f1187,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl25_4 ),
    inference(avatar_component_clause,[],[f1185])).

fof(f1746,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl25_2
    | spl25_3 ),
    inference(forward_demodulation,[],[f1182,f1702])).

fof(f1182,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | spl25_3 ),
    inference(avatar_component_clause,[],[f1181])).

fof(f1189,plain,
    ( ~ spl25_3
    | ~ spl25_4 ),
    inference(avatar_split_clause,[],[f777,f1185,f1181])).

fof(f777,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f674])).

fof(f674,plain,
    ( ( ~ r1_tarski(sK1,sK2)
      | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & ( r1_tarski(sK1,sK2)
      | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f671,f673,f672])).

fof(f672,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,X2)
              | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,X2)
            | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & ( r1_tarski(sK1,X2)
            | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f673,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,X2)
          | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
        & ( r1_tarski(sK1,X2)
          | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(sK1,sK2)
        | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
      & ( r1_tarski(sK1,sK2)
        | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f671,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f670])).

fof(f670,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f514])).

fof(f514,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f506])).

fof(f506,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f505])).

fof(f505,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f1188,plain,
    ( spl25_3
    | spl25_4 ),
    inference(avatar_split_clause,[],[f776,f1185,f1181])).

fof(f776,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f674])).

fof(f1179,plain,(
    spl25_2 ),
    inference(avatar_split_clause,[],[f775,f1176])).

fof(f775,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f674])).

fof(f1174,plain,(
    spl25_1 ),
    inference(avatar_split_clause,[],[f774,f1171])).

fof(f774,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f674])).
%------------------------------------------------------------------------------
