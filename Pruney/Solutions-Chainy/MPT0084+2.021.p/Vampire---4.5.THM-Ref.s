%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:17 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 150 expanded)
%              Number of leaves         :   28 (  71 expanded)
%              Depth                    :    6
%              Number of atoms          :  239 ( 384 expanded)
%              Number of equality atoms :   49 (  84 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5963,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f56,f73,f81,f85,f89,f93,f107,f111,f176,f224,f291,f456,f545,f620,f1258,f1805,f5909,f5956])).

fof(f5956,plain,
    ( ~ spl4_2
    | spl4_21
    | ~ spl4_45
    | ~ spl4_73
    | ~ spl4_173 ),
    inference(avatar_contradiction_clause,[],[f5955])).

fof(f5955,plain,
    ( $false
    | ~ spl4_2
    | spl4_21
    | ~ spl4_45
    | ~ spl4_73
    | ~ spl4_173 ),
    inference(subsumption_resolution,[],[f1818,f5912])).

fof(f5912,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK0)
    | spl4_21
    | ~ spl4_173 ),
    inference(unit_resulting_resolution,[],[f223,f5908])).

fof(f5908,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X3),X2)
        | k1_xboole_0 = k3_xboole_0(X2,X3) )
    | ~ spl4_173 ),
    inference(avatar_component_clause,[],[f5907])).

fof(f5907,plain,
    ( spl4_173
  <=> ! [X3,X2] :
        ( k1_xboole_0 = k3_xboole_0(X2,X3)
        | ~ r1_xboole_0(k3_xboole_0(X2,X3),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_173])])).

fof(f223,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl4_21
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f1818,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_45
    | ~ spl4_73 ),
    inference(unit_resulting_resolution,[],[f50,f1804,f544])).

fof(f544,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_xboole_0(X2,X0)
        | ~ r1_xboole_0(X2,X1) )
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f543])).

fof(f543,plain,
    ( spl4_45
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X2,X1)
        | r1_xboole_0(X2,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f1804,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f1802])).

fof(f1802,plain,
    ( spl4_73
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f50,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f5909,plain,
    ( spl4_173
    | ~ spl4_40
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f639,f618,f454,f5907])).

fof(f454,plain,
    ( spl4_40
  <=> ! [X3,X4] :
        ( k1_xboole_0 = k3_xboole_0(X4,X3)
        | ~ r1_xboole_0(X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f618,plain,
    ( spl4_48
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f639,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = k3_xboole_0(X2,X3)
        | ~ r1_xboole_0(k3_xboole_0(X2,X3),X2) )
    | ~ spl4_40
    | ~ spl4_48 ),
    inference(superposition,[],[f619,f455])).

fof(f455,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 = k3_xboole_0(X4,X3)
        | ~ r1_xboole_0(X3,X4) )
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f454])).

fof(f619,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f618])).

fof(f1805,plain,
    ( spl4_73
    | ~ spl4_27
    | ~ spl4_61 ),
    inference(avatar_split_clause,[],[f1259,f1256,f288,f1802])).

fof(f288,plain,
    ( spl4_27
  <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f1256,plain,
    ( spl4_61
  <=> ! [X18,X20,X19] :
        ( k1_xboole_0 != k3_xboole_0(X18,k3_xboole_0(X19,X20))
        | r1_xboole_0(k3_xboole_0(X18,X19),X20) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f1259,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl4_27
    | ~ spl4_61 ),
    inference(unit_resulting_resolution,[],[f290,f1257])).

fof(f1257,plain,
    ( ! [X19,X20,X18] :
        ( k1_xboole_0 != k3_xboole_0(X18,k3_xboole_0(X19,X20))
        | r1_xboole_0(k3_xboole_0(X18,X19),X20) )
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f1256])).

fof(f290,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f288])).

fof(f1258,plain,
    ( spl4_61
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f204,f174,f87,f1256])).

fof(f87,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f174,plain,
    ( spl4_19
  <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f204,plain,
    ( ! [X19,X20,X18] :
        ( k1_xboole_0 != k3_xboole_0(X18,k3_xboole_0(X19,X20))
        | r1_xboole_0(k3_xboole_0(X18,X19),X20) )
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(superposition,[],[f88,f175])).

fof(f175,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f174])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f87])).

fof(f620,plain,
    ( spl4_48
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f159,f109,f105,f618])).

fof(f105,plain,
    ( spl4_14
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f109,plain,
    ( spl4_15
  <=> ! [X1,X0] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f159,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f158,f106])).

fof(f106,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f105])).

fof(f158,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(superposition,[],[f106,f110])).

fof(f110,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f109])).

fof(f545,plain,
    ( spl4_45
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f141,f91,f79,f543])).

fof(f79,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f91,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X2,X1)
        | r1_xboole_0(X2,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(superposition,[],[f92,f80])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f79])).

fof(f92,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X1) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f91])).

fof(f456,plain,
    ( spl4_40
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f124,f83,f71,f454])).

fof(f71,plain,
    ( spl4_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f83,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f124,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 = k3_xboole_0(X4,X3)
        | ~ r1_xboole_0(X3,X4) )
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(superposition,[],[f84,f72])).

fof(f72,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f291,plain,
    ( spl4_27
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f123,f83,f53,f288])).

fof(f53,plain,
    ( spl4_3
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f123,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f55,f84])).

fof(f55,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f224,plain,
    ( ~ spl4_21
    | spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f132,f87,f43,f221])).

fof(f43,plain,
    ( spl4_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f132,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl4_1
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f45,f88])).

fof(f45,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f176,plain,(
    spl4_19 ),
    inference(avatar_split_clause,[],[f38,f174])).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f111,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f31,f109])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f107,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f30,f105])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f93,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f40,f91])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f89,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f37,f87])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f85,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f36,f83])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f81,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f35,f79])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f73,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f56,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f51,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:39:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.41  % (21330)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.43  % (21337)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.43  % (21338)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.45  % (21334)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.46  % (21331)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.46  % (21332)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.46  % (21327)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.47  % (21339)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.47  % (21340)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.49  % (21336)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.49  % (21342)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.50  % (21328)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.50  % (21333)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (21329)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.50  % (21335)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.51  % (21343)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.51  % (21345)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.51  % (21344)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 2.23/0.64  % (21332)Refutation found. Thanks to Tanya!
% 2.23/0.64  % SZS status Theorem for theBenchmark
% 2.23/0.64  % SZS output start Proof for theBenchmark
% 2.23/0.64  fof(f5963,plain,(
% 2.23/0.64    $false),
% 2.23/0.64    inference(avatar_sat_refutation,[],[f46,f51,f56,f73,f81,f85,f89,f93,f107,f111,f176,f224,f291,f456,f545,f620,f1258,f1805,f5909,f5956])).
% 2.23/0.64  fof(f5956,plain,(
% 2.23/0.64    ~spl4_2 | spl4_21 | ~spl4_45 | ~spl4_73 | ~spl4_173),
% 2.23/0.64    inference(avatar_contradiction_clause,[],[f5955])).
% 2.23/0.64  fof(f5955,plain,(
% 2.23/0.64    $false | (~spl4_2 | spl4_21 | ~spl4_45 | ~spl4_73 | ~spl4_173)),
% 2.23/0.64    inference(subsumption_resolution,[],[f1818,f5912])).
% 2.23/0.64  fof(f5912,plain,(
% 2.23/0.64    ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK0) | (spl4_21 | ~spl4_173)),
% 2.23/0.64    inference(unit_resulting_resolution,[],[f223,f5908])).
% 2.23/0.64  fof(f5908,plain,(
% 2.23/0.64    ( ! [X2,X3] : (~r1_xboole_0(k3_xboole_0(X2,X3),X2) | k1_xboole_0 = k3_xboole_0(X2,X3)) ) | ~spl4_173),
% 2.23/0.64    inference(avatar_component_clause,[],[f5907])).
% 2.23/0.64  fof(f5907,plain,(
% 2.23/0.64    spl4_173 <=> ! [X3,X2] : (k1_xboole_0 = k3_xboole_0(X2,X3) | ~r1_xboole_0(k3_xboole_0(X2,X3),X2))),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_173])])).
% 2.23/0.64  fof(f223,plain,(
% 2.23/0.64    k1_xboole_0 != k3_xboole_0(sK0,sK1) | spl4_21),
% 2.23/0.64    inference(avatar_component_clause,[],[f221])).
% 2.23/0.64  fof(f221,plain,(
% 2.23/0.64    spl4_21 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 2.23/0.64  fof(f1818,plain,(
% 2.23/0.64    r1_xboole_0(k3_xboole_0(sK0,sK1),sK0) | (~spl4_2 | ~spl4_45 | ~spl4_73)),
% 2.23/0.64    inference(unit_resulting_resolution,[],[f50,f1804,f544])).
% 2.23/0.64  fof(f544,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X2,X0) | ~r1_xboole_0(X2,X1)) ) | ~spl4_45),
% 2.23/0.64    inference(avatar_component_clause,[],[f543])).
% 2.23/0.64  fof(f543,plain,(
% 2.23/0.64    spl4_45 <=> ! [X1,X0,X2] : (~r1_xboole_0(X2,X1) | r1_xboole_0(X2,X0) | ~r1_tarski(X0,X1))),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 2.23/0.64  fof(f1804,plain,(
% 2.23/0.64    r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | ~spl4_73),
% 2.23/0.64    inference(avatar_component_clause,[],[f1802])).
% 2.23/0.64  fof(f1802,plain,(
% 2.23/0.64    spl4_73 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 2.23/0.64  fof(f50,plain,(
% 2.23/0.64    r1_tarski(sK0,sK2) | ~spl4_2),
% 2.23/0.64    inference(avatar_component_clause,[],[f48])).
% 2.23/0.64  fof(f48,plain,(
% 2.23/0.64    spl4_2 <=> r1_tarski(sK0,sK2)),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.23/0.64  fof(f5909,plain,(
% 2.23/0.64    spl4_173 | ~spl4_40 | ~spl4_48),
% 2.23/0.64    inference(avatar_split_clause,[],[f639,f618,f454,f5907])).
% 2.23/0.64  fof(f454,plain,(
% 2.23/0.64    spl4_40 <=> ! [X3,X4] : (k1_xboole_0 = k3_xboole_0(X4,X3) | ~r1_xboole_0(X3,X4))),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 2.23/0.64  fof(f618,plain,(
% 2.23/0.64    spl4_48 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 2.23/0.64  fof(f639,plain,(
% 2.23/0.64    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(X2,X3) | ~r1_xboole_0(k3_xboole_0(X2,X3),X2)) ) | (~spl4_40 | ~spl4_48)),
% 2.23/0.64    inference(superposition,[],[f619,f455])).
% 2.23/0.64  fof(f455,plain,(
% 2.23/0.64    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(X4,X3) | ~r1_xboole_0(X3,X4)) ) | ~spl4_40),
% 2.23/0.64    inference(avatar_component_clause,[],[f454])).
% 2.23/0.64  fof(f619,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl4_48),
% 2.23/0.64    inference(avatar_component_clause,[],[f618])).
% 2.23/0.64  fof(f1805,plain,(
% 2.23/0.64    spl4_73 | ~spl4_27 | ~spl4_61),
% 2.23/0.64    inference(avatar_split_clause,[],[f1259,f1256,f288,f1802])).
% 2.23/0.64  fof(f288,plain,(
% 2.23/0.64    spl4_27 <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.23/0.64  fof(f1256,plain,(
% 2.23/0.64    spl4_61 <=> ! [X18,X20,X19] : (k1_xboole_0 != k3_xboole_0(X18,k3_xboole_0(X19,X20)) | r1_xboole_0(k3_xboole_0(X18,X19),X20))),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 2.23/0.64  fof(f1259,plain,(
% 2.23/0.64    r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | (~spl4_27 | ~spl4_61)),
% 2.23/0.64    inference(unit_resulting_resolution,[],[f290,f1257])).
% 2.23/0.64  fof(f1257,plain,(
% 2.23/0.64    ( ! [X19,X20,X18] : (k1_xboole_0 != k3_xboole_0(X18,k3_xboole_0(X19,X20)) | r1_xboole_0(k3_xboole_0(X18,X19),X20)) ) | ~spl4_61),
% 2.23/0.64    inference(avatar_component_clause,[],[f1256])).
% 2.23/0.64  fof(f290,plain,(
% 2.23/0.64    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl4_27),
% 2.23/0.64    inference(avatar_component_clause,[],[f288])).
% 2.23/0.64  fof(f1258,plain,(
% 2.23/0.64    spl4_61 | ~spl4_11 | ~spl4_19),
% 2.23/0.64    inference(avatar_split_clause,[],[f204,f174,f87,f1256])).
% 2.23/0.64  fof(f87,plain,(
% 2.23/0.64    spl4_11 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.23/0.64  fof(f174,plain,(
% 2.23/0.64    spl4_19 <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.23/0.64  fof(f204,plain,(
% 2.23/0.64    ( ! [X19,X20,X18] : (k1_xboole_0 != k3_xboole_0(X18,k3_xboole_0(X19,X20)) | r1_xboole_0(k3_xboole_0(X18,X19),X20)) ) | (~spl4_11 | ~spl4_19)),
% 2.23/0.64    inference(superposition,[],[f88,f175])).
% 2.23/0.64  fof(f175,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) ) | ~spl4_19),
% 2.23/0.64    inference(avatar_component_clause,[],[f174])).
% 2.23/0.64  fof(f88,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl4_11),
% 2.23/0.64    inference(avatar_component_clause,[],[f87])).
% 2.23/0.64  fof(f620,plain,(
% 2.23/0.64    spl4_48 | ~spl4_14 | ~spl4_15),
% 2.23/0.64    inference(avatar_split_clause,[],[f159,f109,f105,f618])).
% 2.23/0.64  fof(f105,plain,(
% 2.23/0.64    spl4_14 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.23/0.64  fof(f109,plain,(
% 2.23/0.64    spl4_15 <=> ! [X1,X0] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.23/0.64  fof(f159,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) ) | (~spl4_14 | ~spl4_15)),
% 2.23/0.64    inference(forward_demodulation,[],[f158,f106])).
% 2.23/0.64  fof(f106,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl4_14),
% 2.23/0.64    inference(avatar_component_clause,[],[f105])).
% 2.23/0.64  fof(f158,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) ) | (~spl4_14 | ~spl4_15)),
% 2.23/0.64    inference(superposition,[],[f106,f110])).
% 2.23/0.64  fof(f110,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) ) | ~spl4_15),
% 2.23/0.64    inference(avatar_component_clause,[],[f109])).
% 2.23/0.64  fof(f545,plain,(
% 2.23/0.64    spl4_45 | ~spl4_9 | ~spl4_12),
% 2.23/0.64    inference(avatar_split_clause,[],[f141,f91,f79,f543])).
% 2.23/0.64  fof(f79,plain,(
% 2.23/0.64    spl4_9 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.23/0.64  fof(f91,plain,(
% 2.23/0.64    spl4_12 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1))),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.23/0.64  fof(f141,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (~r1_xboole_0(X2,X1) | r1_xboole_0(X2,X0) | ~r1_tarski(X0,X1)) ) | (~spl4_9 | ~spl4_12)),
% 2.23/0.64    inference(superposition,[],[f92,f80])).
% 2.23/0.64  fof(f80,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) ) | ~spl4_9),
% 2.23/0.64    inference(avatar_component_clause,[],[f79])).
% 2.23/0.64  fof(f92,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) ) | ~spl4_12),
% 2.23/0.64    inference(avatar_component_clause,[],[f91])).
% 2.23/0.64  fof(f456,plain,(
% 2.23/0.64    spl4_40 | ~spl4_7 | ~spl4_10),
% 2.23/0.64    inference(avatar_split_clause,[],[f124,f83,f71,f454])).
% 2.23/0.64  fof(f71,plain,(
% 2.23/0.64    spl4_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.23/0.64  fof(f83,plain,(
% 2.23/0.64    spl4_10 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.23/0.64  fof(f124,plain,(
% 2.23/0.64    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(X4,X3) | ~r1_xboole_0(X3,X4)) ) | (~spl4_7 | ~spl4_10)),
% 2.23/0.64    inference(superposition,[],[f84,f72])).
% 2.23/0.64  fof(f72,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl4_7),
% 2.23/0.64    inference(avatar_component_clause,[],[f71])).
% 2.23/0.64  fof(f84,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl4_10),
% 2.23/0.64    inference(avatar_component_clause,[],[f83])).
% 2.23/0.64  fof(f291,plain,(
% 2.23/0.64    spl4_27 | ~spl4_3 | ~spl4_10),
% 2.23/0.64    inference(avatar_split_clause,[],[f123,f83,f53,f288])).
% 2.23/0.64  fof(f53,plain,(
% 2.23/0.64    spl4_3 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.23/0.64  fof(f123,plain,(
% 2.23/0.64    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | (~spl4_3 | ~spl4_10)),
% 2.23/0.64    inference(unit_resulting_resolution,[],[f55,f84])).
% 2.23/0.64  fof(f55,plain,(
% 2.23/0.64    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl4_3),
% 2.23/0.64    inference(avatar_component_clause,[],[f53])).
% 2.23/0.64  fof(f224,plain,(
% 2.23/0.64    ~spl4_21 | spl4_1 | ~spl4_11),
% 2.23/0.64    inference(avatar_split_clause,[],[f132,f87,f43,f221])).
% 2.23/0.64  fof(f43,plain,(
% 2.23/0.64    spl4_1 <=> r1_xboole_0(sK0,sK1)),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.23/0.64  fof(f132,plain,(
% 2.23/0.64    k1_xboole_0 != k3_xboole_0(sK0,sK1) | (spl4_1 | ~spl4_11)),
% 2.23/0.64    inference(unit_resulting_resolution,[],[f45,f88])).
% 2.23/0.64  fof(f45,plain,(
% 2.23/0.64    ~r1_xboole_0(sK0,sK1) | spl4_1),
% 2.23/0.64    inference(avatar_component_clause,[],[f43])).
% 2.23/0.64  fof(f176,plain,(
% 2.23/0.64    spl4_19),
% 2.23/0.64    inference(avatar_split_clause,[],[f38,f174])).
% 2.23/0.64  fof(f38,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 2.23/0.64    inference(cnf_transformation,[],[f5])).
% 2.23/0.64  fof(f5,axiom,(
% 2.23/0.64    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 2.23/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 2.23/0.64  fof(f111,plain,(
% 2.23/0.64    spl4_15),
% 2.23/0.64    inference(avatar_split_clause,[],[f31,f109])).
% 2.23/0.64  fof(f31,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f8])).
% 2.23/0.64  fof(f8,axiom,(
% 2.23/0.64    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.23/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.23/0.64  fof(f107,plain,(
% 2.23/0.64    spl4_14),
% 2.23/0.64    inference(avatar_split_clause,[],[f30,f105])).
% 2.23/0.64  fof(f30,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.23/0.64    inference(cnf_transformation,[],[f9])).
% 2.23/0.64  fof(f9,axiom,(
% 2.23/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.23/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.23/0.64  fof(f93,plain,(
% 2.23/0.64    spl4_12),
% 2.23/0.64    inference(avatar_split_clause,[],[f40,f91])).
% 2.23/0.64  fof(f40,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f18])).
% 2.23/0.64  fof(f18,plain,(
% 2.23/0.64    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.23/0.64    inference(ennf_transformation,[],[f11])).
% 2.23/0.64  fof(f11,axiom,(
% 2.23/0.64    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.23/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.23/0.64  fof(f89,plain,(
% 2.23/0.64    spl4_11),
% 2.23/0.64    inference(avatar_split_clause,[],[f37,f87])).
% 2.23/0.64  fof(f37,plain,(
% 2.23/0.64    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.23/0.64    inference(cnf_transformation,[],[f23])).
% 2.23/0.64  fof(f23,plain,(
% 2.23/0.64    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.23/0.64    inference(nnf_transformation,[],[f2])).
% 2.23/0.64  fof(f2,axiom,(
% 2.23/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.23/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.23/0.64  fof(f85,plain,(
% 2.23/0.64    spl4_10),
% 2.23/0.64    inference(avatar_split_clause,[],[f36,f83])).
% 2.23/0.64  fof(f36,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f23])).
% 2.23/0.64  fof(f81,plain,(
% 2.23/0.64    spl4_9),
% 2.23/0.64    inference(avatar_split_clause,[],[f35,f79])).
% 2.23/0.64  fof(f35,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f17])).
% 2.23/0.64  fof(f17,plain,(
% 2.23/0.64    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.23/0.64    inference(ennf_transformation,[],[f4])).
% 2.23/0.64  fof(f4,axiom,(
% 2.23/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.23/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.23/0.64  fof(f73,plain,(
% 2.23/0.64    spl4_7),
% 2.23/0.64    inference(avatar_split_clause,[],[f29,f71])).
% 2.23/0.64  fof(f29,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f1])).
% 2.23/0.64  fof(f1,axiom,(
% 2.23/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.23/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.23/0.64  fof(f56,plain,(
% 2.23/0.64    spl4_3),
% 2.23/0.64    inference(avatar_split_clause,[],[f26,f53])).
% 2.23/0.64  fof(f26,plain,(
% 2.23/0.64    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 2.23/0.64    inference(cnf_transformation,[],[f20])).
% 2.23/0.64  fof(f20,plain,(
% 2.23/0.64    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 2.23/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f19])).
% 2.23/0.64  fof(f19,plain,(
% 2.23/0.64    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 2.23/0.64    introduced(choice_axiom,[])).
% 2.23/0.64  fof(f15,plain,(
% 2.23/0.64    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 2.23/0.64    inference(ennf_transformation,[],[f13])).
% 2.23/0.64  fof(f13,negated_conjecture,(
% 2.23/0.64    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 2.23/0.64    inference(negated_conjecture,[],[f12])).
% 2.23/0.64  fof(f12,conjecture,(
% 2.23/0.64    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 2.23/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 2.23/0.64  fof(f51,plain,(
% 2.23/0.64    spl4_2),
% 2.23/0.64    inference(avatar_split_clause,[],[f25,f48])).
% 2.23/0.64  fof(f25,plain,(
% 2.23/0.64    r1_tarski(sK0,sK2)),
% 2.23/0.64    inference(cnf_transformation,[],[f20])).
% 2.23/0.64  fof(f46,plain,(
% 2.23/0.64    ~spl4_1),
% 2.23/0.64    inference(avatar_split_clause,[],[f24,f43])).
% 2.23/0.64  fof(f24,plain,(
% 2.23/0.64    ~r1_xboole_0(sK0,sK1)),
% 2.23/0.64    inference(cnf_transformation,[],[f20])).
% 2.23/0.64  % SZS output end Proof for theBenchmark
% 2.23/0.64  % (21332)------------------------------
% 2.23/0.64  % (21332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.64  % (21332)Termination reason: Refutation
% 2.23/0.64  
% 2.23/0.64  % (21332)Memory used [KB]: 10490
% 2.23/0.64  % (21332)Time elapsed: 0.236 s
% 2.23/0.64  % (21332)------------------------------
% 2.23/0.64  % (21332)------------------------------
% 2.23/0.65  % (21323)Success in time 0.297 s
%------------------------------------------------------------------------------
