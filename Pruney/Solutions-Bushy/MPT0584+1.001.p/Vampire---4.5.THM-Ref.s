%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0584+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 128 expanded)
%              Number of leaves         :   20 (  61 expanded)
%              Depth                    :    7
%              Number of atoms          :  178 ( 433 expanded)
%              Number of equality atoms :   59 ( 167 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f36,f41,f46,f50,f54,f58,f64,f70,f74,f80,f88,f99])).

fof(f99,plain,
    ( spl4_1
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl4_1
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f96,f25])).

fof(f25,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl4_1
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f96,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(superposition,[],[f86,f63])).

fof(f63,plain,
    ( sK2 = k3_xboole_0(sK2,sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_9
  <=> sK2 = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f86,plain,
    ( ! [X0] : k7_relat_1(sK1,k3_xboole_0(X0,sK3)) = k7_relat_1(sK0,k3_xboole_0(X0,sK3))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_13
  <=> ! [X0] : k7_relat_1(sK1,k3_xboole_0(X0,sK3)) = k7_relat_1(sK0,k3_xboole_0(X0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f88,plain,
    ( spl4_13
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f82,f78,f48,f85])).

fof(f48,plain,
    ( spl4_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f78,plain,
    ( spl4_12
  <=> ! [X0] : k7_relat_1(sK1,k3_xboole_0(sK3,X0)) = k7_relat_1(sK0,k3_xboole_0(sK3,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f82,plain,
    ( ! [X1] : k7_relat_1(sK1,k3_xboole_0(X1,sK3)) = k7_relat_1(sK0,k3_xboole_0(X1,sK3))
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(superposition,[],[f79,f49])).

fof(f49,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f79,plain,
    ( ! [X0] : k7_relat_1(sK1,k3_xboole_0(sK3,X0)) = k7_relat_1(sK0,k3_xboole_0(sK3,X0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,
    ( spl4_12
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f76,f72,f68,f28,f78])).

fof(f28,plain,
    ( spl4_2
  <=> k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f68,plain,
    ( spl4_10
  <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f72,plain,
    ( spl4_11
  <=> ! [X3,X2] : k7_relat_1(k7_relat_1(sK0,X2),X3) = k7_relat_1(sK0,k3_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f76,plain,
    ( ! [X0] : k7_relat_1(sK1,k3_xboole_0(sK3,X0)) = k7_relat_1(sK0,k3_xboole_0(sK3,X0))
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f75,f73])).

fof(f73,plain,
    ( ! [X2,X3] : k7_relat_1(k7_relat_1(sK0,X2),X3) = k7_relat_1(sK0,k3_xboole_0(X2,X3))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f75,plain,
    ( ! [X0] : k7_relat_1(sK1,k3_xboole_0(sK3,X0)) = k7_relat_1(k7_relat_1(sK0,sK3),X0)
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(superposition,[],[f69,f30])).

fof(f30,plain,
    ( k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f69,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k3_xboole_0(X0,X1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f74,plain,
    ( spl4_11
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f66,f56,f43,f72])).

fof(f43,plain,
    ( spl4_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f56,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f66,plain,
    ( ! [X2,X3] : k7_relat_1(k7_relat_1(sK0,X2),X3) = k7_relat_1(sK0,k3_xboole_0(X2,X3))
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(resolution,[],[f57,f45])).

fof(f45,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f57,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f70,plain,
    ( spl4_10
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f65,f56,f38,f68])).

fof(f38,plain,
    ( spl4_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f65,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k3_xboole_0(X0,X1))
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(resolution,[],[f57,f40])).

fof(f40,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f64,plain,
    ( spl4_9
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f59,f52,f33,f61])).

fof(f33,plain,
    ( spl4_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f52,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f59,plain,
    ( sK2 = k3_xboole_0(sK2,sK3)
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f53,f35])).

fof(f35,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f58,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f21,f56])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f54,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f50,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f19,f48])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f46,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f14,f43])).

fof(f14,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f12,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & r1_tarski(X2,X3) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
              & k7_relat_1(X1,X3) = k7_relat_1(sK0,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
            & k7_relat_1(X1,X3) = k7_relat_1(sK0,X3)
            & r1_tarski(X2,X3) )
        & v1_relat_1(X1) )
   => ( ? [X3,X2] :
          ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
          & k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
          & r1_tarski(X2,X3) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X3,X2] :
        ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
        & k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
        & r1_tarski(X2,X3) )
   => ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
      & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2,X3] :
                ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                  & r1_tarski(X2,X3) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2,X3] :
              ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & r1_tarski(X2,X3) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t188_relat_1)).

fof(f41,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f15,f38])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f17,f28])).

fof(f17,plain,(
    k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f26,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f18,f23])).

fof(f18,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
