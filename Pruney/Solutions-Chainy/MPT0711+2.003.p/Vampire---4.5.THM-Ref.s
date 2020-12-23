%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:41 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 636 expanded)
%              Number of leaves         :   28 ( 236 expanded)
%              Depth                    :   16
%              Number of atoms          :  508 (3185 expanded)
%              Number of equality atoms :  137 (1321 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2462,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f74,f104,f113,f234,f2293,f2304,f2428,f2434,f2454,f2456,f2458,f2461])).

fof(f2461,plain,
    ( ~ spl5_2
    | ~ spl5_5
    | spl5_15 ),
    inference(avatar_contradiction_clause,[],[f2459])).

fof(f2459,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_5
    | spl5_15 ),
    inference(resolution,[],[f2453,f118])).

fof(f118,plain,
    ( ! [X2] : r1_tarski(k1_relat_1(k7_relat_1(sK0,X2)),k1_relat_1(sK0))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(superposition,[],[f71,f112])).

fof(f112,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_5
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f71,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_2
  <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2453,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f2451])).

fof(f2451,plain,
    ( spl5_15
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f2458,plain,(
    spl5_14 ),
    inference(avatar_contradiction_clause,[],[f2457])).

fof(f2457,plain,
    ( $false
    | spl5_14 ),
    inference(resolution,[],[f2449,f39])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    & ! [X3] :
        ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
        | ~ r2_hidden(X3,sK2) )
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
              & ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(sK0,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(sK0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
            & ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(sK0,X3)
                | ~ r2_hidden(X3,X2) )
            & k1_relat_1(X1) = k1_relat_1(sK0) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
          & ! [X3] :
              ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
              | ~ r2_hidden(X3,X2) )
          & k1_relat_1(sK0) = k1_relat_1(sK1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
        & ! [X3] :
            ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
            | ~ r2_hidden(X3,X2) )
        & k1_relat_1(sK0) = k1_relat_1(sK1) )
   => ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
      & ! [X3] :
          ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
          | ~ r2_hidden(X3,sK2) )
      & k1_relat_1(sK0) = k1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                  & k1_relat_1(X1) = k1_relat_1(X0) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_1)).

fof(f2449,plain,
    ( ~ v1_funct_1(sK1)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f2447])).

fof(f2447,plain,
    ( spl5_14
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f2456,plain,(
    spl5_13 ),
    inference(avatar_contradiction_clause,[],[f2455])).

fof(f2455,plain,
    ( $false
    | spl5_13 ),
    inference(resolution,[],[f2445,f37])).

fof(f37,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f2445,plain,
    ( ~ v1_funct_1(sK0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f2443])).

fof(f2443,plain,
    ( spl5_13
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f2454,plain,
    ( ~ spl5_3
    | ~ spl5_13
    | ~ spl5_1
    | ~ spl5_14
    | spl5_12
    | ~ spl5_15
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f2441,f2421,f2451,f2425,f2447,f66,f2443,f96])).

fof(f96,plain,
    ( spl5_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f66,plain,
    ( spl5_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2425,plain,
    ( spl5_12
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f2421,plain,
    ( spl5_11
  <=> k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f2441,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_11 ),
    inference(duplicate_literal_removal,[],[f2440])).

fof(f2440,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f2439,f40])).

fof(f40,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f2439,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f2438,f468])).

fof(f468,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) ),
    inference(forward_demodulation,[],[f467,f240])).

fof(f240,plain,(
    ! [X6] : k1_relat_1(k7_relat_1(sK0,X6)) = k1_relat_1(k7_relat_1(sK4(X6),k1_relat_1(sK0))) ),
    inference(superposition,[],[f207,f208])).

fof(f208,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(sK0))) ),
    inference(superposition,[],[f203,f61])).

fof(f61,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(definition_unfolding,[],[f51,f60,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f203,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),X0)) ),
    inference(resolution,[],[f62,f36])).

fof(f36,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f55,f60])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f207,plain,(
    ! [X2,X3] : k1_setfam_1(k1_enumset1(X2,X2,X3)) = k1_relat_1(k7_relat_1(sK4(X2),X3)) ),
    inference(forward_demodulation,[],[f205,f49])).

fof(f49,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = k1_xboole_0
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK4(X0)) = X0
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k1_xboole_0
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = k1_xboole_0 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f205,plain,(
    ! [X2,X3] : k1_relat_1(k7_relat_1(sK4(X2),X3)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK4(X2)),k1_relat_1(sK4(X2)),X3)) ),
    inference(resolution,[],[f62,f47])).

fof(f47,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f467,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK4(X0),k1_relat_1(sK0)))) ),
    inference(forward_demodulation,[],[f464,f49])).

fof(f464,plain,(
    ! [X0] : k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK4(X0),k1_relat_1(sK0)))) = k7_relat_1(sK0,k1_relat_1(sK4(X0))) ),
    inference(resolution,[],[f457,f47])).

fof(f457,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(sK0,k1_relat_1(X0)) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK0)))) ) ),
    inference(resolution,[],[f43,f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

fof(f2438,plain,
    ( k7_relat_1(sK1,sK2) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f2437,f492])).

fof(f492,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) ),
    inference(forward_demodulation,[],[f491,f49])).

fof(f491,plain,(
    ! [X0] : k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK1,k1_relat_1(sK4(X0))) ),
    inference(forward_demodulation,[],[f488,f240])).

fof(f488,plain,(
    ! [X0] : k7_relat_1(sK1,k1_relat_1(sK4(X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK4(X0),k1_relat_1(sK0)))) ),
    inference(resolution,[],[f460,f47])).

fof(f460,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(sK1,k1_relat_1(X1)) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0)))) ) ),
    inference(forward_demodulation,[],[f458,f40])).

fof(f458,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(sK1,k1_relat_1(X1)) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK1)))) ) ),
    inference(resolution,[],[f43,f38])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f2437,plain,
    ( k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_11 ),
    inference(trivial_inequality_removal,[],[f2436])).

fof(f2436,plain,
    ( k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) != k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))))
    | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_11 ),
    inference(superposition,[],[f46,f2423])).

fof(f2423,plain,
    ( k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f2421])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
      | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
                    & r2_hidden(sK3(X0,X1,X2),X2) ) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) ) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) ) )
                & ( ! [X3] :
                      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                      | ~ r2_hidden(X3,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( r1_tarski(X2,k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) )
             => ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_1)).

fof(f2434,plain,(
    ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f2433])).

fof(f2433,plain,
    ( $false
    | ~ spl5_12 ),
    inference(trivial_inequality_removal,[],[f2429])).

fof(f2429,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK0,sK2)
    | ~ spl5_12 ),
    inference(superposition,[],[f42,f2427])).

fof(f2427,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f2425])).

fof(f42,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f2428,plain,
    ( spl5_11
    | spl5_12
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f2365,f2302,f232,f111,f70,f2425,f2421])).

fof(f232,plain,
    ( spl5_8
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X3,k1_relat_1(k7_relat_1(sK0,X2)))
        | r2_hidden(X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f2302,plain,
    ( spl5_10
  <=> ! [X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(sK0,sK1,X1),X1)
        | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f2365,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))))
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(resolution,[],[f2341,f41])).

fof(f41,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2341,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),X0)
        | k7_relat_1(sK1,X0) = k7_relat_1(sK0,X0) )
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(resolution,[],[f2316,f233])).

fof(f233,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k1_relat_1(k7_relat_1(sK0,X2)))
        | r2_hidden(X3,X2) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f232])).

fof(f2316,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X1))),k1_relat_1(k7_relat_1(sK0,X1)))
        | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1) )
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f2315,f468])).

fof(f2315,plain,
    ( ! [X1] :
        ( k7_relat_1(sK1,X1) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X1)))
        | r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X1))),k1_relat_1(k7_relat_1(sK0,X1))) )
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f2306,f492])).

fof(f2306,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X1))),k1_relat_1(k7_relat_1(sK0,X1)))
        | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X1))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X1))) )
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_10 ),
    inference(resolution,[],[f2303,f118])).

fof(f2303,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(sK0,sK1,X1),X1)
        | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f2302])).

fof(f2304,plain,
    ( ~ spl5_1
    | spl5_10
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f2299,f2291,f2302,f66])).

fof(f2291,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(sK0,X0,X1),X1)
        | k7_relat_1(X0,X1) = k7_relat_1(sK0,X1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | ~ r1_tarski(X1,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f2299,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK0))
        | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1)
        | ~ v1_relat_1(sK1)
        | r2_hidden(sK3(sK0,sK1,X1),X1) )
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f2298])).

fof(f2298,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK0))
        | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1)
        | ~ v1_relat_1(sK1)
        | r2_hidden(sK3(sK0,sK1,X1),X1)
        | ~ r1_tarski(X1,k1_relat_1(sK0)) )
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f2295,f40])).

fof(f2295,plain,
    ( ! [X1] :
        ( k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1)
        | ~ v1_relat_1(sK1)
        | r2_hidden(sK3(sK0,sK1,X1),X1)
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | ~ r1_tarski(X1,k1_relat_1(sK1)) )
    | ~ spl5_9 ),
    inference(resolution,[],[f2292,f39])).

fof(f2292,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | k7_relat_1(X0,X1) = k7_relat_1(sK0,X1)
        | ~ v1_relat_1(X0)
        | r2_hidden(sK3(sK0,X0,X1),X1)
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | ~ r1_tarski(X1,k1_relat_1(X0)) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f2291])).

fof(f2293,plain,
    ( ~ spl5_3
    | spl5_9 ),
    inference(avatar_split_clause,[],[f942,f2291,f96])).

fof(f942,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK0,X0,X1),X1)
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ r1_tarski(X1,k1_relat_1(sK0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k7_relat_1(sK0,X1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f45,f37])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f234,plain,
    ( ~ spl5_1
    | spl5_8 ),
    inference(avatar_split_clause,[],[f227,f232,f66])).

fof(f227,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(k7_relat_1(sK0,X2)))
      | r2_hidden(X3,X2)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f57,f216])).

fof(f216,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k1_relat_1(k7_relat_1(sK0,X1)) ),
    inference(forward_demodulation,[],[f206,f203])).

fof(f206,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),X1)) ),
    inference(forward_demodulation,[],[f204,f40])).

fof(f204,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X1)) ),
    inference(resolution,[],[f62,f38])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f113,plain,
    ( ~ spl5_3
    | spl5_5 ),
    inference(avatar_split_clause,[],[f83,f111,f96])).

fof(f83,plain,(
    ! [X0] :
      ( k1_relat_1(k7_relat_1(sK0,X0)) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f78,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

fof(f78,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK0))
      | k1_relat_1(k7_relat_1(sK1,X1)) = X1 ) ),
    inference(forward_demodulation,[],[f76,f40])).

fof(f76,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK1))
      | k1_relat_1(k7_relat_1(sK1,X1)) = X1 ) ),
    inference(resolution,[],[f56,f38])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f104,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl5_3 ),
    inference(resolution,[],[f98,f36])).

fof(f98,plain,
    ( ~ v1_relat_1(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f74,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f68,f38])).

fof(f68,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f72,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f63,f70,f66])).

fof(f63,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK0))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f54,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (30380)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.44  % (30372)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (30384)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (30369)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (30379)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (30371)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (30376)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (30382)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (30368)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (30367)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (30375)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (30378)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (30381)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (30377)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (30370)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (30373)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (30385)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (30383)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.54/0.56  % (30369)Refutation found. Thanks to Tanya!
% 1.54/0.56  % SZS status Theorem for theBenchmark
% 1.54/0.56  % SZS output start Proof for theBenchmark
% 1.54/0.56  fof(f2462,plain,(
% 1.54/0.56    $false),
% 1.54/0.56    inference(avatar_sat_refutation,[],[f72,f74,f104,f113,f234,f2293,f2304,f2428,f2434,f2454,f2456,f2458,f2461])).
% 1.54/0.56  fof(f2461,plain,(
% 1.54/0.56    ~spl5_2 | ~spl5_5 | spl5_15),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f2459])).
% 1.54/0.56  fof(f2459,plain,(
% 1.54/0.56    $false | (~spl5_2 | ~spl5_5 | spl5_15)),
% 1.54/0.56    inference(resolution,[],[f2453,f118])).
% 1.54/0.56  fof(f118,plain,(
% 1.54/0.56    ( ! [X2] : (r1_tarski(k1_relat_1(k7_relat_1(sK0,X2)),k1_relat_1(sK0))) ) | (~spl5_2 | ~spl5_5)),
% 1.54/0.56    inference(superposition,[],[f71,f112])).
% 1.54/0.56  fof(f112,plain,(
% 1.54/0.56    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))))) ) | ~spl5_5),
% 1.54/0.56    inference(avatar_component_clause,[],[f111])).
% 1.54/0.56  fof(f111,plain,(
% 1.54/0.56    spl5_5 <=> ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.54/0.56  fof(f71,plain,(
% 1.54/0.56    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK0))) ) | ~spl5_2),
% 1.54/0.56    inference(avatar_component_clause,[],[f70])).
% 1.54/0.56  fof(f70,plain,(
% 1.54/0.56    spl5_2 <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK0))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.54/0.56  fof(f2453,plain,(
% 1.54/0.56    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | spl5_15),
% 1.54/0.56    inference(avatar_component_clause,[],[f2451])).
% 1.54/0.56  fof(f2451,plain,(
% 1.54/0.56    spl5_15 <=> r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.54/0.56  fof(f2458,plain,(
% 1.54/0.56    spl5_14),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f2457])).
% 1.54/0.56  fof(f2457,plain,(
% 1.54/0.56    $false | spl5_14),
% 1.54/0.56    inference(resolution,[],[f2449,f39])).
% 1.54/0.56  fof(f39,plain,(
% 1.54/0.56    v1_funct_1(sK1)),
% 1.54/0.56    inference(cnf_transformation,[],[f27])).
% 1.54/0.56  fof(f27,plain,(
% 1.54/0.56    ((k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.54/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26,f25,f24])).
% 1.54/0.56  fof(f24,plain,(
% 1.54/0.56    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f25,plain,(
% 1.54/0.56    ? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f26,plain,(
% 1.54/0.56    ? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) => (k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f14,plain,(
% 1.54/0.56    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.54/0.56    inference(flattening,[],[f13])).
% 1.54/0.56  fof(f13,plain,(
% 1.54/0.56    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.54/0.56    inference(ennf_transformation,[],[f12])).
% 1.54/0.56  fof(f12,negated_conjecture,(
% 1.54/0.56    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 1.54/0.56    inference(negated_conjecture,[],[f11])).
% 1.54/0.56  fof(f11,conjecture,(
% 1.54/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_1)).
% 1.54/0.56  fof(f2449,plain,(
% 1.54/0.56    ~v1_funct_1(sK1) | spl5_14),
% 1.54/0.56    inference(avatar_component_clause,[],[f2447])).
% 1.54/0.56  fof(f2447,plain,(
% 1.54/0.56    spl5_14 <=> v1_funct_1(sK1)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.54/0.56  fof(f2456,plain,(
% 1.54/0.56    spl5_13),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f2455])).
% 1.54/0.56  fof(f2455,plain,(
% 1.54/0.56    $false | spl5_13),
% 1.54/0.56    inference(resolution,[],[f2445,f37])).
% 1.54/0.56  fof(f37,plain,(
% 1.54/0.56    v1_funct_1(sK0)),
% 1.54/0.56    inference(cnf_transformation,[],[f27])).
% 1.54/0.56  fof(f2445,plain,(
% 1.54/0.56    ~v1_funct_1(sK0) | spl5_13),
% 1.54/0.56    inference(avatar_component_clause,[],[f2443])).
% 1.54/0.56  fof(f2443,plain,(
% 1.54/0.56    spl5_13 <=> v1_funct_1(sK0)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.54/0.56  fof(f2454,plain,(
% 1.54/0.56    ~spl5_3 | ~spl5_13 | ~spl5_1 | ~spl5_14 | spl5_12 | ~spl5_15 | ~spl5_11),
% 1.54/0.56    inference(avatar_split_clause,[],[f2441,f2421,f2451,f2425,f2447,f66,f2443,f96])).
% 1.54/0.56  fof(f96,plain,(
% 1.54/0.56    spl5_3 <=> v1_relat_1(sK0)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.54/0.56  fof(f66,plain,(
% 1.54/0.56    spl5_1 <=> v1_relat_1(sK1)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.54/0.56  fof(f2425,plain,(
% 1.54/0.56    spl5_12 <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.54/0.56  fof(f2421,plain,(
% 1.54/0.56    spl5_11 <=> k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2))))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.54/0.56  fof(f2441,plain,(
% 1.54/0.56    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl5_11),
% 1.54/0.56    inference(duplicate_literal_removal,[],[f2440])).
% 1.54/0.56  fof(f2440,plain,(
% 1.54/0.56    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl5_11),
% 1.54/0.56    inference(forward_demodulation,[],[f2439,f40])).
% 1.54/0.56  fof(f40,plain,(
% 1.54/0.56    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 1.54/0.56    inference(cnf_transformation,[],[f27])).
% 1.54/0.56  fof(f2439,plain,(
% 1.54/0.56    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl5_11),
% 1.54/0.56    inference(forward_demodulation,[],[f2438,f468])).
% 1.54/0.56  fof(f468,plain,(
% 1.54/0.56    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))) )),
% 1.54/0.56    inference(forward_demodulation,[],[f467,f240])).
% 1.54/0.56  fof(f240,plain,(
% 1.54/0.56    ( ! [X6] : (k1_relat_1(k7_relat_1(sK0,X6)) = k1_relat_1(k7_relat_1(sK4(X6),k1_relat_1(sK0)))) )),
% 1.54/0.56    inference(superposition,[],[f207,f208])).
% 1.54/0.56  fof(f208,plain,(
% 1.54/0.56    ( ! [X1] : (k1_relat_1(k7_relat_1(sK0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(sK0)))) )),
% 1.54/0.56    inference(superposition,[],[f203,f61])).
% 1.54/0.56  fof(f61,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f51,f60,f60])).
% 1.54/0.56  fof(f60,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f52,f53])).
% 1.54/0.56  fof(f53,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f2])).
% 1.54/0.56  fof(f2,axiom,(
% 1.54/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.54/0.56  fof(f52,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f3])).
% 1.54/0.56  fof(f3,axiom,(
% 1.54/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.54/0.56  fof(f51,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f1])).
% 1.54/0.56  fof(f1,axiom,(
% 1.54/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.54/0.56  fof(f203,plain,(
% 1.54/0.56    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),X0))) )),
% 1.54/0.56    inference(resolution,[],[f62,f36])).
% 1.54/0.56  fof(f36,plain,(
% 1.54/0.56    v1_relat_1(sK0)),
% 1.54/0.56    inference(cnf_transformation,[],[f27])).
% 1.54/0.56  fof(f62,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f55,f60])).
% 1.54/0.56  fof(f55,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f20])).
% 1.54/0.56  fof(f20,plain,(
% 1.54/0.56    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f7])).
% 1.54/0.56  fof(f7,axiom,(
% 1.54/0.56    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.54/0.56  fof(f207,plain,(
% 1.54/0.56    ( ! [X2,X3] : (k1_setfam_1(k1_enumset1(X2,X2,X3)) = k1_relat_1(k7_relat_1(sK4(X2),X3))) )),
% 1.54/0.56    inference(forward_demodulation,[],[f205,f49])).
% 1.54/0.56  fof(f49,plain,(
% 1.54/0.56    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f33])).
% 1.54/0.56  fof(f33,plain,(
% 1.54/0.56    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 1.54/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f32])).
% 1.54/0.56  fof(f32,plain,(
% 1.54/0.56    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = k1_xboole_0 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f18,plain,(
% 1.54/0.56    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = k1_xboole_0 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f9])).
% 1.54/0.56  fof(f9,axiom,(
% 1.54/0.56    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = k1_xboole_0) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.54/0.56  fof(f205,plain,(
% 1.54/0.56    ( ! [X2,X3] : (k1_relat_1(k7_relat_1(sK4(X2),X3)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK4(X2)),k1_relat_1(sK4(X2)),X3))) )),
% 1.54/0.56    inference(resolution,[],[f62,f47])).
% 1.54/0.56  fof(f47,plain,(
% 1.54/0.56    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f33])).
% 1.54/0.56  fof(f467,plain,(
% 1.54/0.56    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK4(X0),k1_relat_1(sK0))))) )),
% 1.54/0.56    inference(forward_demodulation,[],[f464,f49])).
% 1.54/0.56  fof(f464,plain,(
% 1.54/0.56    ( ! [X0] : (k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK4(X0),k1_relat_1(sK0)))) = k7_relat_1(sK0,k1_relat_1(sK4(X0)))) )),
% 1.54/0.56    inference(resolution,[],[f457,f47])).
% 1.54/0.56  fof(f457,plain,(
% 1.54/0.56    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(sK0,k1_relat_1(X0)) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK0))))) )),
% 1.54/0.56    inference(resolution,[],[f43,f36])).
% 1.54/0.56  fof(f43,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f15])).
% 1.54/0.56  fof(f15,plain,(
% 1.54/0.56    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.54/0.56    inference(ennf_transformation,[],[f4])).
% 1.54/0.56  fof(f4,axiom,(
% 1.54/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).
% 1.54/0.56  fof(f2438,plain,(
% 1.54/0.56    k7_relat_1(sK1,sK2) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl5_11),
% 1.54/0.56    inference(forward_demodulation,[],[f2437,f492])).
% 1.54/0.56  fof(f492,plain,(
% 1.54/0.56    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))) )),
% 1.54/0.56    inference(forward_demodulation,[],[f491,f49])).
% 1.54/0.56  fof(f491,plain,(
% 1.54/0.56    ( ! [X0] : (k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK1,k1_relat_1(sK4(X0)))) )),
% 1.54/0.56    inference(forward_demodulation,[],[f488,f240])).
% 1.54/0.56  fof(f488,plain,(
% 1.54/0.56    ( ! [X0] : (k7_relat_1(sK1,k1_relat_1(sK4(X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK4(X0),k1_relat_1(sK0))))) )),
% 1.54/0.56    inference(resolution,[],[f460,f47])).
% 1.54/0.56  fof(f460,plain,(
% 1.54/0.56    ( ! [X1] : (~v1_relat_1(X1) | k7_relat_1(sK1,k1_relat_1(X1)) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0))))) )),
% 1.54/0.56    inference(forward_demodulation,[],[f458,f40])).
% 1.54/0.56  fof(f458,plain,(
% 1.54/0.56    ( ! [X1] : (~v1_relat_1(X1) | k7_relat_1(sK1,k1_relat_1(X1)) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK1))))) )),
% 1.54/0.56    inference(resolution,[],[f43,f38])).
% 1.54/0.56  fof(f38,plain,(
% 1.54/0.56    v1_relat_1(sK1)),
% 1.54/0.56    inference(cnf_transformation,[],[f27])).
% 1.54/0.56  fof(f2437,plain,(
% 1.54/0.56    k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl5_11),
% 1.54/0.56    inference(trivial_inequality_removal,[],[f2436])).
% 1.54/0.56  fof(f2436,plain,(
% 1.54/0.56    k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) != k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl5_11),
% 1.54/0.56    inference(superposition,[],[f46,f2423])).
% 1.54/0.56  fof(f2423,plain,(
% 1.54/0.56    k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) | ~spl5_11),
% 1.54/0.56    inference(avatar_component_clause,[],[f2421])).
% 1.54/0.56  fof(f46,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f31])).
% 1.54/0.56  fof(f31,plain,(
% 1.54/0.56    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 1.54/0.56  fof(f30,plain,(
% 1.54/0.56    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2)))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f29,plain,(
% 1.54/0.56    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.56    inference(rectify,[],[f28])).
% 1.54/0.56  fof(f28,plain,(
% 1.54/0.56    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.56    inference(nnf_transformation,[],[f17])).
% 1.54/0.56  fof(f17,plain,(
% 1.54/0.56    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.56    inference(flattening,[],[f16])).
% 1.54/0.56  fof(f16,plain,(
% 1.54/0.56    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | (~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.56    inference(ennf_transformation,[],[f10])).
% 1.54/0.56  fof(f10,axiom,(
% 1.54/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_1)).
% 1.54/0.56  fof(f2434,plain,(
% 1.54/0.56    ~spl5_12),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f2433])).
% 1.54/0.56  fof(f2433,plain,(
% 1.54/0.56    $false | ~spl5_12),
% 1.54/0.56    inference(trivial_inequality_removal,[],[f2429])).
% 1.54/0.56  fof(f2429,plain,(
% 1.54/0.56    k7_relat_1(sK0,sK2) != k7_relat_1(sK0,sK2) | ~spl5_12),
% 1.54/0.56    inference(superposition,[],[f42,f2427])).
% 1.54/0.56  fof(f2427,plain,(
% 1.54/0.56    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~spl5_12),
% 1.54/0.56    inference(avatar_component_clause,[],[f2425])).
% 1.54/0.56  fof(f42,plain,(
% 1.54/0.56    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 1.54/0.56    inference(cnf_transformation,[],[f27])).
% 1.54/0.56  fof(f2428,plain,(
% 1.54/0.56    spl5_11 | spl5_12 | ~spl5_2 | ~spl5_5 | ~spl5_8 | ~spl5_10),
% 1.54/0.56    inference(avatar_split_clause,[],[f2365,f2302,f232,f111,f70,f2425,f2421])).
% 1.54/0.56  fof(f232,plain,(
% 1.54/0.56    spl5_8 <=> ! [X3,X2] : (~r2_hidden(X3,k1_relat_1(k7_relat_1(sK0,X2))) | r2_hidden(X3,X2))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.54/0.56  fof(f2302,plain,(
% 1.54/0.56    spl5_10 <=> ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK0,sK1,X1),X1) | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.54/0.56  fof(f2365,plain,(
% 1.54/0.56    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | k1_funct_1(sK0,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,sK2)))) | (~spl5_2 | ~spl5_5 | ~spl5_8 | ~spl5_10)),
% 1.54/0.56    inference(resolution,[],[f2341,f41])).
% 1.54/0.56  fof(f41,plain,(
% 1.54/0.56    ( ! [X3] : (~r2_hidden(X3,sK2) | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f27])).
% 1.54/0.56  fof(f2341,plain,(
% 1.54/0.56    ( ! [X0] : (r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X0))),X0) | k7_relat_1(sK1,X0) = k7_relat_1(sK0,X0)) ) | (~spl5_2 | ~spl5_5 | ~spl5_8 | ~spl5_10)),
% 1.54/0.56    inference(resolution,[],[f2316,f233])).
% 1.54/0.56  fof(f233,plain,(
% 1.54/0.56    ( ! [X2,X3] : (~r2_hidden(X3,k1_relat_1(k7_relat_1(sK0,X2))) | r2_hidden(X3,X2)) ) | ~spl5_8),
% 1.54/0.56    inference(avatar_component_clause,[],[f232])).
% 1.54/0.56  fof(f2316,plain,(
% 1.54/0.56    ( ! [X1] : (r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X1))),k1_relat_1(k7_relat_1(sK0,X1))) | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1)) ) | (~spl5_2 | ~spl5_5 | ~spl5_10)),
% 1.54/0.56    inference(forward_demodulation,[],[f2315,f468])).
% 1.54/0.56  fof(f2315,plain,(
% 1.54/0.56    ( ! [X1] : (k7_relat_1(sK1,X1) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X1))) | r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X1))),k1_relat_1(k7_relat_1(sK0,X1)))) ) | (~spl5_2 | ~spl5_5 | ~spl5_10)),
% 1.54/0.56    inference(forward_demodulation,[],[f2306,f492])).
% 1.54/0.56  fof(f2306,plain,(
% 1.54/0.56    ( ! [X1] : (r2_hidden(sK3(sK0,sK1,k1_relat_1(k7_relat_1(sK0,X1))),k1_relat_1(k7_relat_1(sK0,X1))) | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X1))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X1)))) ) | (~spl5_2 | ~spl5_5 | ~spl5_10)),
% 1.54/0.56    inference(resolution,[],[f2303,f118])).
% 1.54/0.56  fof(f2303,plain,(
% 1.54/0.56    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK0,sK1,X1),X1) | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1)) ) | ~spl5_10),
% 1.54/0.56    inference(avatar_component_clause,[],[f2302])).
% 1.54/0.56  fof(f2304,plain,(
% 1.54/0.56    ~spl5_1 | spl5_10 | ~spl5_9),
% 1.54/0.56    inference(avatar_split_clause,[],[f2299,f2291,f2302,f66])).
% 1.54/0.56  fof(f2291,plain,(
% 1.54/0.56    spl5_9 <=> ! [X1,X0] : (r2_hidden(sK3(sK0,X0,X1),X1) | k7_relat_1(X0,X1) = k7_relat_1(sK0,X1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(X1,k1_relat_1(sK0)) | ~r1_tarski(X1,k1_relat_1(X0)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.54/0.56  fof(f2299,plain,(
% 1.54/0.56    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1) | ~v1_relat_1(sK1) | r2_hidden(sK3(sK0,sK1,X1),X1)) ) | ~spl5_9),
% 1.54/0.56    inference(duplicate_literal_removal,[],[f2298])).
% 1.54/0.56  fof(f2298,plain,(
% 1.54/0.56    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1) | ~v1_relat_1(sK1) | r2_hidden(sK3(sK0,sK1,X1),X1) | ~r1_tarski(X1,k1_relat_1(sK0))) ) | ~spl5_9),
% 1.54/0.56    inference(forward_demodulation,[],[f2295,f40])).
% 1.54/0.56  fof(f2295,plain,(
% 1.54/0.56    ( ! [X1] : (k7_relat_1(sK1,X1) = k7_relat_1(sK0,X1) | ~v1_relat_1(sK1) | r2_hidden(sK3(sK0,sK1,X1),X1) | ~r1_tarski(X1,k1_relat_1(sK0)) | ~r1_tarski(X1,k1_relat_1(sK1))) ) | ~spl5_9),
% 1.54/0.56    inference(resolution,[],[f2292,f39])).
% 1.54/0.56  fof(f2292,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~v1_funct_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(sK0,X1) | ~v1_relat_1(X0) | r2_hidden(sK3(sK0,X0,X1),X1) | ~r1_tarski(X1,k1_relat_1(sK0)) | ~r1_tarski(X1,k1_relat_1(X0))) ) | ~spl5_9),
% 1.54/0.56    inference(avatar_component_clause,[],[f2291])).
% 1.54/0.56  fof(f2293,plain,(
% 1.54/0.56    ~spl5_3 | spl5_9),
% 1.54/0.56    inference(avatar_split_clause,[],[f942,f2291,f96])).
% 1.54/0.56  fof(f942,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X1) | ~r1_tarski(X1,k1_relat_1(X0)) | ~r1_tarski(X1,k1_relat_1(sK0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(sK0,X1) | ~v1_relat_1(sK0)) )),
% 1.54/0.56    inference(resolution,[],[f45,f37])).
% 1.54/0.56  fof(f45,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK3(X0,X1,X2),X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f31])).
% 1.54/0.56  fof(f234,plain,(
% 1.54/0.56    ~spl5_1 | spl5_8),
% 1.54/0.56    inference(avatar_split_clause,[],[f227,f232,f66])).
% 1.54/0.56  fof(f227,plain,(
% 1.54/0.56    ( ! [X2,X3] : (~r2_hidden(X3,k1_relat_1(k7_relat_1(sK0,X2))) | r2_hidden(X3,X2) | ~v1_relat_1(sK1)) )),
% 1.54/0.56    inference(superposition,[],[f57,f216])).
% 1.54/0.56  fof(f216,plain,(
% 1.54/0.56    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k1_relat_1(k7_relat_1(sK0,X1))) )),
% 1.54/0.56    inference(forward_demodulation,[],[f206,f203])).
% 1.54/0.56  fof(f206,plain,(
% 1.54/0.56    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),X1))) )),
% 1.54/0.56    inference(forward_demodulation,[],[f204,f40])).
% 1.54/0.56  fof(f204,plain,(
% 1.54/0.56    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X1))) )),
% 1.54/0.56    inference(resolution,[],[f62,f38])).
% 1.54/0.56  fof(f57,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f35])).
% 1.54/0.56  fof(f35,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 1.54/0.56    inference(flattening,[],[f34])).
% 1.54/0.56  fof(f34,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 1.54/0.56    inference(nnf_transformation,[],[f23])).
% 1.54/0.56  fof(f23,plain,(
% 1.54/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 1.54/0.56    inference(ennf_transformation,[],[f5])).
% 1.54/0.56  fof(f5,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 1.54/0.56  fof(f113,plain,(
% 1.54/0.56    ~spl5_3 | spl5_5),
% 1.54/0.56    inference(avatar_split_clause,[],[f83,f111,f96])).
% 1.54/0.56  fof(f83,plain,(
% 1.54/0.56    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))) | ~v1_relat_1(sK0)) )),
% 1.54/0.56    inference(resolution,[],[f78,f54])).
% 1.54/0.56  fof(f54,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f19])).
% 1.54/0.56  fof(f19,plain,(
% 1.54/0.56    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f6])).
% 1.54/0.56  fof(f6,axiom,(
% 1.54/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).
% 1.54/0.56  fof(f78,plain,(
% 1.54/0.56    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | k1_relat_1(k7_relat_1(sK1,X1)) = X1) )),
% 1.54/0.56    inference(forward_demodulation,[],[f76,f40])).
% 1.54/0.56  fof(f76,plain,(
% 1.54/0.56    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK1)) | k1_relat_1(k7_relat_1(sK1,X1)) = X1) )),
% 1.54/0.56    inference(resolution,[],[f56,f38])).
% 1.54/0.56  fof(f56,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f22])).
% 1.54/0.56  fof(f22,plain,(
% 1.54/0.56    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.54/0.56    inference(flattening,[],[f21])).
% 1.54/0.56  fof(f21,plain,(
% 1.54/0.56    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f8])).
% 1.54/0.56  fof(f8,axiom,(
% 1.54/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.54/0.56  fof(f104,plain,(
% 1.54/0.56    spl5_3),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f103])).
% 1.54/0.56  fof(f103,plain,(
% 1.54/0.56    $false | spl5_3),
% 1.54/0.56    inference(resolution,[],[f98,f36])).
% 1.54/0.56  fof(f98,plain,(
% 1.54/0.56    ~v1_relat_1(sK0) | spl5_3),
% 1.54/0.56    inference(avatar_component_clause,[],[f96])).
% 1.54/0.56  fof(f74,plain,(
% 1.54/0.56    spl5_1),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f73])).
% 1.54/0.56  fof(f73,plain,(
% 1.54/0.56    $false | spl5_1),
% 1.54/0.56    inference(resolution,[],[f68,f38])).
% 1.54/0.56  fof(f68,plain,(
% 1.54/0.56    ~v1_relat_1(sK1) | spl5_1),
% 1.54/0.56    inference(avatar_component_clause,[],[f66])).
% 1.54/0.56  fof(f72,plain,(
% 1.54/0.56    ~spl5_1 | spl5_2),
% 1.54/0.56    inference(avatar_split_clause,[],[f63,f70,f66])).
% 1.54/0.56  fof(f63,plain,(
% 1.54/0.56    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK0)) | ~v1_relat_1(sK1)) )),
% 1.54/0.56    inference(superposition,[],[f54,f40])).
% 1.54/0.56  % SZS output end Proof for theBenchmark
% 1.54/0.56  % (30369)------------------------------
% 1.54/0.56  % (30369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (30369)Termination reason: Refutation
% 1.54/0.56  
% 1.54/0.56  % (30369)Memory used [KB]: 7419
% 1.54/0.56  % (30369)Time elapsed: 0.138 s
% 1.54/0.56  % (30369)------------------------------
% 1.54/0.56  % (30369)------------------------------
% 1.54/0.56  % (30365)Success in time 0.201 s
%------------------------------------------------------------------------------
