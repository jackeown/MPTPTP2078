%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:52 EST 2020

% Result     : Theorem 2.67s
% Output     : Refutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 679 expanded)
%              Number of leaves         :   40 ( 210 expanded)
%              Depth                    :   17
%              Number of atoms          :  585 (1768 expanded)
%              Number of equality atoms :  148 ( 787 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3759,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f195,f200,f428,f431,f2294,f2398,f2879,f2884,f3595,f3641,f3734])).

fof(f3734,plain,
    ( ~ spl12_10
    | ~ spl12_96 ),
    inference(avatar_contradiction_clause,[],[f3733])).

fof(f3733,plain,
    ( $false
    | ~ spl12_10
    | ~ spl12_96 ),
    inference(subsumption_resolution,[],[f2803,f494])).

fof(f494,plain,
    ( ! [X1] : ~ sP0(X1,sK6)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f493])).

fof(f493,plain,
    ( spl12_10
  <=> ! [X1] : ~ sP0(X1,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f2803,plain,
    ( sP0(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),sK6)
    | ~ spl12_96 ),
    inference(subsumption_resolution,[],[f2799,f183])).

fof(f183,plain,(
    k1_xboole_0 != k2_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f182,f66])).

fof(f66,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k2_relat_1(sK6) != k1_tarski(k1_funct_1(sK6,sK5))
    & k1_tarski(sK5) = k1_relat_1(sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f22,f40])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK6) != k1_tarski(k1_funct_1(sK6,sK5))
      & k1_tarski(sK5) = k1_relat_1(sK6)
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f182,plain,
    ( k1_xboole_0 != k2_relat_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f175,f70])).

fof(f70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f175,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(superposition,[],[f146,f79])).

fof(f79,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f146,plain,(
    ~ v1_xboole_0(k1_relat_1(sK6)) ),
    inference(superposition,[],[f117,f116])).

fof(f116,plain,(
    k1_relat_1(sK6) = k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(definition_unfolding,[],[f68,f114])).

fof(f114,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f72,f113])).

fof(f113,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f90,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f96,f111])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f104,f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f108,f109])).

fof(f109,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f108,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f104,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f96,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f90,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f72,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f68,plain,(
    k1_tarski(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f117,plain,(
    ! [X0] : ~ v1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f71,f114])).

fof(f71,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f2799,plain,
    ( sP0(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),sK6)
    | k1_xboole_0 = k2_relat_1(sK6)
    | ~ spl12_96 ),
    inference(trivial_inequality_removal,[],[f2794])).

fof(f2794,plain,
    ( sP0(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),sK6)
    | k1_xboole_0 = k2_relat_1(sK6)
    | k2_relat_1(sK6) != k2_relat_1(sK6)
    | ~ spl12_96 ),
    inference(resolution,[],[f2311,f563])).

fof(f563,plain,(
    ! [X20] :
      ( r2_hidden(sK10(X20,k1_funct_1(sK6,sK5)),X20)
      | k1_xboole_0 = X20
      | k2_relat_1(sK6) != X20 ) ),
    inference(superposition,[],[f115,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK10(X0,X1),X0) ) ),
    inference(definition_unfolding,[],[f94,f114])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( sK10(X0,X1) != X1
        & r2_hidden(sK10(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f31,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK10(X0,X1) != X1
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f115,plain,(
    k2_relat_1(sK6) != k5_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) ),
    inference(definition_unfolding,[],[f69,f114])).

fof(f69,plain,(
    k2_relat_1(sK6) != k1_tarski(k1_funct_1(sK6,sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f2311,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(sK6))
        | sP0(X2,sK6) )
    | ~ spl12_96 ),
    inference(resolution,[],[f2254,f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( ~ sP1(X0,X1)
      | ~ r2_hidden(X3,X1)
      | sP0(X3,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(sK7(X0,X1),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sP0(sK7(X0,X1),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f45,f46])).

% (1836)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(sK7(X0,X1),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sP0(sK7(X0,X1),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP0(X2,X0) )
            & ( sP0(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2254,plain,
    ( sP1(sK6,k2_relat_1(sK6))
    | ~ spl12_96 ),
    inference(avatar_component_clause,[],[f2253])).

fof(f2253,plain,
    ( spl12_96
  <=> sP1(sK6,k2_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_96])])).

fof(f3641,plain,
    ( ~ spl12_7
    | ~ spl12_2
    | ~ spl12_101 ),
    inference(avatar_split_clause,[],[f2400,f2384,f193,f456])).

fof(f456,plain,
    ( spl12_7
  <=> k1_xboole_0 = k1_relat_1(k4_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f193,plain,
    ( spl12_2
  <=> ! [X0] :
        ( k1_xboole_0 != X0
        | ~ sP1(sK6,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f2384,plain,
    ( spl12_101
  <=> sP1(sK6,k1_relat_1(k4_relat_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_101])])).

fof(f2400,plain,
    ( k1_xboole_0 != k1_relat_1(k4_relat_1(sK6))
    | ~ spl12_2
    | ~ spl12_101 ),
    inference(resolution,[],[f2385,f194])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ sP1(sK6,X0)
        | k1_xboole_0 != X0 )
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f193])).

fof(f2385,plain,
    ( sP1(sK6,k1_relat_1(k4_relat_1(sK6)))
    | ~ spl12_101 ),
    inference(avatar_component_clause,[],[f2384])).

fof(f3595,plain,
    ( spl12_10
    | ~ spl12_4
    | ~ spl12_116 ),
    inference(avatar_split_clause,[],[f3594,f2876,f426,f493])).

fof(f426,plain,
    ( spl12_4
  <=> ! [X0] :
        ( sK5 = X0
        | ~ r2_hidden(X0,k2_relat_1(k4_relat_1(sK6))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f2876,plain,
    ( spl12_116
  <=> sP0(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_116])])).

fof(f3594,plain,
    ( ! [X4] : ~ sP0(X4,sK6)
    | ~ spl12_4
    | ~ spl12_116 ),
    inference(subsumption_resolution,[],[f3593,f491])).

fof(f491,plain,
    ( ! [X0] :
        ( k1_funct_1(sK6,sK5) = X0
        | ~ sP0(X0,sK6) )
    | ~ spl12_4 ),
    inference(duplicate_literal_removal,[],[f488])).

fof(f488,plain,
    ( ! [X0] :
        ( k1_funct_1(sK6,sK5) = X0
        | ~ sP0(X0,sK6)
        | ~ sP0(X0,sK6) )
    | ~ spl12_4 ),
    inference(superposition,[],[f87,f483])).

fof(f483,plain,
    ( ! [X4] :
        ( sK5 = sK8(X4,sK6)
        | ~ sP0(X4,sK6) )
    | ~ spl12_4 ),
    inference(resolution,[],[f453,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),k1_relat_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK8(X0,X1)) = X0
          & r2_hidden(sK8(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK8(X0,X1)) = X0
        & r2_hidden(sK8(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ( sP0(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( sP0(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f453,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK6))
        | sK5 = X0 )
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f441,f66])).

fof(f441,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK6))
        | sK5 = X0
        | ~ v1_relat_1(sK6) )
    | ~ spl12_4 ),
    inference(superposition,[],[f427,f77])).

fof(f77,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f427,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(k4_relat_1(sK6)))
        | sK5 = X0 )
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f426])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK8(X0,X1)) = X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f3593,plain,
    ( ! [X4] :
        ( k1_funct_1(sK6,sK5) != X4
        | ~ sP0(X4,sK6) )
    | ~ spl12_4
    | ~ spl12_116 ),
    inference(subsumption_resolution,[],[f3590,f183])).

fof(f3590,plain,
    ( ! [X4] :
        ( k1_funct_1(sK6,sK5) != X4
        | k1_xboole_0 = k2_relat_1(sK6)
        | ~ sP0(X4,sK6) )
    | ~ spl12_4
    | ~ spl12_116 ),
    inference(trivial_inequality_removal,[],[f3583])).

fof(f3583,plain,
    ( ! [X4] :
        ( k1_funct_1(sK6,sK5) != X4
        | k1_xboole_0 = k2_relat_1(sK6)
        | k2_relat_1(sK6) != k2_relat_1(sK6)
        | ~ sP0(X4,sK6) )
    | ~ spl12_4
    | ~ spl12_116 ),
    inference(superposition,[],[f521,f2941])).

fof(f2941,plain,
    ( ! [X0] :
        ( sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) = X0
        | ~ sP0(X0,sK6) )
    | ~ spl12_4
    | ~ spl12_116 ),
    inference(resolution,[],[f2878,f839])).

fof(f839,plain,
    ( ! [X0,X1] :
        ( ~ sP0(X1,sK6)
        | X0 = X1
        | ~ sP0(X0,sK6) )
    | ~ spl12_4 ),
    inference(superposition,[],[f491,f491])).

fof(f2878,plain,
    ( sP0(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),sK6)
    | ~ spl12_116 ),
    inference(avatar_component_clause,[],[f2876])).

fof(f521,plain,(
    ! [X17] :
      ( k1_funct_1(sK6,sK5) != sK10(X17,k1_funct_1(sK6,sK5))
      | k1_xboole_0 = X17
      | k2_relat_1(sK6) != X17 ) ),
    inference(superposition,[],[f115,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | sK10(X0,X1) != X1 ) ),
    inference(definition_unfolding,[],[f95,f114])).

fof(f95,plain,(
    ! [X0,X1] :
      ( sK10(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f2884,plain,(
    spl12_115 ),
    inference(avatar_contradiction_clause,[],[f2883])).

fof(f2883,plain,
    ( $false
    | spl12_115 ),
    inference(subsumption_resolution,[],[f2882,f66])).

fof(f2882,plain,
    ( ~ v1_relat_1(sK6)
    | spl12_115 ),
    inference(trivial_inequality_removal,[],[f2880])).

fof(f2880,plain,
    ( k2_relat_1(sK6) != k2_relat_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl12_115 ),
    inference(superposition,[],[f2874,f76])).

fof(f76,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2874,plain,
    ( k2_relat_1(sK6) != k1_relat_1(k4_relat_1(sK6))
    | spl12_115 ),
    inference(avatar_component_clause,[],[f2872])).

fof(f2872,plain,
    ( spl12_115
  <=> k2_relat_1(sK6) = k1_relat_1(k4_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_115])])).

fof(f2879,plain,
    ( ~ spl12_115
    | spl12_116
    | spl12_7
    | ~ spl12_101 ),
    inference(avatar_split_clause,[],[f2870,f2384,f456,f2876,f2872])).

fof(f2870,plain,
    ( sP0(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),sK6)
    | k2_relat_1(sK6) != k1_relat_1(k4_relat_1(sK6))
    | spl12_7
    | ~ spl12_101 ),
    inference(inner_rewriting,[],[f2869])).

fof(f2869,plain,
    ( sP0(sK10(k1_relat_1(k4_relat_1(sK6)),k1_funct_1(sK6,sK5)),sK6)
    | k2_relat_1(sK6) != k1_relat_1(k4_relat_1(sK6))
    | spl12_7
    | ~ spl12_101 ),
    inference(subsumption_resolution,[],[f2854,f458])).

fof(f458,plain,
    ( k1_xboole_0 != k1_relat_1(k4_relat_1(sK6))
    | spl12_7 ),
    inference(avatar_component_clause,[],[f456])).

fof(f2854,plain,
    ( sP0(sK10(k1_relat_1(k4_relat_1(sK6)),k1_funct_1(sK6,sK5)),sK6)
    | k1_xboole_0 = k1_relat_1(k4_relat_1(sK6))
    | k2_relat_1(sK6) != k1_relat_1(k4_relat_1(sK6))
    | ~ spl12_101 ),
    inference(resolution,[],[f2403,f563])).

fof(f2403,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_relat_1(k4_relat_1(sK6)))
        | sP0(X2,sK6) )
    | ~ spl12_101 ),
    inference(resolution,[],[f2385,f82])).

fof(f2398,plain,
    ( ~ spl12_96
    | spl12_101 ),
    inference(avatar_contradiction_clause,[],[f2397])).

fof(f2397,plain,
    ( $false
    | ~ spl12_96
    | spl12_101 ),
    inference(subsumption_resolution,[],[f2396,f66])).

fof(f2396,plain,
    ( ~ v1_relat_1(sK6)
    | ~ spl12_96
    | spl12_101 ),
    inference(subsumption_resolution,[],[f2394,f2254])).

fof(f2394,plain,
    ( ~ sP1(sK6,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | spl12_101 ),
    inference(superposition,[],[f2386,f76])).

fof(f2386,plain,
    ( ~ sP1(sK6,k1_relat_1(k4_relat_1(sK6)))
    | spl12_101 ),
    inference(avatar_component_clause,[],[f2384])).

fof(f2294,plain,
    ( ~ spl12_1
    | spl12_96 ),
    inference(avatar_contradiction_clause,[],[f2293])).

fof(f2293,plain,
    ( $false
    | ~ spl12_1
    | spl12_96 ),
    inference(subsumption_resolution,[],[f2288,f190])).

fof(f190,plain,
    ( sP2(sK6)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl12_1
  <=> sP2(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f2288,plain,
    ( ~ sP2(sK6)
    | spl12_96 ),
    inference(resolution,[],[f2255,f123])).

fof(f123,plain,(
    ! [X0] :
      ( sP1(X0,k2_relat_1(X0))
      | ~ sP2(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP1(X0,X1) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f2255,plain,
    ( ~ sP1(sK6,k2_relat_1(sK6))
    | spl12_96 ),
    inference(avatar_component_clause,[],[f2253])).

fof(f431,plain,(
    spl12_3 ),
    inference(avatar_contradiction_clause,[],[f430])).

fof(f430,plain,
    ( $false
    | spl12_3 ),
    inference(subsumption_resolution,[],[f429,f66])).

fof(f429,plain,
    ( ~ v1_relat_1(sK6)
    | spl12_3 ),
    inference(resolution,[],[f424,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f424,plain,
    ( ~ v1_relat_1(k4_relat_1(sK6))
    | spl12_3 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl12_3
  <=> v1_relat_1(k4_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f428,plain,
    ( ~ spl12_3
    | spl12_4 ),
    inference(avatar_split_clause,[],[f420,f426,f422])).

fof(f420,plain,(
    ! [X0] :
      ( sK5 = X0
      | ~ r2_hidden(X0,k2_relat_1(k4_relat_1(sK6)))
      | ~ v1_relat_1(k4_relat_1(sK6)) ) ),
    inference(resolution,[],[f418,f340])).

fof(f340,plain,(
    ! [X0,X1] :
      ( sP3(k1_relat_1(X0),X0,X1)
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f337,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f32,f38,f37])).

fof(f37,plain,(
    ! [X1,X2,X0] :
      ( sP3(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(k4_tarski(X3,X0),X2)
          & r2_hidden(X3,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f38,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> sP3(X1,X2,X0) )
      | ~ sP4(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f337,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_relat_1(X0))
      | sP3(k1_relat_1(X0),X0,X1)
      | ~ sP4(X1,X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f97,f74])).

fof(f74,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | sP3(X2,X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X1,X2))
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | ~ r2_hidden(X0,k9_relat_1(X1,X2)) ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ~ sP3(X1,X2,X0) )
        & ( sP3(X1,X2,X0)
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ sP4(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f418,plain,(
    ! [X0,X1] :
      ( ~ sP3(X1,k4_relat_1(sK6),X0)
      | sK5 = X0 ) ),
    inference(resolution,[],[f416,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK11(X0,X1,X2),X2),X1)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X2),X1)
            | ~ r2_hidden(X3,k1_relat_1(X1)) ) )
      & ( ( r2_hidden(sK11(X0,X1,X2),X0)
          & r2_hidden(k4_tarski(sK11(X0,X1,X2),X2),X1)
          & r2_hidden(sK11(X0,X1,X2),k1_relat_1(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X4,X2),X1)
          & r2_hidden(X4,k1_relat_1(X1)) )
     => ( r2_hidden(sK11(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(sK11(X0,X1,X2),X2),X1)
        & r2_hidden(sK11(X0,X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X2),X1)
            | ~ r2_hidden(X3,k1_relat_1(X1)) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X4,X2),X1)
            & r2_hidden(X4,k1_relat_1(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X1,X2,X0] :
      ( ( sP3(X1,X2,X0)
        | ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) )
        | ~ sP3(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f416,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(X6,X7),k4_relat_1(sK6))
      | sK5 = X7 ) ),
    inference(subsumption_resolution,[],[f413,f66])).

fof(f413,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(X6,X7),k4_relat_1(sK6))
      | sK5 = X7
      | ~ v1_relat_1(sK6) ) ),
    inference(resolution,[],[f407,f224])).

fof(f224,plain,(
    ! [X0] :
      ( r1_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k1_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,(
    ! [X0] :
      ( r1_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k1_relat_1(X0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f133,f77])).

fof(f133,plain,(
    ! [X0] :
      ( r1_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k4_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f131,f73])).

fof(f131,plain,(
    ! [X0] :
      ( r1_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k4_relat_1(X0))))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f75,f76])).

fof(f75,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f407,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r1_tarski(X5,k2_zfmisc_1(X6,k1_relat_1(sK6)))
      | ~ r2_hidden(k4_tarski(X4,X3),X5)
      | sK5 = X3 ) ),
    inference(resolution,[],[f405,f91])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f405,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_relat_1(sK6)))
      | sK5 = X1 ) ),
    inference(superposition,[],[f121,f116])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f106,f114])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f200,plain,(
    spl12_1 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | spl12_1 ),
    inference(subsumption_resolution,[],[f198,f66])).

fof(f198,plain,
    ( ~ v1_relat_1(sK6)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f197,f67])).

fof(f67,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f197,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl12_1 ),
    inference(resolution,[],[f191,f89])).

fof(f89,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f29,f35,f34,f33])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f191,plain,
    ( ~ sP2(sK6)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f189])).

fof(f195,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f185,f193,f189])).

fof(f185,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | ~ sP1(sK6,X0)
      | ~ sP2(sK6) ) ),
    inference(superposition,[],[f183,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | ~ sP1(X0,X1)
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:58:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (1809)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (1826)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (1806)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (1818)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (1810)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (1819)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (1828)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (1820)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (1808)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (1815)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (1816)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (1811)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (1807)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (1812)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (1833)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.55  % (1829)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.55  % (1832)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.55  % (1831)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.55  % (1825)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.55  % (1810)Refutation not found, incomplete strategy% (1810)------------------------------
% 1.38/0.55  % (1810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (1810)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (1810)Memory used [KB]: 6268
% 1.38/0.55  % (1810)Time elapsed: 0.129 s
% 1.38/0.55  % (1810)------------------------------
% 1.38/0.55  % (1810)------------------------------
% 1.38/0.55  % (1835)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.55  % (1817)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.55  % (1822)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.55  % (1821)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.55  % (1823)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.55  % (1830)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.55  % (1824)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.55  % (1823)Refutation not found, incomplete strategy% (1823)------------------------------
% 1.38/0.55  % (1823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (1823)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (1823)Memory used [KB]: 10618
% 1.38/0.55  % (1823)Time elapsed: 0.141 s
% 1.38/0.55  % (1823)------------------------------
% 1.38/0.55  % (1823)------------------------------
% 1.38/0.55  % (1827)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.56  % (1834)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.56  % (1813)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.56  % (1814)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.56  % (1828)Refutation not found, incomplete strategy% (1828)------------------------------
% 1.38/0.56  % (1828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (1828)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (1828)Memory used [KB]: 11001
% 1.38/0.56  % (1828)Time elapsed: 0.101 s
% 1.38/0.56  % (1828)------------------------------
% 1.38/0.56  % (1828)------------------------------
% 2.35/0.69  % (1838)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.35/0.70  % (1837)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.67/0.75  % (1833)Refutation found. Thanks to Tanya!
% 2.67/0.75  % SZS status Theorem for theBenchmark
% 2.82/0.75  % SZS output start Proof for theBenchmark
% 2.82/0.75  fof(f3759,plain,(
% 2.82/0.75    $false),
% 2.82/0.75    inference(avatar_sat_refutation,[],[f195,f200,f428,f431,f2294,f2398,f2879,f2884,f3595,f3641,f3734])).
% 2.82/0.75  fof(f3734,plain,(
% 2.82/0.75    ~spl12_10 | ~spl12_96),
% 2.82/0.75    inference(avatar_contradiction_clause,[],[f3733])).
% 2.82/0.75  fof(f3733,plain,(
% 2.82/0.75    $false | (~spl12_10 | ~spl12_96)),
% 2.82/0.75    inference(subsumption_resolution,[],[f2803,f494])).
% 2.82/0.75  fof(f494,plain,(
% 2.82/0.75    ( ! [X1] : (~sP0(X1,sK6)) ) | ~spl12_10),
% 2.82/0.75    inference(avatar_component_clause,[],[f493])).
% 2.82/0.75  fof(f493,plain,(
% 2.82/0.75    spl12_10 <=> ! [X1] : ~sP0(X1,sK6)),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 2.82/0.75  fof(f2803,plain,(
% 2.82/0.75    sP0(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),sK6) | ~spl12_96),
% 2.82/0.75    inference(subsumption_resolution,[],[f2799,f183])).
% 2.82/0.75  fof(f183,plain,(
% 2.82/0.75    k1_xboole_0 != k2_relat_1(sK6)),
% 2.82/0.75    inference(subsumption_resolution,[],[f182,f66])).
% 2.82/0.75  fof(f66,plain,(
% 2.82/0.75    v1_relat_1(sK6)),
% 2.82/0.75    inference(cnf_transformation,[],[f41])).
% 2.82/0.75  fof(f41,plain,(
% 2.82/0.75    k2_relat_1(sK6) != k1_tarski(k1_funct_1(sK6,sK5)) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 2.82/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f22,f40])).
% 2.82/0.75  fof(f40,plain,(
% 2.82/0.75    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK6) != k1_tarski(k1_funct_1(sK6,sK5)) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 2.82/0.75    introduced(choice_axiom,[])).
% 2.82/0.75  fof(f22,plain,(
% 2.82/0.75    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.82/0.75    inference(flattening,[],[f21])).
% 2.82/0.75  fof(f21,plain,(
% 2.82/0.75    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.82/0.75    inference(ennf_transformation,[],[f20])).
% 2.82/0.75  fof(f20,negated_conjecture,(
% 2.82/0.75    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 2.82/0.75    inference(negated_conjecture,[],[f19])).
% 2.82/0.75  fof(f19,conjecture,(
% 2.82/0.75    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 2.82/0.75  fof(f182,plain,(
% 2.82/0.75    k1_xboole_0 != k2_relat_1(sK6) | ~v1_relat_1(sK6)),
% 2.82/0.75    inference(subsumption_resolution,[],[f175,f70])).
% 2.82/0.75  fof(f70,plain,(
% 2.82/0.75    v1_xboole_0(k1_xboole_0)),
% 2.82/0.75    inference(cnf_transformation,[],[f2])).
% 2.82/0.75  fof(f2,axiom,(
% 2.82/0.75    v1_xboole_0(k1_xboole_0)),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.82/0.75  fof(f175,plain,(
% 2.82/0.75    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 != k2_relat_1(sK6) | ~v1_relat_1(sK6)),
% 2.82/0.75    inference(superposition,[],[f146,f79])).
% 2.82/0.75  fof(f79,plain,(
% 2.82/0.75    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f42])).
% 2.82/0.75  fof(f42,plain,(
% 2.82/0.75    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.82/0.75    inference(nnf_transformation,[],[f27])).
% 2.82/0.75  fof(f27,plain,(
% 2.82/0.75    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.82/0.75    inference(ennf_transformation,[],[f17])).
% 2.82/0.75  fof(f17,axiom,(
% 2.82/0.75    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 2.82/0.75  fof(f146,plain,(
% 2.82/0.75    ~v1_xboole_0(k1_relat_1(sK6))),
% 2.82/0.75    inference(superposition,[],[f117,f116])).
% 2.82/0.75  fof(f116,plain,(
% 2.82/0.75    k1_relat_1(sK6) = k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)),
% 2.82/0.75    inference(definition_unfolding,[],[f68,f114])).
% 2.82/0.75  fof(f114,plain,(
% 2.82/0.75    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 2.82/0.75    inference(definition_unfolding,[],[f72,f113])).
% 2.82/0.75  fof(f113,plain,(
% 2.82/0.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 2.82/0.75    inference(definition_unfolding,[],[f90,f112])).
% 2.82/0.75  fof(f112,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 2.82/0.75    inference(definition_unfolding,[],[f96,f111])).
% 2.82/0.75  fof(f111,plain,(
% 2.82/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 2.82/0.75    inference(definition_unfolding,[],[f104,f110])).
% 2.82/0.75  fof(f110,plain,(
% 2.82/0.75    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 2.82/0.75    inference(definition_unfolding,[],[f108,f109])).
% 2.82/0.75  fof(f109,plain,(
% 2.82/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f8])).
% 2.82/0.75  fof(f8,axiom,(
% 2.82/0.75    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.82/0.75  fof(f108,plain,(
% 2.82/0.75    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f7])).
% 2.82/0.75  fof(f7,axiom,(
% 2.82/0.75    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.82/0.75  fof(f104,plain,(
% 2.82/0.75    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f6])).
% 2.82/0.75  fof(f6,axiom,(
% 2.82/0.75    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.82/0.75  fof(f96,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f5])).
% 2.82/0.75  fof(f5,axiom,(
% 2.82/0.75    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.82/0.75  fof(f90,plain,(
% 2.82/0.75    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f4])).
% 2.82/0.75  fof(f4,axiom,(
% 2.82/0.75    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.82/0.75  fof(f72,plain,(
% 2.82/0.75    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f3])).
% 2.82/0.75  fof(f3,axiom,(
% 2.82/0.75    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.82/0.75  fof(f68,plain,(
% 2.82/0.75    k1_tarski(sK5) = k1_relat_1(sK6)),
% 2.82/0.75    inference(cnf_transformation,[],[f41])).
% 2.82/0.75  fof(f117,plain,(
% 2.82/0.75    ( ! [X0] : (~v1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) )),
% 2.82/0.75    inference(definition_unfolding,[],[f71,f114])).
% 2.82/0.75  fof(f71,plain,(
% 2.82/0.75    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.82/0.75    inference(cnf_transformation,[],[f9])).
% 2.82/0.75  fof(f9,axiom,(
% 2.82/0.75    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 2.82/0.75  fof(f2799,plain,(
% 2.82/0.75    sP0(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),sK6) | k1_xboole_0 = k2_relat_1(sK6) | ~spl12_96),
% 2.82/0.75    inference(trivial_inequality_removal,[],[f2794])).
% 2.82/0.75  fof(f2794,plain,(
% 2.82/0.75    sP0(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),sK6) | k1_xboole_0 = k2_relat_1(sK6) | k2_relat_1(sK6) != k2_relat_1(sK6) | ~spl12_96),
% 2.82/0.75    inference(resolution,[],[f2311,f563])).
% 2.82/0.75  fof(f563,plain,(
% 2.82/0.75    ( ! [X20] : (r2_hidden(sK10(X20,k1_funct_1(sK6,sK5)),X20) | k1_xboole_0 = X20 | k2_relat_1(sK6) != X20) )),
% 2.82/0.75    inference(superposition,[],[f115,f119])).
% 2.82/0.75  fof(f119,plain,(
% 2.82/0.75    ( ! [X0,X1] : (k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK10(X0,X1),X0)) )),
% 2.82/0.75    inference(definition_unfolding,[],[f94,f114])).
% 2.82/0.75  fof(f94,plain,(
% 2.82/0.75    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.82/0.75    inference(cnf_transformation,[],[f57])).
% 2.82/0.75  fof(f57,plain,(
% 2.82/0.75    ! [X0,X1] : ((sK10(X0,X1) != X1 & r2_hidden(sK10(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.82/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f31,f56])).
% 2.82/0.75  fof(f56,plain,(
% 2.82/0.75    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK10(X0,X1) != X1 & r2_hidden(sK10(X0,X1),X0)))),
% 2.82/0.75    introduced(choice_axiom,[])).
% 2.82/0.75  fof(f31,plain,(
% 2.82/0.75    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.82/0.75    inference(ennf_transformation,[],[f11])).
% 2.82/0.75  fof(f11,axiom,(
% 2.82/0.75    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 2.82/0.75  fof(f115,plain,(
% 2.82/0.75    k2_relat_1(sK6) != k5_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5))),
% 2.82/0.75    inference(definition_unfolding,[],[f69,f114])).
% 2.82/0.75  fof(f69,plain,(
% 2.82/0.75    k2_relat_1(sK6) != k1_tarski(k1_funct_1(sK6,sK5))),
% 2.82/0.75    inference(cnf_transformation,[],[f41])).
% 2.82/0.75  fof(f2311,plain,(
% 2.82/0.75    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK6)) | sP0(X2,sK6)) ) | ~spl12_96),
% 2.82/0.75    inference(resolution,[],[f2254,f82])).
% 2.82/0.75  fof(f82,plain,(
% 2.82/0.75    ( ! [X0,X3,X1] : (~sP1(X0,X1) | ~r2_hidden(X3,X1) | sP0(X3,X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f47])).
% 2.82/0.75  fof(f47,plain,(
% 2.82/0.75    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(sK7(X0,X1),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (sP0(sK7(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 2.82/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f45,f46])).
% 2.82/0.75  % (1836)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.82/0.75  fof(f46,plain,(
% 2.82/0.75    ! [X1,X0] : (? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1))) => ((~sP0(sK7(X0,X1),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (sP0(sK7(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 2.82/0.75    introduced(choice_axiom,[])).
% 2.82/0.75  fof(f45,plain,(
% 2.82/0.75    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 2.82/0.75    inference(rectify,[],[f44])).
% 2.82/0.75  fof(f44,plain,(
% 2.82/0.75    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X2,X0)) & (sP0(X2,X0) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 2.82/0.75    inference(nnf_transformation,[],[f34])).
% 2.82/0.75  fof(f34,plain,(
% 2.82/0.75    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X2,X0)))),
% 2.82/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.82/0.75  fof(f2254,plain,(
% 2.82/0.75    sP1(sK6,k2_relat_1(sK6)) | ~spl12_96),
% 2.82/0.75    inference(avatar_component_clause,[],[f2253])).
% 2.82/0.75  fof(f2253,plain,(
% 2.82/0.75    spl12_96 <=> sP1(sK6,k2_relat_1(sK6))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl12_96])])).
% 2.82/0.75  fof(f3641,plain,(
% 2.82/0.75    ~spl12_7 | ~spl12_2 | ~spl12_101),
% 2.82/0.75    inference(avatar_split_clause,[],[f2400,f2384,f193,f456])).
% 2.82/0.75  fof(f456,plain,(
% 2.82/0.75    spl12_7 <=> k1_xboole_0 = k1_relat_1(k4_relat_1(sK6))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 2.82/0.75  fof(f193,plain,(
% 2.82/0.75    spl12_2 <=> ! [X0] : (k1_xboole_0 != X0 | ~sP1(sK6,X0))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 2.82/0.75  fof(f2384,plain,(
% 2.82/0.75    spl12_101 <=> sP1(sK6,k1_relat_1(k4_relat_1(sK6)))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl12_101])])).
% 2.82/0.75  fof(f2400,plain,(
% 2.82/0.75    k1_xboole_0 != k1_relat_1(k4_relat_1(sK6)) | (~spl12_2 | ~spl12_101)),
% 2.82/0.75    inference(resolution,[],[f2385,f194])).
% 2.82/0.75  fof(f194,plain,(
% 2.82/0.75    ( ! [X0] : (~sP1(sK6,X0) | k1_xboole_0 != X0) ) | ~spl12_2),
% 2.82/0.75    inference(avatar_component_clause,[],[f193])).
% 2.82/0.75  fof(f2385,plain,(
% 2.82/0.75    sP1(sK6,k1_relat_1(k4_relat_1(sK6))) | ~spl12_101),
% 2.82/0.75    inference(avatar_component_clause,[],[f2384])).
% 2.82/0.75  fof(f3595,plain,(
% 2.82/0.75    spl12_10 | ~spl12_4 | ~spl12_116),
% 2.82/0.75    inference(avatar_split_clause,[],[f3594,f2876,f426,f493])).
% 2.82/0.75  fof(f426,plain,(
% 2.82/0.75    spl12_4 <=> ! [X0] : (sK5 = X0 | ~r2_hidden(X0,k2_relat_1(k4_relat_1(sK6))))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 2.82/0.75  fof(f2876,plain,(
% 2.82/0.75    spl12_116 <=> sP0(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),sK6)),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl12_116])])).
% 2.82/0.75  fof(f3594,plain,(
% 2.82/0.75    ( ! [X4] : (~sP0(X4,sK6)) ) | (~spl12_4 | ~spl12_116)),
% 2.82/0.75    inference(subsumption_resolution,[],[f3593,f491])).
% 2.82/0.75  fof(f491,plain,(
% 2.82/0.75    ( ! [X0] : (k1_funct_1(sK6,sK5) = X0 | ~sP0(X0,sK6)) ) | ~spl12_4),
% 2.82/0.75    inference(duplicate_literal_removal,[],[f488])).
% 2.82/0.75  fof(f488,plain,(
% 2.82/0.75    ( ! [X0] : (k1_funct_1(sK6,sK5) = X0 | ~sP0(X0,sK6) | ~sP0(X0,sK6)) ) | ~spl12_4),
% 2.82/0.75    inference(superposition,[],[f87,f483])).
% 2.82/0.75  fof(f483,plain,(
% 2.82/0.75    ( ! [X4] : (sK5 = sK8(X4,sK6) | ~sP0(X4,sK6)) ) | ~spl12_4),
% 2.82/0.75    inference(resolution,[],[f453,f86])).
% 2.82/0.75  fof(f86,plain,(
% 2.82/0.75    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),k1_relat_1(X1)) | ~sP0(X0,X1)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f51])).
% 2.82/0.75  fof(f51,plain,(
% 2.82/0.75    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK8(X0,X1)) = X0 & r2_hidden(sK8(X0,X1),k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 2.82/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).
% 2.82/0.75  fof(f50,plain,(
% 2.82/0.75    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK8(X0,X1)) = X0 & r2_hidden(sK8(X0,X1),k1_relat_1(X1))))),
% 2.82/0.75    introduced(choice_axiom,[])).
% 2.82/0.75  fof(f49,plain,(
% 2.82/0.75    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 2.82/0.75    inference(rectify,[],[f48])).
% 2.82/0.75  fof(f48,plain,(
% 2.82/0.75    ! [X2,X0] : ((sP0(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X0)))),
% 2.82/0.75    inference(nnf_transformation,[],[f33])).
% 2.82/0.75  fof(f33,plain,(
% 2.82/0.75    ! [X2,X0] : (sP0(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 2.82/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.82/0.75  fof(f453,plain,(
% 2.82/0.75    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | sK5 = X0) ) | ~spl12_4),
% 2.82/0.75    inference(subsumption_resolution,[],[f441,f66])).
% 2.82/0.75  fof(f441,plain,(
% 2.82/0.75    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | sK5 = X0 | ~v1_relat_1(sK6)) ) | ~spl12_4),
% 2.82/0.75    inference(superposition,[],[f427,f77])).
% 2.82/0.75  fof(f77,plain,(
% 2.82/0.75    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f26])).
% 2.82/0.75  fof(f26,plain,(
% 2.82/0.75    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.82/0.75    inference(ennf_transformation,[],[f16])).
% 2.82/0.75  fof(f16,axiom,(
% 2.82/0.75    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 2.82/0.75  fof(f427,plain,(
% 2.82/0.75    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k4_relat_1(sK6))) | sK5 = X0) ) | ~spl12_4),
% 2.82/0.75    inference(avatar_component_clause,[],[f426])).
% 2.82/0.75  fof(f87,plain,(
% 2.82/0.75    ( ! [X0,X1] : (k1_funct_1(X1,sK8(X0,X1)) = X0 | ~sP0(X0,X1)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f51])).
% 2.82/0.75  fof(f3593,plain,(
% 2.82/0.75    ( ! [X4] : (k1_funct_1(sK6,sK5) != X4 | ~sP0(X4,sK6)) ) | (~spl12_4 | ~spl12_116)),
% 2.82/0.75    inference(subsumption_resolution,[],[f3590,f183])).
% 2.82/0.75  fof(f3590,plain,(
% 2.82/0.75    ( ! [X4] : (k1_funct_1(sK6,sK5) != X4 | k1_xboole_0 = k2_relat_1(sK6) | ~sP0(X4,sK6)) ) | (~spl12_4 | ~spl12_116)),
% 2.82/0.75    inference(trivial_inequality_removal,[],[f3583])).
% 2.82/0.75  fof(f3583,plain,(
% 2.82/0.75    ( ! [X4] : (k1_funct_1(sK6,sK5) != X4 | k1_xboole_0 = k2_relat_1(sK6) | k2_relat_1(sK6) != k2_relat_1(sK6) | ~sP0(X4,sK6)) ) | (~spl12_4 | ~spl12_116)),
% 2.82/0.75    inference(superposition,[],[f521,f2941])).
% 2.82/0.75  fof(f2941,plain,(
% 2.82/0.75    ( ! [X0] : (sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) = X0 | ~sP0(X0,sK6)) ) | (~spl12_4 | ~spl12_116)),
% 2.82/0.75    inference(resolution,[],[f2878,f839])).
% 2.82/0.75  fof(f839,plain,(
% 2.82/0.75    ( ! [X0,X1] : (~sP0(X1,sK6) | X0 = X1 | ~sP0(X0,sK6)) ) | ~spl12_4),
% 2.82/0.75    inference(superposition,[],[f491,f491])).
% 2.82/0.75  fof(f2878,plain,(
% 2.82/0.75    sP0(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),sK6) | ~spl12_116),
% 2.82/0.75    inference(avatar_component_clause,[],[f2876])).
% 2.82/0.75  fof(f521,plain,(
% 2.82/0.75    ( ! [X17] : (k1_funct_1(sK6,sK5) != sK10(X17,k1_funct_1(sK6,sK5)) | k1_xboole_0 = X17 | k2_relat_1(sK6) != X17) )),
% 2.82/0.75    inference(superposition,[],[f115,f118])).
% 2.82/0.75  fof(f118,plain,(
% 2.82/0.75    ( ! [X0,X1] : (k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | sK10(X0,X1) != X1) )),
% 2.82/0.75    inference(definition_unfolding,[],[f95,f114])).
% 2.82/0.75  fof(f95,plain,(
% 2.82/0.75    ( ! [X0,X1] : (sK10(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.82/0.75    inference(cnf_transformation,[],[f57])).
% 2.82/0.75  fof(f2884,plain,(
% 2.82/0.75    spl12_115),
% 2.82/0.75    inference(avatar_contradiction_clause,[],[f2883])).
% 2.82/0.75  fof(f2883,plain,(
% 2.82/0.75    $false | spl12_115),
% 2.82/0.75    inference(subsumption_resolution,[],[f2882,f66])).
% 2.82/0.75  fof(f2882,plain,(
% 2.82/0.75    ~v1_relat_1(sK6) | spl12_115),
% 2.82/0.75    inference(trivial_inequality_removal,[],[f2880])).
% 2.82/0.75  fof(f2880,plain,(
% 2.82/0.75    k2_relat_1(sK6) != k2_relat_1(sK6) | ~v1_relat_1(sK6) | spl12_115),
% 2.82/0.75    inference(superposition,[],[f2874,f76])).
% 2.82/0.75  fof(f76,plain,(
% 2.82/0.75    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f26])).
% 2.82/0.75  fof(f2874,plain,(
% 2.82/0.75    k2_relat_1(sK6) != k1_relat_1(k4_relat_1(sK6)) | spl12_115),
% 2.82/0.75    inference(avatar_component_clause,[],[f2872])).
% 2.82/0.75  fof(f2872,plain,(
% 2.82/0.75    spl12_115 <=> k2_relat_1(sK6) = k1_relat_1(k4_relat_1(sK6))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl12_115])])).
% 2.82/0.75  fof(f2879,plain,(
% 2.82/0.75    ~spl12_115 | spl12_116 | spl12_7 | ~spl12_101),
% 2.82/0.75    inference(avatar_split_clause,[],[f2870,f2384,f456,f2876,f2872])).
% 2.82/0.75  fof(f2870,plain,(
% 2.82/0.75    sP0(sK10(k2_relat_1(sK6),k1_funct_1(sK6,sK5)),sK6) | k2_relat_1(sK6) != k1_relat_1(k4_relat_1(sK6)) | (spl12_7 | ~spl12_101)),
% 2.82/0.75    inference(inner_rewriting,[],[f2869])).
% 2.82/0.75  fof(f2869,plain,(
% 2.82/0.75    sP0(sK10(k1_relat_1(k4_relat_1(sK6)),k1_funct_1(sK6,sK5)),sK6) | k2_relat_1(sK6) != k1_relat_1(k4_relat_1(sK6)) | (spl12_7 | ~spl12_101)),
% 2.82/0.75    inference(subsumption_resolution,[],[f2854,f458])).
% 2.82/0.75  fof(f458,plain,(
% 2.82/0.75    k1_xboole_0 != k1_relat_1(k4_relat_1(sK6)) | spl12_7),
% 2.82/0.75    inference(avatar_component_clause,[],[f456])).
% 2.82/0.75  fof(f2854,plain,(
% 2.82/0.75    sP0(sK10(k1_relat_1(k4_relat_1(sK6)),k1_funct_1(sK6,sK5)),sK6) | k1_xboole_0 = k1_relat_1(k4_relat_1(sK6)) | k2_relat_1(sK6) != k1_relat_1(k4_relat_1(sK6)) | ~spl12_101),
% 2.82/0.75    inference(resolution,[],[f2403,f563])).
% 2.82/0.75  fof(f2403,plain,(
% 2.82/0.75    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(k4_relat_1(sK6))) | sP0(X2,sK6)) ) | ~spl12_101),
% 2.82/0.75    inference(resolution,[],[f2385,f82])).
% 2.82/0.75  fof(f2398,plain,(
% 2.82/0.75    ~spl12_96 | spl12_101),
% 2.82/0.75    inference(avatar_contradiction_clause,[],[f2397])).
% 2.82/0.75  fof(f2397,plain,(
% 2.82/0.75    $false | (~spl12_96 | spl12_101)),
% 2.82/0.75    inference(subsumption_resolution,[],[f2396,f66])).
% 2.82/0.75  fof(f2396,plain,(
% 2.82/0.75    ~v1_relat_1(sK6) | (~spl12_96 | spl12_101)),
% 2.82/0.75    inference(subsumption_resolution,[],[f2394,f2254])).
% 2.82/0.75  fof(f2394,plain,(
% 2.82/0.75    ~sP1(sK6,k2_relat_1(sK6)) | ~v1_relat_1(sK6) | spl12_101),
% 2.82/0.75    inference(superposition,[],[f2386,f76])).
% 2.82/0.75  fof(f2386,plain,(
% 2.82/0.75    ~sP1(sK6,k1_relat_1(k4_relat_1(sK6))) | spl12_101),
% 2.82/0.75    inference(avatar_component_clause,[],[f2384])).
% 2.82/0.75  fof(f2294,plain,(
% 2.82/0.75    ~spl12_1 | spl12_96),
% 2.82/0.75    inference(avatar_contradiction_clause,[],[f2293])).
% 2.82/0.75  fof(f2293,plain,(
% 2.82/0.75    $false | (~spl12_1 | spl12_96)),
% 2.82/0.75    inference(subsumption_resolution,[],[f2288,f190])).
% 2.82/0.75  fof(f190,plain,(
% 2.82/0.75    sP2(sK6) | ~spl12_1),
% 2.82/0.75    inference(avatar_component_clause,[],[f189])).
% 2.82/0.75  fof(f189,plain,(
% 2.82/0.75    spl12_1 <=> sP2(sK6)),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 2.82/0.75  fof(f2288,plain,(
% 2.82/0.75    ~sP2(sK6) | spl12_96),
% 2.82/0.75    inference(resolution,[],[f2255,f123])).
% 2.82/0.75  fof(f123,plain,(
% 2.82/0.75    ( ! [X0] : (sP1(X0,k2_relat_1(X0)) | ~sP2(X0)) )),
% 2.82/0.75    inference(equality_resolution,[],[f80])).
% 2.82/0.75  fof(f80,plain,(
% 2.82/0.75    ( ! [X0,X1] : (sP1(X0,X1) | k2_relat_1(X0) != X1 | ~sP2(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f43])).
% 2.82/0.75  fof(f43,plain,(
% 2.82/0.75    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k2_relat_1(X0) != X1)) | ~sP2(X0))),
% 2.82/0.75    inference(nnf_transformation,[],[f35])).
% 2.82/0.75  fof(f35,plain,(
% 2.82/0.75    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP1(X0,X1)) | ~sP2(X0))),
% 2.82/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.82/0.75  fof(f2255,plain,(
% 2.82/0.75    ~sP1(sK6,k2_relat_1(sK6)) | spl12_96),
% 2.82/0.75    inference(avatar_component_clause,[],[f2253])).
% 2.82/0.75  fof(f431,plain,(
% 2.82/0.75    spl12_3),
% 2.82/0.75    inference(avatar_contradiction_clause,[],[f430])).
% 2.82/0.75  fof(f430,plain,(
% 2.82/0.75    $false | spl12_3),
% 2.82/0.75    inference(subsumption_resolution,[],[f429,f66])).
% 2.82/0.75  fof(f429,plain,(
% 2.82/0.75    ~v1_relat_1(sK6) | spl12_3),
% 2.82/0.75    inference(resolution,[],[f424,f73])).
% 2.82/0.75  fof(f73,plain,(
% 2.82/0.75    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f23])).
% 2.82/0.75  fof(f23,plain,(
% 2.82/0.75    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.82/0.75    inference(ennf_transformation,[],[f12])).
% 2.82/0.75  fof(f12,axiom,(
% 2.82/0.75    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 2.82/0.75  fof(f424,plain,(
% 2.82/0.75    ~v1_relat_1(k4_relat_1(sK6)) | spl12_3),
% 2.82/0.75    inference(avatar_component_clause,[],[f422])).
% 2.82/0.75  fof(f422,plain,(
% 2.82/0.75    spl12_3 <=> v1_relat_1(k4_relat_1(sK6))),
% 2.82/0.75    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 2.82/0.75  fof(f428,plain,(
% 2.82/0.75    ~spl12_3 | spl12_4),
% 2.82/0.75    inference(avatar_split_clause,[],[f420,f426,f422])).
% 2.82/0.75  fof(f420,plain,(
% 2.82/0.75    ( ! [X0] : (sK5 = X0 | ~r2_hidden(X0,k2_relat_1(k4_relat_1(sK6))) | ~v1_relat_1(k4_relat_1(sK6))) )),
% 2.82/0.75    inference(resolution,[],[f418,f340])).
% 2.82/0.75  fof(f340,plain,(
% 2.82/0.75    ( ! [X0,X1] : (sP3(k1_relat_1(X0),X0,X1) | ~r2_hidden(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.82/0.75    inference(subsumption_resolution,[],[f337,f103])).
% 2.82/0.75  fof(f103,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (sP4(X0,X2,X1) | ~v1_relat_1(X2)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f39])).
% 2.82/0.75  fof(f39,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (sP4(X0,X2,X1) | ~v1_relat_1(X2))),
% 2.82/0.75    inference(definition_folding,[],[f32,f38,f37])).
% 2.82/0.75  fof(f37,plain,(
% 2.82/0.75    ! [X1,X2,X0] : (sP3(X1,X2,X0) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))))),
% 2.82/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.82/0.75  fof(f38,plain,(
% 2.82/0.75    ! [X0,X2,X1] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> sP3(X1,X2,X0)) | ~sP4(X0,X2,X1))),
% 2.82/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 2.82/0.75  fof(f32,plain,(
% 2.82/0.75    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.82/0.75    inference(ennf_transformation,[],[f13])).
% 2.82/0.75  fof(f13,axiom,(
% 2.82/0.75    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 2.82/0.75  fof(f337,plain,(
% 2.82/0.75    ( ! [X0,X1] : (~r2_hidden(X1,k2_relat_1(X0)) | sP3(k1_relat_1(X0),X0,X1) | ~sP4(X1,X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.82/0.75    inference(superposition,[],[f97,f74])).
% 2.82/0.75  fof(f74,plain,(
% 2.82/0.75    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f24])).
% 2.82/0.75  fof(f24,plain,(
% 2.82/0.75    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.82/0.75    inference(ennf_transformation,[],[f14])).
% 2.82/0.75  fof(f14,axiom,(
% 2.82/0.75    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 2.82/0.75  fof(f97,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X1,X2)) | sP3(X2,X1,X0) | ~sP4(X0,X1,X2)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f59])).
% 2.82/0.75  fof(f59,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X1,X2)) | ~sP3(X2,X1,X0)) & (sP3(X2,X1,X0) | ~r2_hidden(X0,k9_relat_1(X1,X2)))) | ~sP4(X0,X1,X2))),
% 2.82/0.75    inference(rectify,[],[f58])).
% 2.82/0.75  fof(f58,plain,(
% 2.82/0.75    ! [X0,X2,X1] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ~sP3(X1,X2,X0)) & (sP3(X1,X2,X0) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~sP4(X0,X2,X1))),
% 2.82/0.75    inference(nnf_transformation,[],[f38])).
% 2.82/0.75  fof(f418,plain,(
% 2.82/0.75    ( ! [X0,X1] : (~sP3(X1,k4_relat_1(sK6),X0) | sK5 = X0) )),
% 2.82/0.75    inference(resolution,[],[f416,f100])).
% 2.82/0.75  fof(f100,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK11(X0,X1,X2),X2),X1) | ~sP3(X0,X1,X2)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f63])).
% 2.82/0.75  fof(f63,plain,(
% 2.82/0.75    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X3,X2),X1) | ~r2_hidden(X3,k1_relat_1(X1)))) & ((r2_hidden(sK11(X0,X1,X2),X0) & r2_hidden(k4_tarski(sK11(X0,X1,X2),X2),X1) & r2_hidden(sK11(X0,X1,X2),k1_relat_1(X1))) | ~sP3(X0,X1,X2)))),
% 2.82/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f61,f62])).
% 2.82/0.75  fof(f62,plain,(
% 2.82/0.75    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X2),X1) & r2_hidden(X4,k1_relat_1(X1))) => (r2_hidden(sK11(X0,X1,X2),X0) & r2_hidden(k4_tarski(sK11(X0,X1,X2),X2),X1) & r2_hidden(sK11(X0,X1,X2),k1_relat_1(X1))))),
% 2.82/0.75    introduced(choice_axiom,[])).
% 2.82/0.75  fof(f61,plain,(
% 2.82/0.75    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X3,X2),X1) | ~r2_hidden(X3,k1_relat_1(X1)))) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X2),X1) & r2_hidden(X4,k1_relat_1(X1))) | ~sP3(X0,X1,X2)))),
% 2.82/0.75    inference(rectify,[],[f60])).
% 2.82/0.75  fof(f60,plain,(
% 2.82/0.75    ! [X1,X2,X0] : ((sP3(X1,X2,X0) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~sP3(X1,X2,X0)))),
% 2.82/0.75    inference(nnf_transformation,[],[f37])).
% 2.82/0.75  fof(f416,plain,(
% 2.82/0.75    ( ! [X6,X7] : (~r2_hidden(k4_tarski(X6,X7),k4_relat_1(sK6)) | sK5 = X7) )),
% 2.82/0.75    inference(subsumption_resolution,[],[f413,f66])).
% 2.82/0.75  fof(f413,plain,(
% 2.82/0.75    ( ! [X6,X7] : (~r2_hidden(k4_tarski(X6,X7),k4_relat_1(sK6)) | sK5 = X7 | ~v1_relat_1(sK6)) )),
% 2.82/0.75    inference(resolution,[],[f407,f224])).
% 2.82/0.75  fof(f224,plain,(
% 2.82/0.75    ( ! [X0] : (r1_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k1_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 2.82/0.75    inference(duplicate_literal_removal,[],[f221])).
% 2.82/0.75  fof(f221,plain,(
% 2.82/0.75    ( ! [X0] : (r1_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k1_relat_1(X0))) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.82/0.75    inference(superposition,[],[f133,f77])).
% 2.82/0.75  fof(f133,plain,(
% 2.82/0.75    ( ! [X0] : (r1_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k4_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 2.82/0.75    inference(subsumption_resolution,[],[f131,f73])).
% 2.82/0.75  fof(f131,plain,(
% 2.82/0.75    ( ! [X0] : (r1_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k4_relat_1(X0)))) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.82/0.75    inference(superposition,[],[f75,f76])).
% 2.82/0.75  fof(f75,plain,(
% 2.82/0.75    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f25])).
% 2.82/0.75  fof(f25,plain,(
% 2.82/0.75    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.82/0.75    inference(ennf_transformation,[],[f15])).
% 2.82/0.75  fof(f15,axiom,(
% 2.82/0.75    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 2.82/0.75  fof(f407,plain,(
% 2.82/0.75    ( ! [X6,X4,X5,X3] : (~r1_tarski(X5,k2_zfmisc_1(X6,k1_relat_1(sK6))) | ~r2_hidden(k4_tarski(X4,X3),X5) | sK5 = X3) )),
% 2.82/0.75    inference(resolution,[],[f405,f91])).
% 2.82/0.75  fof(f91,plain,(
% 2.82/0.75    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f55])).
% 2.82/0.75  fof(f55,plain,(
% 2.82/0.75    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.82/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f53,f54])).
% 2.82/0.75  fof(f54,plain,(
% 2.82/0.75    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 2.82/0.75    introduced(choice_axiom,[])).
% 2.82/0.75  fof(f53,plain,(
% 2.82/0.75    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.82/0.75    inference(rectify,[],[f52])).
% 2.82/0.75  fof(f52,plain,(
% 2.82/0.75    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.82/0.75    inference(nnf_transformation,[],[f30])).
% 2.82/0.75  fof(f30,plain,(
% 2.82/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f1])).
% 2.82/0.75  fof(f1,axiom,(
% 2.82/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.82/0.75  fof(f405,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_relat_1(sK6))) | sK5 = X1) )),
% 2.82/0.75    inference(superposition,[],[f121,f116])).
% 2.82/0.75  fof(f121,plain,(
% 2.82/0.75    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X3))) | X1 = X3) )),
% 2.82/0.75    inference(definition_unfolding,[],[f106,f114])).
% 2.82/0.75  fof(f106,plain,(
% 2.82/0.75    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 2.82/0.75    inference(cnf_transformation,[],[f65])).
% 2.82/0.75  fof(f65,plain,(
% 2.82/0.75    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 2.82/0.75    inference(flattening,[],[f64])).
% 2.82/0.75  fof(f64,plain,(
% 2.82/0.75    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 2.82/0.75    inference(nnf_transformation,[],[f10])).
% 2.82/0.75  fof(f10,axiom,(
% 2.82/0.75    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 2.82/0.75  fof(f200,plain,(
% 2.82/0.75    spl12_1),
% 2.82/0.75    inference(avatar_contradiction_clause,[],[f199])).
% 2.82/0.75  fof(f199,plain,(
% 2.82/0.75    $false | spl12_1),
% 2.82/0.75    inference(subsumption_resolution,[],[f198,f66])).
% 2.82/0.75  fof(f198,plain,(
% 2.82/0.75    ~v1_relat_1(sK6) | spl12_1),
% 2.82/0.75    inference(subsumption_resolution,[],[f197,f67])).
% 2.82/0.75  fof(f67,plain,(
% 2.82/0.75    v1_funct_1(sK6)),
% 2.82/0.75    inference(cnf_transformation,[],[f41])).
% 2.82/0.75  fof(f197,plain,(
% 2.82/0.75    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl12_1),
% 2.82/0.75    inference(resolution,[],[f191,f89])).
% 2.82/0.75  fof(f89,plain,(
% 2.82/0.75    ( ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f36])).
% 2.82/0.75  fof(f36,plain,(
% 2.82/0.75    ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.82/0.75    inference(definition_folding,[],[f29,f35,f34,f33])).
% 2.82/0.75  fof(f29,plain,(
% 2.82/0.75    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.82/0.75    inference(flattening,[],[f28])).
% 2.82/0.75  fof(f28,plain,(
% 2.82/0.75    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f18])).
% 2.82/0.75  fof(f18,axiom,(
% 2.82/0.75    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 2.82/0.75  fof(f191,plain,(
% 2.82/0.75    ~sP2(sK6) | spl12_1),
% 2.82/0.75    inference(avatar_component_clause,[],[f189])).
% 2.82/0.75  fof(f195,plain,(
% 2.82/0.75    ~spl12_1 | spl12_2),
% 2.82/0.75    inference(avatar_split_clause,[],[f185,f193,f189])).
% 2.82/0.75  fof(f185,plain,(
% 2.82/0.75    ( ! [X0] : (k1_xboole_0 != X0 | ~sP1(sK6,X0) | ~sP2(sK6)) )),
% 2.82/0.75    inference(superposition,[],[f183,f81])).
% 2.82/0.75  fof(f81,plain,(
% 2.82/0.75    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | ~sP1(X0,X1) | ~sP2(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f43])).
% 2.82/0.75  % SZS output end Proof for theBenchmark
% 2.82/0.75  % (1833)------------------------------
% 2.82/0.75  % (1833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.82/0.75  % (1833)Termination reason: Refutation
% 2.82/0.75  
% 2.82/0.75  % (1833)Memory used [KB]: 7803
% 2.82/0.75  % (1833)Time elapsed: 0.330 s
% 2.82/0.75  % (1833)------------------------------
% 2.82/0.75  % (1833)------------------------------
% 2.82/0.76  % (1805)Success in time 0.39 s
%------------------------------------------------------------------------------
