%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 218 expanded)
%              Number of leaves         :   14 (  72 expanded)
%              Depth                    :   21
%              Number of atoms          :  387 (1515 expanded)
%              Number of equality atoms :   71 ( 360 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f198,f203])).

fof(f203,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f168,f66])).

fof(f66,plain,
    ( spl6_1
  <=> sP0(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f168,plain,(
    sP0(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[],[f163,f35])).

fof(f35,plain,(
    k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ v2_funct_1(sK2)
    & k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK3)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f10,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK2)
      & ? [X1] :
          ( k5_relat_1(sK2,X1) = k6_relat_1(k1_relat_1(sK2))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( k5_relat_1(sK2,X1) = k6_relat_1(k1_relat_1(sK2))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK3)
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ? [X1] :
              ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & v1_funct_1(X1)
              & v1_relat_1(X1) )
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(f163,plain,(
    ! [X1] : sP0(k6_relat_1(X1)) ),
    inference(subsumption_resolution,[],[f162,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_1(sK4(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK4(X0) != sK5(X0)
          & k5_relat_1(sK4(X0),X0) = k5_relat_1(sK5(X0),X0)
          & k1_relat_1(sK4(X0)) = k1_relat_1(sK5(X0))
          & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0))
          & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0))
          & v1_funct_1(sK5(X0))
          & v1_relat_1(sK5(X0))
          & v1_funct_1(sK4(X0))
          & v1_relat_1(sK4(X0)) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( X3 = X4
                | k5_relat_1(X3,X0) != k5_relat_1(X4,X0)
                | k1_relat_1(X3) != k1_relat_1(X4)
                | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X0))
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f29,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
              & k1_relat_1(X1) = k1_relat_1(X2)
              & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
              & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( sK4(X0) != X2
            & k5_relat_1(X2,X0) = k5_relat_1(sK4(X0),X0)
            & k1_relat_1(X2) = k1_relat_1(sK4(X0))
            & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
            & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0))
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK4(X0) != X2
          & k5_relat_1(X2,X0) = k5_relat_1(sK4(X0),X0)
          & k1_relat_1(X2) = k1_relat_1(sK4(X0))
          & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
          & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( sK4(X0) != sK5(X0)
        & k5_relat_1(sK4(X0),X0) = k5_relat_1(sK5(X0),X0)
        & k1_relat_1(sK4(X0)) = k1_relat_1(sK5(X0))
        & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0))
        & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0))
        & v1_funct_1(sK5(X0))
        & v1_relat_1(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                & k1_relat_1(X1) = k1_relat_1(X2)
                & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( X3 = X4
                | k5_relat_1(X3,X0) != k5_relat_1(X4,X0)
                | k1_relat_1(X3) != k1_relat_1(X4)
                | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X0))
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                & k1_relat_1(X1) = k1_relat_1(X2)
                & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) ) )
      & ( ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
              | k1_relat_1(X1) != k1_relat_1(X2)
              | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
              | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f162,plain,(
    ! [X1] :
      ( sP0(k6_relat_1(X1))
      | ~ v1_relat_1(sK4(k6_relat_1(X1))) ) ),
    inference(subsumption_resolution,[],[f161,f63])).

fof(f63,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK4(k6_relat_1(X0))),X0)
      | sP0(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f48,f39])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f48,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f161,plain,(
    ! [X1] :
      ( sP0(k6_relat_1(X1))
      | ~ r1_tarski(k2_relat_1(sK4(k6_relat_1(X1))),X1)
      | ~ v1_relat_1(sK4(k6_relat_1(X1))) ) ),
    inference(subsumption_resolution,[],[f159,f52])).

fof(f52,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f159,plain,(
    ! [X1] :
      ( sK4(k6_relat_1(X1)) = sK5(k6_relat_1(X1))
      | sP0(k6_relat_1(X1))
      | ~ r1_tarski(k2_relat_1(sK4(k6_relat_1(X1))),X1)
      | ~ v1_relat_1(sK4(k6_relat_1(X1))) ) ),
    inference(superposition,[],[f94,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f94,plain,(
    ! [X0] :
      ( sK5(k6_relat_1(X0)) = k5_relat_1(sK4(k6_relat_1(X0)),k6_relat_1(X0))
      | sP0(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f93,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_relat_1(sK5(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,(
    ! [X0] :
      ( sK5(k6_relat_1(X0)) = k5_relat_1(sK4(k6_relat_1(X0)),k6_relat_1(X0))
      | ~ v1_relat_1(sK5(k6_relat_1(X0)))
      | sP0(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f91,f74])).

fof(f74,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK5(k6_relat_1(X0))),X0)
      | sP0(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f49,f39])).

fof(f49,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,(
    ! [X0] :
      ( sK5(k6_relat_1(X0)) = k5_relat_1(sK4(k6_relat_1(X0)),k6_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(sK5(k6_relat_1(X0))),X0)
      | ~ v1_relat_1(sK5(k6_relat_1(X0)))
      | sP0(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f56,f51])).

fof(f51,plain,(
    ! [X0] :
      ( k5_relat_1(sK4(X0),X0) = k5_relat_1(sK5(X0),X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f198,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f196,f33])).

fof(f33,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f196,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f195,f34])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f195,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f194,f31])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f194,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f193,f32])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f193,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f192,f83])).

fof(f83,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f82,f58])).

fof(f58,plain,(
    v1_funct_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[],[f38,f35])).

fof(f38,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f82,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f81,f57])).

fof(f57,plain,(
    v1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[],[f37,f35])).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f81,plain,
    ( ~ v1_relat_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl6_1 ),
    inference(resolution,[],[f61,f68])).

fof(f68,plain,
    ( sP0(k5_relat_1(sK2,sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f61,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(resolution,[],[f53,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f53,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f12,f20,f19])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                    & k1_relat_1(X1) = k1_relat_1(X2)
                    & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                    & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) )
                 => X1 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).

fof(f192,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f191,f36])).

fof(f36,plain,(
    ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f191,plain,
    ( v2_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f190,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | v2_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

fof(f190,plain,(
    r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f189,f33])).

fof(f189,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f188,f34])).

fof(f188,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f187,f31])).

fof(f187,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f176,f32])).

fof(f176,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f175])).

fof(f175,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f54,f59])).

fof(f59,plain,(
    k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[],[f39,f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (8414)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (8420)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (8410)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (8418)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (8414)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f198,f203])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f168,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl6_1 <=> sP0(k5_relat_1(sK2,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    sP0(k5_relat_1(sK2,sK3))),
% 0.21/0.50    inference(superposition,[],[f163,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ~v2_funct_1(sK2) & (k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK3) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f10,f23,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X0] : (~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v2_funct_1(sK2) & ? [X1] : (k5_relat_1(sK2,X1) = k6_relat_1(k1_relat_1(sK2)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ? [X1] : (k5_relat_1(sK2,X1) = k6_relat_1(k1_relat_1(sK2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK3) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0] : (~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0] : ((~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ( ! [X1] : (sP0(k6_relat_1(X1))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f162,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(sK4(X0)) | sP0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : ((sP0(X0) | ((sK4(X0) != sK5(X0) & k5_relat_1(sK4(X0),X0) = k5_relat_1(sK5(X0),X0) & k1_relat_1(sK4(X0)) = k1_relat_1(sK5(X0)) & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0)) & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0))) & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))) & (! [X3] : (! [X4] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~sP0(X0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f29,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (sK4(X0) != X2 & k5_relat_1(X2,X0) = k5_relat_1(sK4(X0),X0) & k1_relat_1(X2) = k1_relat_1(sK4(X0)) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (? [X2] : (sK4(X0) != X2 & k5_relat_1(X2,X0) = k5_relat_1(sK4(X0),X0) & k1_relat_1(X2) = k1_relat_1(sK4(X0)) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) => (sK4(X0) != sK5(X0) & k5_relat_1(sK4(X0),X0) = k5_relat_1(sK5(X0),X0) & k1_relat_1(sK4(X0)) = k1_relat_1(sK5(X0)) & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0)) & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))) & (! [X3] : (! [X4] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~sP0(X0)))),
% 0.21/0.50    inference(rectify,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))) & (! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~sP0(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ( ! [X1] : (sP0(k6_relat_1(X1)) | ~v1_relat_1(sK4(k6_relat_1(X1)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f161,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k2_relat_1(sK4(k6_relat_1(X0))),X0) | sP0(k6_relat_1(X0))) )),
% 0.21/0.50    inference(superposition,[],[f48,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0)) | sP0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ( ! [X1] : (sP0(k6_relat_1(X1)) | ~r1_tarski(k2_relat_1(sK4(k6_relat_1(X1))),X1) | ~v1_relat_1(sK4(k6_relat_1(X1)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f159,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0] : (sK4(X0) != sK5(X0) | sP0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ( ! [X1] : (sK4(k6_relat_1(X1)) = sK5(k6_relat_1(X1)) | sP0(k6_relat_1(X1)) | ~r1_tarski(k2_relat_1(sK4(k6_relat_1(X1))),X1) | ~v1_relat_1(sK4(k6_relat_1(X1)))) )),
% 0.21/0.50    inference(superposition,[],[f94,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X0] : (sK5(k6_relat_1(X0)) = k5_relat_1(sK4(k6_relat_1(X0)),k6_relat_1(X0)) | sP0(k6_relat_1(X0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f93,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(sK5(X0)) | sP0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X0] : (sK5(k6_relat_1(X0)) = k5_relat_1(sK4(k6_relat_1(X0)),k6_relat_1(X0)) | ~v1_relat_1(sK5(k6_relat_1(X0))) | sP0(k6_relat_1(X0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f91,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k2_relat_1(sK5(k6_relat_1(X0))),X0) | sP0(k6_relat_1(X0))) )),
% 0.21/0.50    inference(superposition,[],[f49,f39])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0)) | sP0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X0] : (sK5(k6_relat_1(X0)) = k5_relat_1(sK4(k6_relat_1(X0)),k6_relat_1(X0)) | ~r1_tarski(k2_relat_1(sK5(k6_relat_1(X0))),X0) | ~v1_relat_1(sK5(k6_relat_1(X0))) | sP0(k6_relat_1(X0))) )),
% 0.21/0.50    inference(superposition,[],[f56,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0] : (k5_relat_1(sK4(X0),X0) = k5_relat_1(sK5(X0),X0) | sP0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    ~spl6_1),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f197])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    $false | ~spl6_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f196,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    v1_relat_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    ~v1_relat_1(sK3) | ~spl6_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f195,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl6_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f194,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    v1_relat_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl6_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f193,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl6_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f192,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    v2_funct_1(k5_relat_1(sK2,sK3)) | ~spl6_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f82,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    v1_funct_1(k5_relat_1(sK2,sK3))),
% 0.21/0.50    inference(superposition,[],[f38,f35])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ~v1_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(k5_relat_1(sK2,sK3)) | ~spl6_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f81,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    v1_relat_1(k5_relat_1(sK2,sK3))),
% 0.21/0.50    inference(superposition,[],[f37,f35])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ~v1_relat_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(k5_relat_1(sK2,sK3)) | ~spl6_1),
% 0.21/0.50    inference(resolution,[],[f61,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    sP0(k5_relat_1(sK2,sK3)) | ~spl6_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f66])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0] : (~sP0(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | v2_funct_1(X0)) )),
% 0.21/0.50    inference(resolution,[],[f53,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(definition_folding,[],[f12,f20,f19])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : ((X1 = X2 | (k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) => X1 = X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f191,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ~v2_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    v2_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.50    inference(resolution,[],[f190,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3))),
% 0.21/0.50    inference(subsumption_resolution,[],[f189,f33])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f188,f34])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f187,f31])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f176,f32])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f175])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    k1_relat_1(sK2) != k1_relat_1(sK2) | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.50    inference(superposition,[],[f54,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK3))),
% 0.21/0.50    inference(superposition,[],[f39,f35])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (8414)------------------------------
% 0.21/0.50  % (8414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8414)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (8414)Memory used [KB]: 6268
% 0.21/0.50  % (8414)Time elapsed: 0.096 s
% 0.21/0.50  % (8414)------------------------------
% 0.21/0.50  % (8414)------------------------------
% 0.21/0.50  % (8409)Success in time 0.145 s
%------------------------------------------------------------------------------
