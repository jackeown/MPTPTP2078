%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 251 expanded)
%              Number of leaves         :   14 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :  236 ( 884 expanded)
%              Number of equality atoms :   16 (  76 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f374,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f31,f361,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f38,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f361,plain,(
    ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))) ),
    inference(resolution,[],[f333,f139])).

fof(f139,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)),sK3)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))) ),
    inference(subsumption_resolution,[],[f138,f31])).

fof(f138,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)),sK3)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f137,f53])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f35,f51])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f137,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)),sK3)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)),sK3)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))) ),
    inference(resolution,[],[f97,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f97,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))),k3_relat_1(sK2))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)),sK3)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))) ),
    inference(subsumption_resolution,[],[f95,f32])).

fof(f32,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k3_relat_1(sK2),k3_relat_1(sK3)))
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f11,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK2,X1)),k3_xboole_0(k3_relat_1(sK2),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK2,X1)),k3_xboole_0(k3_relat_1(sK2),k3_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k3_relat_1(sK2),k3_relat_1(sK3)))
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(f95,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))),k3_relat_1(sK2))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)),sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))) ),
    inference(resolution,[],[f75,f34])).

fof(f75,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))),k3_relat_1(sK3))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))),k3_relat_1(sK2)) ),
    inference(resolution,[],[f52,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f51])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f52,plain,(
    ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))),k1_setfam_1(k2_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),k3_relat_1(sK2),k3_relat_1(sK3)))) ),
    inference(definition_unfolding,[],[f33,f51,f51])).

fof(f33,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k3_relat_1(sK2),k3_relat_1(sK3))) ),
    inference(cnf_transformation,[],[f22])).

fof(f333,plain,(
    ! [X12,X11] : r1_tarski(k1_setfam_1(k2_enumset1(X11,X11,X11,X12)),X12) ),
    inference(resolution,[],[f284,f66])).

fof(f66,plain,(
    ! [X6,X8,X7] :
      ( ~ sP1(X6,X7,X8)
      | r1_tarski(X8,X6) ) ),
    inference(superposition,[],[f53,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f49,f51])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f18,f17])).

fof(f17,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f284,plain,(
    ! [X0,X1] : sP1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(subsumption_resolution,[],[f283,f107])).

fof(f107,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK4(X6,X7,X7),X6)
      | sP1(X6,X7,X7) ) ),
    inference(subsumption_resolution,[],[f104,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | sP1(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X1) ) ),
    inference(resolution,[],[f43,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,sK4(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sP0(X1,sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sP0(X1,sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f104,plain,(
    ! [X6,X7] :
      ( sP1(X6,X7,X7)
      | ~ r2_hidden(sK4(X6,X7,X7),X7)
      | ~ r2_hidden(sK4(X6,X7,X7),X6) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X6,X7] :
      ( sP1(X6,X7,X7)
      | ~ r2_hidden(sK4(X6,X7,X7),X7)
      | ~ r2_hidden(sK4(X6,X7,X7),X6)
      | sP1(X6,X7,X7) ) ),
    inference(resolution,[],[f72,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X1)
      | sP1(X0,X1,X1) ) ),
    inference(factoring,[],[f69])).

fof(f72,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK4(X3,X4,X5),X5)
      | sP1(X3,X4,X5)
      | ~ r2_hidden(sK4(X3,X4,X5),X4)
      | ~ r2_hidden(sK4(X3,X4,X5),X3) ) ),
    inference(resolution,[],[f44,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,sK4(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f283,plain,(
    ! [X0,X1] :
      ( sP1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))
      | r2_hidden(sK4(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),X0) ) ),
    inference(duplicate_literal_removal,[],[f276])).

fof(f276,plain,(
    ! [X0,X1] :
      ( sP1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))
      | r2_hidden(sK4(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),X0)
      | sP1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ) ),
    inference(resolution,[],[f150,f107])).

fof(f150,plain,(
    ! [X4,X2,X5,X3] :
      ( r2_hidden(sK4(X2,X3,k1_setfam_1(k2_enumset1(X4,X4,X4,X5))),X5)
      | sP1(X2,X3,k1_setfam_1(k2_enumset1(X4,X4,X4,X5)))
      | r2_hidden(sK4(X2,X3,k1_setfam_1(k2_enumset1(X4,X4,X4,X5))),X2) ) ),
    inference(resolution,[],[f89,f46])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,sK4(X0,X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),X2)
      | r2_hidden(sK4(X0,X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),X0)
      | sP1(X0,X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) ) ),
    inference(resolution,[],[f70,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | sP0(X2,X0,X1) ) ),
    inference(resolution,[],[f41,f58])).

fof(f58,plain,(
    ! [X0,X1] : sP1(X0,X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK4(X3,X4,X5),X5)
      | sP1(X3,X4,X5)
      | r2_hidden(sK4(X3,X4,X5),X3) ) ),
    inference(resolution,[],[f43,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (32219)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (32226)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (32226)Refutation not found, incomplete strategy% (32226)------------------------------
% 0.21/0.51  % (32226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32242)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (32226)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32226)Memory used [KB]: 10618
% 0.21/0.52  % (32226)Time elapsed: 0.102 s
% 0.21/0.52  % (32226)------------------------------
% 0.21/0.52  % (32226)------------------------------
% 0.21/0.53  % (32224)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (32223)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (32223)Refutation not found, incomplete strategy% (32223)------------------------------
% 0.21/0.53  % (32223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32223)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32223)Memory used [KB]: 6140
% 0.21/0.53  % (32223)Time elapsed: 0.079 s
% 0.21/0.53  % (32223)------------------------------
% 0.21/0.53  % (32223)------------------------------
% 0.21/0.53  % (32221)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (32222)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (32236)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (32230)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (32247)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (32232)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (32220)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (32220)Refutation not found, incomplete strategy% (32220)------------------------------
% 0.21/0.54  % (32220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32220)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32220)Memory used [KB]: 10618
% 0.21/0.54  % (32220)Time elapsed: 0.137 s
% 0.21/0.54  % (32220)------------------------------
% 0.21/0.54  % (32220)------------------------------
% 0.21/0.54  % (32247)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (32231)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (32246)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (32245)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (32225)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (32240)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (32233)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (32229)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (32238)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (32241)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (32238)Refutation not found, incomplete strategy% (32238)------------------------------
% 0.21/0.56  % (32238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32238)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32238)Memory used [KB]: 10746
% 0.21/0.56  % (32238)Time elapsed: 0.139 s
% 0.21/0.56  % (32238)------------------------------
% 0.21/0.56  % (32238)------------------------------
% 0.21/0.56  % (32235)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (32235)Refutation not found, incomplete strategy% (32235)------------------------------
% 0.21/0.56  % (32235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32235)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32235)Memory used [KB]: 10618
% 0.21/0.56  % (32235)Time elapsed: 0.149 s
% 0.21/0.56  % (32235)------------------------------
% 0.21/0.56  % (32235)------------------------------
% 0.21/0.56  % (32244)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (32218)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.54/0.56  % (32239)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.54/0.56  % (32243)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.54/0.56  % (32239)Refutation not found, incomplete strategy% (32239)------------------------------
% 1.54/0.56  % (32239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (32239)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (32239)Memory used [KB]: 1663
% 1.54/0.56  % (32239)Time elapsed: 0.134 s
% 1.54/0.56  % (32239)------------------------------
% 1.54/0.56  % (32239)------------------------------
% 1.54/0.56  % (32228)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.54/0.57  % (32227)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.54/0.57  % (32237)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.54/0.57  % (32234)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.54/0.57  % SZS output start Proof for theBenchmark
% 1.54/0.57  fof(f374,plain,(
% 1.54/0.57    $false),
% 1.54/0.57    inference(unit_resulting_resolution,[],[f31,f361,f54])).
% 1.54/0.57  fof(f54,plain,(
% 1.54/0.57    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(definition_unfolding,[],[f38,f51])).
% 1.54/0.57  fof(f51,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.54/0.57    inference(definition_unfolding,[],[f36,f50])).
% 1.54/0.57  fof(f50,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.54/0.57    inference(definition_unfolding,[],[f37,f39])).
% 1.54/0.57  fof(f39,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f5])).
% 1.54/0.57  fof(f5,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.54/0.57  fof(f37,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f4])).
% 1.54/0.57  fof(f4,axiom,(
% 1.54/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.54/0.57  fof(f36,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f6])).
% 1.54/0.57  fof(f6,axiom,(
% 1.54/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.54/0.57  fof(f38,plain,(
% 1.54/0.57    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f14])).
% 1.54/0.57  fof(f14,plain,(
% 1.54/0.57    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.54/0.57    inference(ennf_transformation,[],[f7])).
% 1.54/0.57  fof(f7,axiom,(
% 1.54/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.54/0.57  fof(f361,plain,(
% 1.54/0.57    ~v1_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)))),
% 1.54/0.57    inference(resolution,[],[f333,f139])).
% 1.54/0.57  fof(f139,plain,(
% 1.54/0.57    ~r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)),sK3) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)))),
% 1.54/0.57    inference(subsumption_resolution,[],[f138,f31])).
% 1.54/0.57  fof(f138,plain,(
% 1.54/0.57    ~r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)),sK3) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))) | ~v1_relat_1(sK2)),
% 1.54/0.57    inference(subsumption_resolution,[],[f137,f53])).
% 1.54/0.57  fof(f53,plain,(
% 1.54/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 1.54/0.57    inference(definition_unfolding,[],[f35,f51])).
% 1.54/0.57  fof(f35,plain,(
% 1.54/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f2])).
% 1.54/0.57  fof(f2,axiom,(
% 1.54/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.54/0.57  fof(f137,plain,(
% 1.54/0.57    ~r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)),sK3) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)),sK2) | ~v1_relat_1(sK2)),
% 1.54/0.57    inference(duplicate_literal_removal,[],[f135])).
% 1.54/0.57  fof(f135,plain,(
% 1.54/0.57    ~r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)),sK3) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)),sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)))),
% 1.54/0.57    inference(resolution,[],[f97,f34])).
% 1.54/0.57  fof(f34,plain,(
% 1.54/0.57    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f13])).
% 1.54/0.57  fof(f13,plain,(
% 1.54/0.57    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.54/0.57    inference(flattening,[],[f12])).
% 1.54/0.57  fof(f12,plain,(
% 1.54/0.57    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.54/0.57    inference(ennf_transformation,[],[f8])).
% 1.54/0.57  fof(f8,axiom,(
% 1.54/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 1.54/0.57  fof(f97,plain,(
% 1.54/0.57    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))),k3_relat_1(sK2)) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)),sK3) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)))),
% 1.54/0.57    inference(subsumption_resolution,[],[f95,f32])).
% 1.54/0.57  fof(f32,plain,(
% 1.54/0.57    v1_relat_1(sK3)),
% 1.54/0.57    inference(cnf_transformation,[],[f22])).
% 1.54/0.57  fof(f22,plain,(
% 1.54/0.57    (~r1_tarski(k3_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k3_relat_1(sK2),k3_relat_1(sK3))) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 1.54/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f11,f21,f20])).
% 1.54/0.57  fof(f20,plain,(
% 1.54/0.57    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK2,X1)),k3_xboole_0(k3_relat_1(sK2),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f21,plain,(
% 1.54/0.57    ? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK2,X1)),k3_xboole_0(k3_relat_1(sK2),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k3_relat_1(sK2),k3_relat_1(sK3))) & v1_relat_1(sK3))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f11,plain,(
% 1.54/0.57    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.54/0.57    inference(ennf_transformation,[],[f10])).
% 1.54/0.57  fof(f10,negated_conjecture,(
% 1.54/0.57    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.54/0.57    inference(negated_conjecture,[],[f9])).
% 1.54/0.57  fof(f9,conjecture,(
% 1.54/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).
% 1.54/0.57  fof(f95,plain,(
% 1.54/0.57    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))),k3_relat_1(sK2)) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)),sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)))),
% 1.54/0.57    inference(resolution,[],[f75,f34])).
% 1.54/0.57  fof(f75,plain,(
% 1.54/0.57    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))),k3_relat_1(sK3)) | ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))),k3_relat_1(sK2))),
% 1.54/0.57    inference(resolution,[],[f52,f55])).
% 1.54/0.57  fof(f55,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.54/0.57    inference(definition_unfolding,[],[f40,f51])).
% 1.54/0.57  fof(f40,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f16])).
% 1.54/0.57  fof(f16,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.54/0.57    inference(flattening,[],[f15])).
% 1.54/0.57  fof(f15,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.54/0.57    inference(ennf_transformation,[],[f3])).
% 1.54/0.57  fof(f3,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.54/0.57  fof(f52,plain,(
% 1.54/0.57    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))),k1_setfam_1(k2_enumset1(k3_relat_1(sK2),k3_relat_1(sK2),k3_relat_1(sK2),k3_relat_1(sK3))))),
% 1.54/0.57    inference(definition_unfolding,[],[f33,f51,f51])).
% 1.54/0.57  fof(f33,plain,(
% 1.54/0.57    ~r1_tarski(k3_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k3_relat_1(sK2),k3_relat_1(sK3)))),
% 1.54/0.57    inference(cnf_transformation,[],[f22])).
% 1.54/0.57  fof(f333,plain,(
% 1.54/0.57    ( ! [X12,X11] : (r1_tarski(k1_setfam_1(k2_enumset1(X11,X11,X11,X12)),X12)) )),
% 1.54/0.57    inference(resolution,[],[f284,f66])).
% 1.54/0.57  fof(f66,plain,(
% 1.54/0.57    ( ! [X6,X8,X7] : (~sP1(X6,X7,X8) | r1_tarski(X8,X6)) )),
% 1.54/0.57    inference(superposition,[],[f53,f56])).
% 1.54/0.57  fof(f56,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 | ~sP1(X0,X1,X2)) )),
% 1.54/0.57    inference(definition_unfolding,[],[f49,f51])).
% 1.54/0.57  fof(f49,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f30])).
% 1.54/0.57  fof(f30,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.54/0.57    inference(nnf_transformation,[],[f19])).
% 1.54/0.57  fof(f19,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 1.54/0.57    inference(definition_folding,[],[f1,f18,f17])).
% 1.54/0.57  fof(f17,plain,(
% 1.54/0.57    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 1.54/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.54/0.57  fof(f18,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 1.54/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.54/0.57  fof(f1,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.54/0.57  fof(f284,plain,(
% 1.54/0.57    ( ! [X0,X1] : (sP1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f283,f107])).
% 1.54/0.57  fof(f107,plain,(
% 1.54/0.57    ( ! [X6,X7] : (~r2_hidden(sK4(X6,X7,X7),X6) | sP1(X6,X7,X7)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f104,f69])).
% 1.54/0.57  fof(f69,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | sP1(X0,X1,X2) | r2_hidden(sK4(X0,X1,X2),X1)) )),
% 1.54/0.57    inference(resolution,[],[f43,f46])).
% 1.54/0.57  fof(f46,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f29])).
% 1.54/0.57  fof(f29,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 1.54/0.57    inference(rectify,[],[f28])).
% 1.54/0.57  fof(f28,plain,(
% 1.54/0.57    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.54/0.57    inference(flattening,[],[f27])).
% 1.54/0.57  fof(f27,plain,(
% 1.54/0.57    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.54/0.57    inference(nnf_transformation,[],[f17])).
% 1.54/0.57  fof(f43,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (sP0(X1,sK4(X0,X1,X2),X0) | sP1(X0,X1,X2) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f26])).
% 1.54/0.57  fof(f26,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sP0(X1,sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.54/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 1.54/0.57  fof(f25,plain,(
% 1.54/0.57    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sP0(X1,sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f24,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.54/0.57    inference(rectify,[],[f23])).
% 1.54/0.57  fof(f23,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 1.54/0.57    inference(nnf_transformation,[],[f18])).
% 1.54/0.57  fof(f104,plain,(
% 1.54/0.57    ( ! [X6,X7] : (sP1(X6,X7,X7) | ~r2_hidden(sK4(X6,X7,X7),X7) | ~r2_hidden(sK4(X6,X7,X7),X6)) )),
% 1.54/0.57    inference(duplicate_literal_removal,[],[f100])).
% 1.54/0.57  fof(f100,plain,(
% 1.54/0.57    ( ! [X6,X7] : (sP1(X6,X7,X7) | ~r2_hidden(sK4(X6,X7,X7),X7) | ~r2_hidden(sK4(X6,X7,X7),X6) | sP1(X6,X7,X7)) )),
% 1.54/0.57    inference(resolution,[],[f72,f88])).
% 1.54/0.57  fof(f88,plain,(
% 1.54/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X1) | sP1(X0,X1,X1)) )),
% 1.54/0.57    inference(factoring,[],[f69])).
% 1.54/0.57  fof(f72,plain,(
% 1.54/0.57    ( ! [X4,X5,X3] : (~r2_hidden(sK4(X3,X4,X5),X5) | sP1(X3,X4,X5) | ~r2_hidden(sK4(X3,X4,X5),X4) | ~r2_hidden(sK4(X3,X4,X5),X3)) )),
% 1.54/0.57    inference(resolution,[],[f44,f47])).
% 1.54/0.57  fof(f47,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f29])).
% 1.54/0.57  fof(f44,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~sP0(X1,sK4(X0,X1,X2),X0) | sP1(X0,X1,X2) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f26])).
% 1.54/0.57  fof(f283,plain,(
% 1.54/0.57    ( ! [X0,X1] : (sP1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) | r2_hidden(sK4(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),X0)) )),
% 1.54/0.57    inference(duplicate_literal_removal,[],[f276])).
% 1.54/0.57  fof(f276,plain,(
% 1.54/0.57    ( ! [X0,X1] : (sP1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) | r2_hidden(sK4(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),X0) | sP1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) )),
% 1.54/0.57    inference(resolution,[],[f150,f107])).
% 1.54/0.57  fof(f150,plain,(
% 1.54/0.57    ( ! [X4,X2,X5,X3] : (r2_hidden(sK4(X2,X3,k1_setfam_1(k2_enumset1(X4,X4,X4,X5))),X5) | sP1(X2,X3,k1_setfam_1(k2_enumset1(X4,X4,X4,X5))) | r2_hidden(sK4(X2,X3,k1_setfam_1(k2_enumset1(X4,X4,X4,X5))),X2)) )),
% 1.54/0.57    inference(resolution,[],[f89,f46])).
% 1.54/0.57  fof(f89,plain,(
% 1.54/0.57    ( ! [X2,X0,X3,X1] : (sP0(X3,sK4(X0,X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),X2) | r2_hidden(sK4(X0,X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),X0) | sP1(X0,X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))) )),
% 1.54/0.57    inference(resolution,[],[f70,f61])).
% 1.54/0.57  fof(f61,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | sP0(X2,X0,X1)) )),
% 1.54/0.57    inference(resolution,[],[f41,f58])).
% 1.54/0.57  fof(f58,plain,(
% 1.54/0.57    ( ! [X0,X1] : (sP1(X0,X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.54/0.57    inference(equality_resolution,[],[f57])).
% 1.54/0.57  fof(f57,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 1.54/0.57    inference(definition_unfolding,[],[f48,f51])).
% 1.54/0.57  fof(f48,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.54/0.57    inference(cnf_transformation,[],[f30])).
% 1.54/0.57  fof(f41,plain,(
% 1.54/0.57    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f26])).
% 1.54/0.57  fof(f70,plain,(
% 1.54/0.57    ( ! [X4,X5,X3] : (r2_hidden(sK4(X3,X4,X5),X5) | sP1(X3,X4,X5) | r2_hidden(sK4(X3,X4,X5),X3)) )),
% 1.54/0.57    inference(resolution,[],[f43,f45])).
% 1.54/0.57  fof(f45,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f29])).
% 1.54/0.57  fof(f31,plain,(
% 1.54/0.57    v1_relat_1(sK2)),
% 1.54/0.57    inference(cnf_transformation,[],[f22])).
% 1.54/0.57  % SZS output end Proof for theBenchmark
% 1.54/0.57  % (32247)------------------------------
% 1.54/0.57  % (32247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (32247)Termination reason: Refutation
% 1.54/0.57  
% 1.54/0.57  % (32247)Memory used [KB]: 1918
% 1.54/0.57  % (32247)Time elapsed: 0.093 s
% 1.54/0.57  % (32247)------------------------------
% 1.54/0.57  % (32247)------------------------------
% 1.54/0.58  % (32217)Success in time 0.212 s
%------------------------------------------------------------------------------
