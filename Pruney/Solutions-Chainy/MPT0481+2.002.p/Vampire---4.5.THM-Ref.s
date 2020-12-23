%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 675 expanded)
%              Number of leaves         :   11 ( 190 expanded)
%              Depth                    :   35
%              Number of atoms          :  210 (2172 expanded)
%              Number of equality atoms :   36 ( 264 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(subsumption_resolution,[],[f96,f80])).

fof(f80,plain,(
    ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f31,f79])).

fof(f79,plain,(
    r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) ),
    inference(subsumption_resolution,[],[f78,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f78,plain,
    ( r2_hidden(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK1)
    | r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) ),
    inference(subsumption_resolution,[],[f77,f30])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)
      | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
          | ~ r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        | ~ r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
          & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f77,plain,
    ( r2_hidden(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK1)
    | ~ v1_relat_1(sK1)
    | r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) ),
    inference(resolution,[],[f72,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),k5_relat_1(X3,k6_relat_1(X4)))
      | r2_hidden(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f40,f69])).

fof(f69,plain,(
    sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))) ),
    inference(subsumption_resolution,[],[f67,f52])).

fof(f52,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)
    | sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))) ),
    inference(subsumption_resolution,[],[f51,f30])).

fof(f51,plain,
    ( sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)))
    | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f50,f32])).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f50,plain,
    ( sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)))
    | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f49,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f49,plain,
    ( ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)))
    | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) ),
    inference(resolution,[],[f48,f31])).

fof(f48,plain,(
    ! [X2,X1] :
      ( r1_tarski(X1,X2)
      | ~ v1_relat_1(X1)
      | sK5(X1,X2) = k4_tarski(sK3(sK5(X1,X2)),sK4(sK5(X1,X2))) ) ),
    inference(resolution,[],[f33,f37])).

fof(f33,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,X0)
      | k4_tarski(sK3(X4),sK4(X4)) = X4
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK2(X0)
          & r2_hidden(sK2(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK3(X4),sK4(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f22,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK2(X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK3(X4),sK4(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f67,plain,
    ( sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)))
    | r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) ),
    inference(resolution,[],[f66,f38])).

fof(f66,plain,
    ( r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK1)
    | sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))) ),
    inference(subsumption_resolution,[],[f65,f52])).

fof(f65,plain,
    ( r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK1)
    | sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)))
    | r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f64,f30])).

fof(f64,plain,
    ( r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK1)
    | ~ v1_relat_1(sK1)
    | sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)))
    | r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) ),
    inference(resolution,[],[f62,f37])).

fof(f62,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),k5_relat_1(k6_relat_1(X9),X10))
      | r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),X10)
      | ~ v1_relat_1(X10)
      | sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))) ) ),
    inference(superposition,[],[f43,f56])).

fof(f56,plain,
    ( sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = k4_tarski(sK3(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK4(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)))
    | sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))) ),
    inference(subsumption_resolution,[],[f55,f32])).

fof(f55,plain,
    ( sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)))
    | sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = k4_tarski(sK3(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK4(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f54,f30])).

fof(f54,plain,
    ( sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)))
    | sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = k4_tarski(sK3(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK4(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(resolution,[],[f53,f36])).

fof(f53,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)))
    | sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = k4_tarski(sK3(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK4(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1))) ),
    inference(resolution,[],[f52,f48])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | r2_hidden(k4_tarski(X0,X1),X3)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | r2_hidden(k4_tarski(X0,X1),X3)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).

fof(f31,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)
    | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f96,plain,(
    r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) ),
    inference(resolution,[],[f95,f38])).

fof(f95,plain,(
    r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK1) ),
    inference(subsumption_resolution,[],[f94,f80])).

fof(f94,plain,
    ( r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK1)
    | r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f93,f30])).

fof(f93,plain,
    ( r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK1)
    | ~ v1_relat_1(sK1)
    | r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) ),
    inference(resolution,[],[f91,f37])).

fof(f91,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),k5_relat_1(k6_relat_1(X9),X10))
      | r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),X10)
      | ~ v1_relat_1(X10) ) ),
    inference(superposition,[],[f43,f85])).

fof(f85,plain,(
    sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = k4_tarski(sK3(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK4(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1))) ),
    inference(subsumption_resolution,[],[f84,f32])).

fof(f84,plain,
    ( sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = k4_tarski(sK3(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK4(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f83,f30])).

fof(f83,plain,
    ( sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = k4_tarski(sK3(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK4(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(resolution,[],[f81,f36])).

fof(f81,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = k4_tarski(sK3(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK4(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1))) ),
    inference(resolution,[],[f80,f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:59:46 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (22277)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.47  % (22261)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.47  % (22261)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f96,f80])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    ~r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f31,f79])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f78,f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.22/0.47    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    r2_hidden(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK1) | r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f77,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    v1_relat_1(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    (~r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) | ~r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)) & v1_relat_1(sK1)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ? [X0,X1] : ((~r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) & v1_relat_1(X1)) => ((~r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) | ~r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)) & v1_relat_1(sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0,X1] : ((~r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) & v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.22/0.47    inference(negated_conjecture,[],[f7])).
% 0.22/0.47  fof(f7,conjecture,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    r2_hidden(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK1) | ~v1_relat_1(sK1) | r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),
% 0.22/0.47    inference(resolution,[],[f72,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f25])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    ( ! [X4,X3] : (~r2_hidden(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),k5_relat_1(X3,k6_relat_1(X4))) | r2_hidden(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),X3) | ~v1_relat_1(X3)) )),
% 0.22/0.47    inference(superposition,[],[f40,f69])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)))),
% 0.22/0.47    inference(subsumption_resolution,[],[f67,f52])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ~r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) | sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)))),
% 0.22/0.47    inference(subsumption_resolution,[],[f51,f30])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))) | ~r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) | ~v1_relat_1(sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f50,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))) | ~r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK1)),
% 0.22/0.47    inference(resolution,[],[f49,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) | sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))) | ~r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),
% 0.22/0.47    inference(resolution,[],[f48,f31])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ( ! [X2,X1] : (r1_tarski(X1,X2) | ~v1_relat_1(X1) | sK5(X1,X2) = k4_tarski(sK3(sK5(X1,X2)),sK4(sK5(X1,X2)))) )),
% 0.22/0.47    inference(resolution,[],[f33,f37])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X4,X0] : (~r2_hidden(X4,X0) | k4_tarski(sK3(X4),sK4(X4)) = X4 | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK2(X0) & r2_hidden(sK2(X0),X0))) & (! [X4] : (k4_tarski(sK3(X4),sK4(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f22,f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK2(X0) & r2_hidden(sK2(X0),X0)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK3(X4),sK4(X4)) = X4)),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.22/0.47    inference(rectify,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 0.22/0.47    inference(nnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))) | r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),
% 0.22/0.47    inference(resolution,[],[f66,f38])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK1) | sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)))),
% 0.22/0.47    inference(subsumption_resolution,[],[f65,f52])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK1) | sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))) | r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f64,f30])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK1) | ~v1_relat_1(sK1) | sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))) | r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),
% 0.22/0.47    inference(resolution,[],[f62,f37])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    ( ! [X10,X9] : (~r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),k5_relat_1(k6_relat_1(X9),X10)) | r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),X10) | ~v1_relat_1(X10) | sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)))) )),
% 0.22/0.47    inference(superposition,[],[f43,f56])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = k4_tarski(sK3(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK4(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1))) | sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)))),
% 0.22/0.47    inference(subsumption_resolution,[],[f55,f32])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))) | sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = k4_tarski(sK3(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK4(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1))) | ~v1_relat_1(k6_relat_1(sK0))),
% 0.22/0.47    inference(subsumption_resolution,[],[f54,f30])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))) | sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = k4_tarski(sK3(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK4(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(sK0))),
% 0.22/0.47    inference(resolution,[],[f53,f36])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = k4_tarski(sK3(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK4(sK5(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))) | sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = k4_tarski(sK3(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK4(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)))),
% 0.22/0.47    inference(resolution,[],[f52,f48])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | r2_hidden(k4_tarski(X0,X1),X3) | ~v1_relat_1(X3)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 0.22/0.47    inference(flattening,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 0.22/0.47    inference(nnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) | ~v1_relat_1(X3))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | r2_hidden(k4_tarski(X0,X1),X3) | ~v1_relat_1(X3)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 0.22/0.47    inference(flattening,[],[f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 0.22/0.47    inference(nnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))) | ~v1_relat_1(X3))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ~r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) | ~r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f96,plain,(
% 0.22/0.47    r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),
% 0.22/0.47    inference(resolution,[],[f95,f38])).
% 0.22/0.47  fof(f95,plain,(
% 0.22/0.47    r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f94,f80])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK1) | r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f93,f30])).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK1) | ~v1_relat_1(sK1) | r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),
% 0.22/0.47    inference(resolution,[],[f91,f37])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    ( ! [X10,X9] : (~r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),k5_relat_1(k6_relat_1(X9),X10)) | r2_hidden(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1),X10) | ~v1_relat_1(X10)) )),
% 0.22/0.47    inference(superposition,[],[f43,f85])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = k4_tarski(sK3(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK4(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)))),
% 0.22/0.48    inference(subsumption_resolution,[],[f84,f32])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = k4_tarski(sK3(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK4(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1))) | ~v1_relat_1(k6_relat_1(sK0))),
% 0.22/0.48    inference(subsumption_resolution,[],[f83,f30])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = k4_tarski(sK3(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK4(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(sK0))),
% 0.22/0.48    inference(resolution,[],[f81,f36])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = k4_tarski(sK3(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK4(sK5(k5_relat_1(k6_relat_1(sK0),sK1),sK1)))),
% 0.22/0.48    inference(resolution,[],[f80,f48])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (22261)------------------------------
% 0.22/0.48  % (22261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22261)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.49  % (22261)Memory used [KB]: 6268
% 0.22/0.49  % (22261)Time elapsed: 0.060 s
% 0.22/0.49  % (22261)------------------------------
% 0.22/0.49  % (22261)------------------------------
% 0.22/0.49  % (22253)Success in time 0.124 s
%------------------------------------------------------------------------------
