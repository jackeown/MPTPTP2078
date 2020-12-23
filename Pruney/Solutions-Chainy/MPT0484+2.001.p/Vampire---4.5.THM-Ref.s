%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 114 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :   16
%              Number of atoms          :  231 ( 432 expanded)
%              Number of equality atoms :   25 (  67 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(subsumption_resolution,[],[f153,f37])).

fof(f37,plain,(
    sK1 != k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK1 != k5_relat_1(sK1,k6_relat_1(sK0))
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( k5_relat_1(X1,k6_relat_1(X0)) != X1
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( sK1 != k5_relat_1(sK1,k6_relat_1(sK0))
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k2_relat_1(X1),X0)
         => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f153,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(resolution,[],[f128,f36])).

fof(f36,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK1),X0)
      | sK1 = k5_relat_1(sK1,k6_relat_1(X0)) ) ),
    inference(resolution,[],[f108,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X0)))
      | sK1 = k5_relat_1(sK1,k6_relat_1(X0)) ) ),
    inference(resolution,[],[f60,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f60,plain,(
    ! [X0] : r1_tarski(k5_relat_1(sK1,k6_relat_1(X0)),sK1) ),
    inference(resolution,[],[f35,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f108,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X0)))
      | ~ r1_tarski(k2_relat_1(sK1),X0) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X0)))
      | r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X0)))
      | ~ r1_tarski(k2_relat_1(sK1),X0) ) ),
    inference(resolution,[],[f101,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK1,X0),X1)
      | r1_tarski(sK1,X0)
      | ~ r1_tarski(k2_relat_1(sK1),X1) ) ),
    inference(resolution,[],[f77,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f77,plain,(
    ! [X2] :
      ( r2_hidden(sK3(sK1,X2),k2_relat_1(sK1))
      | r1_tarski(sK1,X2) ) ),
    inference(resolution,[],[f62,f58])).

fof(f58,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f62,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK2(sK1,X2),sK3(sK1,X2)),sK1)
      | r1_tarski(sK1,X2) ) ),
    inference(resolution,[],[f35,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f101,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(X4))),X4)
      | r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X4))) ) ),
    inference(subsumption_resolution,[],[f100,f35])).

fof(f100,plain,(
    ! [X4] :
      ( r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X4)))
      | ~ r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(X4))),X4)
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X4] :
      ( r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X4)))
      | ~ r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(X4))),X4)
      | r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X4)))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f81,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(sK1,X0),sK3(sK1,X0)),k5_relat_1(sK1,k6_relat_1(X1)))
      | r1_tarski(sK1,X0)
      | ~ r2_hidden(sK3(sK1,X0),X1) ) ),
    inference(subsumption_resolution,[],[f76,f35])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK1,X0)
      | r2_hidden(k4_tarski(sK2(sK1,X0),sK3(sK1,X0)),k5_relat_1(sK1,k6_relat_1(X1)))
      | ~ r2_hidden(sK3(sK1,X0),X1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f62,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X3)
      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:08:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (15590)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (15585)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (15590)Refutation not found, incomplete strategy% (15590)------------------------------
% 0.22/0.52  % (15590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15583)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (15588)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (15590)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15590)Memory used [KB]: 10746
% 0.22/0.53  % (15590)Time elapsed: 0.101 s
% 0.22/0.53  % (15590)------------------------------
% 0.22/0.53  % (15590)------------------------------
% 0.22/0.53  % (15581)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (15598)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (15586)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (15589)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (15602)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (15607)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (15602)Refutation not found, incomplete strategy% (15602)------------------------------
% 0.22/0.54  % (15602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15602)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (15602)Memory used [KB]: 10746
% 0.22/0.54  % (15602)Time elapsed: 0.089 s
% 0.22/0.54  % (15602)------------------------------
% 0.22/0.54  % (15602)------------------------------
% 0.22/0.55  % (15601)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (15582)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (15584)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (15594)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (15582)Refutation not found, incomplete strategy% (15582)------------------------------
% 0.22/0.55  % (15582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15582)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15582)Memory used [KB]: 10746
% 0.22/0.55  % (15582)Time elapsed: 0.135 s
% 0.22/0.55  % (15582)------------------------------
% 0.22/0.55  % (15582)------------------------------
% 0.22/0.55  % (15592)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (15591)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (15580)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (15603)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (15597)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (15599)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (15608)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (15588)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f156,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f153,f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    sK1 != k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    sK1 != k5_relat_1(sK1,k6_relat_1(sK0)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(sK1)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ? [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) != X1 & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X1)) => (sK1 != k5_relat_1(sK1,k6_relat_1(sK0)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(sK1))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    ? [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) != X1 & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f9])).
% 0.22/0.56  fof(f9,plain,(
% 0.22/0.56    ? [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) != X1 & r1_tarski(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.56    inference(negated_conjecture,[],[f7])).
% 0.22/0.56  fof(f7,conjecture,(
% 0.22/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.56  fof(f153,plain,(
% 0.22/0.56    sK1 = k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.22/0.56    inference(resolution,[],[f128,f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f128,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | sK1 = k5_relat_1(sK1,k6_relat_1(X0))) )),
% 0.22/0.56    inference(resolution,[],[f108,f73])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X0))) | sK1 = k5_relat_1(sK1,k6_relat_1(X0))) )),
% 0.22/0.56    inference(resolution,[],[f60,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.56    inference(flattening,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k5_relat_1(sK1,k6_relat_1(X0)),sK1)) )),
% 0.22/0.56    inference(resolution,[],[f35,f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    v1_relat_1(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X0))) | ~r1_tarski(k2_relat_1(sK1),X0)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f103])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X0))) | r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X0))) | ~r1_tarski(k2_relat_1(sK1),X0)) )),
% 0.22/0.56    inference(resolution,[],[f101,f83])).
% 0.22/0.56  fof(f83,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(sK3(sK1,X0),X1) | r1_tarski(sK1,X0) | ~r1_tarski(k2_relat_1(sK1),X1)) )),
% 0.22/0.56    inference(resolution,[],[f77,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(rectify,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    ( ! [X2] : (r2_hidden(sK3(sK1,X2),k2_relat_1(sK1)) | r1_tarski(sK1,X2)) )),
% 0.22/0.56    inference(resolution,[],[f62,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 0.22/0.56    inference(equality_resolution,[],[f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f28,f31,f30,f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.56    inference(rectify,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X2] : (r2_hidden(k4_tarski(sK2(sK1,X2),sK3(sK1,X2)),sK1) | r1_tarski(sK1,X2)) )),
% 0.22/0.56    inference(resolution,[],[f35,f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(rectify,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(nnf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.22/0.56  fof(f101,plain,(
% 0.22/0.56    ( ! [X4] : (~r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(X4))),X4) | r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X4)))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f100,f35])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    ( ! [X4] : (r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X4))) | ~r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(X4))),X4) | ~v1_relat_1(sK1)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f95])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    ( ! [X4] : (r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X4))) | ~r2_hidden(sK3(sK1,k5_relat_1(sK1,k6_relat_1(X4))),X4) | r1_tarski(sK1,k5_relat_1(sK1,k6_relat_1(X4))) | ~v1_relat_1(sK1)) )),
% 0.22/0.56    inference(resolution,[],[f81,f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(sK1,X0),sK3(sK1,X0)),k5_relat_1(sK1,k6_relat_1(X1))) | r1_tarski(sK1,X0) | ~r2_hidden(sK3(sK1,X0),X1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f76,f35])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(sK1,X0) | r2_hidden(k4_tarski(sK2(sK1,X0),sK3(sK1,X0)),k5_relat_1(sK1,k6_relat_1(X1))) | ~r2_hidden(sK3(sK1,X0),X1) | ~v1_relat_1(sK1)) )),
% 0.22/0.56    inference(resolution,[],[f62,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),X3) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~r2_hidden(X1,X2) | ~v1_relat_1(X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 0.22/0.56    inference(flattening,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 0.22/0.56    inference(nnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))) | ~v1_relat_1(X3))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (15588)------------------------------
% 0.22/0.56  % (15588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15588)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (15588)Memory used [KB]: 10746
% 0.22/0.56  % (15588)Time elapsed: 0.118 s
% 0.22/0.56  % (15588)------------------------------
% 0.22/0.56  % (15588)------------------------------
% 0.22/0.56  % (15579)Success in time 0.192 s
%------------------------------------------------------------------------------
