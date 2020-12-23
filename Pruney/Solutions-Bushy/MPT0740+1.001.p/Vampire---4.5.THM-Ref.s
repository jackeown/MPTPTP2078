%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0740+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:34 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 230 expanded)
%              Number of leaves         :   19 (  66 expanded)
%              Depth                    :   18
%              Number of atoms          :  387 (1300 expanded)
%              Number of equality atoms :   25 ( 132 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2012,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2002,f48])).

fof(f48,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ v3_ordinal1(k3_tarski(sK0))
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(k3_tarski(X0))
        & v3_ordinal1(X0) )
   => ( ~ v3_ordinal1(k3_tarski(sK0))
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(k3_tarski(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v3_ordinal1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).

fof(f2002,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f1946,f49])).

fof(f49,plain,(
    ~ v3_ordinal1(k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f1946,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f1938])).

fof(f1938,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f1904,f1256])).

fof(f1256,plain,(
    ! [X0] :
      ( ~ v1_ordinal1(k3_tarski(X0))
      | v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f1238,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_ordinal1(X0)
      | v3_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
    <=> ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_ordinal1)).

fof(f1238,plain,(
    ! [X0] :
      ( v2_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f1237,f1138])).

fof(f1138,plain,(
    ! [X6] :
      ( v3_ordinal1(sK2(k3_tarski(X6)))
      | ~ v3_ordinal1(X6)
      | v2_ordinal1(k3_tarski(X6)) ) ),
    inference(global_subsumption,[],[f175,f184])).

fof(f184,plain,(
    ! [X4] :
      ( ~ v3_ordinal1(sK6(X4,sK2(k3_tarski(X4))))
      | v3_ordinal1(sK2(k3_tarski(X4)))
      | v2_ordinal1(k3_tarski(X4)) ) ),
    inference(resolution,[],[f100,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ( ~ r2_hidden(sK3(X0),sK2(X0))
          & sK2(X0) != sK3(X0)
          & ~ r2_hidden(sK2(X0),sK3(X0))
          & r2_hidden(sK3(X0),X0)
          & r2_hidden(sK2(X0),X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK3(X0),sK2(X0))
        & sK2(X0) != sK3(X0)
        & ~ r2_hidden(sK2(X0),sK3(X0))
        & r2_hidden(sK3(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1,X2] :
            ( r2_hidden(X2,X1)
            | X1 = X2
            | r2_hidden(X1,X2)
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).

fof(f100,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k3_tarski(X3))
      | v3_ordinal1(X2)
      | ~ v3_ordinal1(sK6(X3,X2)) ) ),
    inference(resolution,[],[f80,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f80,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK6(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK6(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK4(X0,X1),X3) )
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( ( r2_hidden(sK5(X0,X1),X0)
              & r2_hidden(sK4(X0,X1),sK5(X0,X1)) )
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK6(X0,X5),X0)
                & r2_hidden(X5,sK6(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f42,f45,f44,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK4(X0,X1),X3) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK4(X0,X1),X4) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK4(X0,X1),X4) )
     => ( r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK6(X0,X5),X0)
        & r2_hidden(X5,sK6(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f175,plain,(
    ! [X4] :
      ( v3_ordinal1(sK6(X4,sK2(k3_tarski(X4))))
      | ~ v3_ordinal1(X4)
      | v2_ordinal1(k3_tarski(X4)) ) ),
    inference(resolution,[],[f97,f57])).

fof(f97,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k3_tarski(X3))
      | v3_ordinal1(sK6(X3,X2))
      | ~ v3_ordinal1(X3) ) ),
    inference(resolution,[],[f79,f65])).

fof(f79,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1237,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v2_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(sK2(k3_tarski(X0))) ) ),
    inference(duplicate_literal_removal,[],[f1228])).

fof(f1228,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v2_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(sK2(k3_tarski(X0)))
      | v2_ordinal1(k3_tarski(X0)) ) ),
    inference(resolution,[],[f1139,f123])).

fof(f123,plain,(
    ! [X8] :
      ( ~ v3_ordinal1(sK3(X8))
      | ~ v3_ordinal1(sK2(X8))
      | v2_ordinal1(X8) ) ),
    inference(subsumption_resolution,[],[f122,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),sK2(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f122,plain,(
    ! [X8] :
      ( r2_hidden(sK3(X8),sK2(X8))
      | ~ v3_ordinal1(sK2(X8))
      | ~ v3_ordinal1(sK3(X8))
      | v2_ordinal1(X8) ) ),
    inference(subsumption_resolution,[],[f115,f60])).

fof(f60,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f115,plain,(
    ! [X8] :
      ( sK3(X8) = sK2(X8)
      | r2_hidden(sK3(X8),sK2(X8))
      | ~ v3_ordinal1(sK2(X8))
      | ~ v3_ordinal1(sK3(X8))
      | v2_ordinal1(X8) ) ),
    inference(resolution,[],[f52,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0),sK3(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f1139,plain,(
    ! [X8] :
      ( v3_ordinal1(sK3(k3_tarski(X8)))
      | ~ v3_ordinal1(X8)
      | v2_ordinal1(k3_tarski(X8)) ) ),
    inference(global_subsumption,[],[f176,f185])).

fof(f185,plain,(
    ! [X5] :
      ( ~ v3_ordinal1(sK6(X5,sK3(k3_tarski(X5))))
      | v3_ordinal1(sK3(k3_tarski(X5)))
      | v2_ordinal1(k3_tarski(X5)) ) ),
    inference(resolution,[],[f100,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f176,plain,(
    ! [X5] :
      ( v3_ordinal1(sK6(X5,sK3(k3_tarski(X5))))
      | ~ v3_ordinal1(X5)
      | v2_ordinal1(k3_tarski(X5)) ) ),
    inference(resolution,[],[f97,f58])).

fof(f1904,plain,(
    ! [X10] :
      ( v1_ordinal1(k3_tarski(X10))
      | ~ v3_ordinal1(X10) ) ),
    inference(global_subsumption,[],[f50,f1866])).

fof(f1866,plain,(
    ! [X3] :
      ( v1_ordinal1(k3_tarski(X3))
      | ~ v1_ordinal1(X3) ) ),
    inference(subsumption_resolution,[],[f1865,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k3_tarski(X0)),X0)
      | v1_ordinal1(k3_tarski(X0)) ) ),
    inference(resolution,[],[f67,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK1(X0),X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK1(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(f1865,plain,(
    ! [X3] :
      ( ~ v1_ordinal1(X3)
      | v1_ordinal1(k3_tarski(X3))
      | r2_hidden(sK1(k3_tarski(X3)),X3) ) ),
    inference(subsumption_resolution,[],[f1805,f102])).

fof(f102,plain,(
    ! [X0] :
      ( v1_ordinal1(k3_tarski(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f98,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f98,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k3_tarski(X5))
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f79,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f1805,plain,(
    ! [X3] :
      ( ~ v1_ordinal1(X3)
      | v1_ordinal1(k3_tarski(X3))
      | v1_xboole_0(X3)
      | r2_hidden(sK1(k3_tarski(X3)),X3) ) ),
    inference(resolution,[],[f1396,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f1396,plain,(
    ! [X3] :
      ( m1_subset_1(sK1(k3_tarski(X3)),X3)
      | ~ v1_ordinal1(X3)
      | v1_ordinal1(k3_tarski(X3)) ) ),
    inference(resolution,[],[f1371,f54])).

fof(f1371,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_tarski(X0))
      | ~ v1_ordinal1(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f1355])).

fof(f1355,plain,(
    ! [X0,X1] :
      ( ~ v1_ordinal1(X0)
      | ~ r2_hidden(X1,k3_tarski(X0))
      | m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,k3_tarski(X0)) ) ),
    inference(resolution,[],[f210,f80])).

fof(f210,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,sK6(X1,X0))
      | ~ v1_ordinal1(X1)
      | ~ r2_hidden(X0,k3_tarski(X1))
      | m1_subset_1(X2,X1) ) ),
    inference(resolution,[],[f96,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f77,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK6(X1,X0),X1)
      | ~ r2_hidden(X0,k3_tarski(X1))
      | ~ v1_ordinal1(X1) ) ),
    inference(resolution,[],[f79,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | r1_tarski(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

%------------------------------------------------------------------------------
