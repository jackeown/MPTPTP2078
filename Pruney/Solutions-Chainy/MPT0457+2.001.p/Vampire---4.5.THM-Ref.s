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
% DateTime   : Thu Dec  3 12:47:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  85 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :  248 ( 360 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f209,plain,(
    $false ),
    inference(subsumption_resolution,[],[f208,f37])).

fof(f37,plain,(
    ~ r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3))
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f8,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK2,X1)),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK2,X1)),k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3))
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f208,plain,(
    r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3)) ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3))
    | r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3)) ),
    inference(resolution,[],[f197,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f12,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f197,plain,(
    ! [X5] :
      ( r2_hidden(sK8(k2_relat_1(k5_relat_1(sK2,sK3)),X5),k2_relat_1(sK3))
      | r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),X5) ) ),
    inference(resolution,[],[f191,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f191,plain,(
    ! [X10] :
      ( ~ r2_hidden(X10,k2_relat_1(k5_relat_1(sK2,sK3)))
      | r2_hidden(X10,k2_relat_1(sK3)) ) ),
    inference(resolution,[],[f131,f55])).

fof(f55,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f131,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK7(sK3,sK2,sK11(k5_relat_1(sK2,sK3),X1),X1),X1),sK3)
      | ~ r2_hidden(X1,k2_relat_1(k5_relat_1(sK2,sK3))) ) ),
    inference(resolution,[],[f127,f36])).

fof(f36,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(k5_relat_1(sK2,X1)))
      | r2_hidden(k4_tarski(sK7(X1,sK2,sK11(k5_relat_1(sK2,X1),X0),X0),X0),X1) ) ),
    inference(resolution,[],[f76,f35])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,k2_relat_1(k5_relat_1(X1,X0)))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK7(X0,X1,sK11(k5_relat_1(X1,X0),X2),X2),X2),X0) ) ),
    inference(resolution,[],[f66,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f60,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,k5_relat_1(X1,X0))
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f54,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f9,f14,f13])).

fof(f13,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3,X4] :
          ( r2_hidden(k4_tarski(X3,X4),X2)
        <=> ? [X5] :
              ( r2_hidden(k4_tarski(X5,X4),X1)
              & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ( k5_relat_1(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f54,plain,(
    ! [X2,X1] :
      ( ~ sP1(k5_relat_1(X1,X2),X1,X2)
      | sP0(X2,X1,k5_relat_1(X1,X2)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k5_relat_1(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( k5_relat_1(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k5_relat_1(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ( ( k5_relat_1(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k5_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(k4_tarski(sK7(X0,X1,sK11(X2,X3),X3),X3),X0)
      | ~ r2_hidden(X3,k2_relat_1(X2)) ) ),
    inference(resolution,[],[f41,f56])).

fof(f56,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f41,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),X2)
      | r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X0)
                | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X1) )
            | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
          & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X0)
              & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X1) )
            | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) )
      & ( ! [X7,X8] :
            ( ( r2_hidden(k4_tarski(X7,X8),X2)
              | ! [X9] :
                  ( ~ r2_hidden(k4_tarski(X9,X8),X0)
                  | ~ r2_hidden(k4_tarski(X7,X9),X1) ) )
            & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X0)
                & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X1) )
              | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X0)
                | ~ r2_hidden(k4_tarski(X3,X5),X1) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X0)
                & r2_hidden(k4_tarski(X3,X6),X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X0)
              | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X1) )
          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X0)
              & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X1) )
          | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X0)
          & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X1) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X0)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X0)
          & r2_hidden(k4_tarski(X7,X10),X1) )
     => ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X0)
        & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(k4_tarski(X5,X4),X0)
                  | ~ r2_hidden(k4_tarski(X3,X5),X1) )
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ? [X6] :
                  ( r2_hidden(k4_tarski(X6,X4),X0)
                  & r2_hidden(k4_tarski(X3,X6),X1) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X7,X8] :
            ( ( r2_hidden(k4_tarski(X7,X8),X2)
              | ! [X9] :
                  ( ~ r2_hidden(k4_tarski(X9,X8),X0)
                  | ~ r2_hidden(k4_tarski(X7,X9),X1) ) )
            & ( ? [X10] :
                  ( r2_hidden(k4_tarski(X10,X8),X0)
                  & r2_hidden(k4_tarski(X7,X10),X1) )
              | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3,X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                  | ~ r2_hidden(k4_tarski(X3,X5),X0) )
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(k4_tarski(X3,X5),X0) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X2)
              | ! [X5] :
                  ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                  | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(k4_tarski(X3,X5),X0) )
              | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (30534)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.47  % (30548)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.48  % (30534)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f209,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f208,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ~r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    (~r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3)) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f8,f17,f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k5_relat_1(sK2,X1)),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ? [X1] : (~r1_tarski(k2_relat_1(k5_relat_1(sK2,X1)),k2_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3)) & v1_relat_1(sK3))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.20/0.48    inference(negated_conjecture,[],[f5])).
% 0.20/0.48  fof(f5,conjecture,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 0.20/0.48  fof(f208,plain,(
% 0.20/0.48    r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3))),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f207])).
% 0.20/0.48  fof(f207,plain,(
% 0.20/0.48    r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3)) | r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),k2_relat_1(sK3))),
% 0.20/0.48    inference(resolution,[],[f197,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f12,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.20/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.48  fof(f197,plain,(
% 0.20/0.48    ( ! [X5] : (r2_hidden(sK8(k2_relat_1(k5_relat_1(sK2,sK3)),X5),k2_relat_1(sK3)) | r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),X5)) )),
% 0.20/0.48    inference(resolution,[],[f191,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f191,plain,(
% 0.20/0.48    ( ! [X10] : (~r2_hidden(X10,k2_relat_1(k5_relat_1(sK2,sK3))) | r2_hidden(X10,k2_relat_1(sK3))) )),
% 0.20/0.48    inference(resolution,[],[f131,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 0.20/0.48    inference(equality_resolution,[],[f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0) | r2_hidden(sK9(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f30,f33,f32,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0) | r2_hidden(sK9(X0,X1),X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0) => r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK11(X0,X5),X5),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.48    inference(rectify,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    ( ! [X1] : (r2_hidden(k4_tarski(sK7(sK3,sK2,sK11(k5_relat_1(sK2,sK3),X1),X1),X1),sK3) | ~r2_hidden(X1,k2_relat_1(k5_relat_1(sK2,sK3)))) )),
% 0.20/0.48    inference(resolution,[],[f127,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    v1_relat_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,k2_relat_1(k5_relat_1(sK2,X1))) | r2_hidden(k4_tarski(sK7(X1,sK2,sK11(k5_relat_1(sK2,X1),X0),X0),X0),X1)) )),
% 0.20/0.48    inference(resolution,[],[f76,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,k2_relat_1(k5_relat_1(X1,X0))) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK7(X0,X1,sK11(k5_relat_1(X1,X0),X2),X2),X2),X0)) )),
% 0.20/0.48    inference(resolution,[],[f66,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP0(X0,X1,k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f60,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP0(X0,X1,k5_relat_1(X1,X0)) | ~v1_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(resolution,[],[f54,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (sP1(X2,X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(definition_folding,[],[f9,f14,f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0))))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X2,X0,X1] : ((k5_relat_1(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~sP1(k5_relat_1(X1,X2),X1,X2) | sP0(X2,X1,k5_relat_1(X1,X2))) )),
% 0.20/0.49    inference(equality_resolution,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | k5_relat_1(X1,X2) != X0 | ~sP1(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((k5_relat_1(X1,X2) = X0 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k5_relat_1(X1,X2) != X0)) | ~sP1(X0,X1,X2))),
% 0.20/0.49    inference(rectify,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X2,X0,X1] : (((k5_relat_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k5_relat_1(X0,X1) != X2)) | ~sP1(X2,X0,X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f14])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2) | r2_hidden(k4_tarski(sK7(X0,X1,sK11(X2,X3),X3),X3),X0) | ~r2_hidden(X3,k2_relat_1(X2))) )),
% 0.20/0.49    inference(resolution,[],[f41,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.20/0.49    inference(equality_resolution,[],[f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X2,X0,X8,X7,X1] : (~r2_hidden(k4_tarski(X7,X8),X2) | r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X0) | ~sP0(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X0) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X0) & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X1)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X0) | ~r2_hidden(k4_tarski(X7,X9),X1))) & ((r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X0) & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X1)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f22,f25,f24,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X3,X5),X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X0) & r2_hidden(k4_tarski(X3,X6),X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X0) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X0) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X1)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X0) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X1)) => (r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X0) & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X1)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X0) & r2_hidden(k4_tarski(X7,X10),X1)) => (r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X0) & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X1)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X3,X5),X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X0) & r2_hidden(k4_tarski(X3,X6),X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X0) | ~r2_hidden(k4_tarski(X7,X9),X1))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X0) & r2_hidden(k4_tarski(X7,X10),X1)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.49    inference(rectify,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.49    inference(nnf_transformation,[],[f13])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (30534)------------------------------
% 0.20/0.49  % (30534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (30534)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (30534)Memory used [KB]: 6780
% 0.20/0.49  % (30534)Time elapsed: 0.070 s
% 0.20/0.49  % (30534)------------------------------
% 0.20/0.49  % (30534)------------------------------
% 0.20/0.49  % (30526)Success in time 0.131 s
%------------------------------------------------------------------------------
