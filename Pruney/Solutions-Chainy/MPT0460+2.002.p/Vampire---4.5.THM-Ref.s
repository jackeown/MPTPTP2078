%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:24 EST 2020

% Result     : Theorem 3.02s
% Output     : Refutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 229 expanded)
%              Number of leaves         :   15 (  78 expanded)
%              Depth                    :   25
%              Number of atoms          :  336 (1158 expanded)
%              Number of equality atoms :    8 (  27 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1302,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1301,f39])).

fof(f39,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3))
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK4)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f8,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
                & r1_tarski(X0,X1)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X2,sK2),k5_relat_1(X2,X1))
              & r1_tarski(sK2,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(X2,sK2),k5_relat_1(X2,X1))
            & r1_tarski(sK2,X1)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X2,sK2),k5_relat_1(X2,sK3))
          & r1_tarski(sK2,sK3)
          & v1_relat_1(X2) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(X2,sK2),k5_relat_1(X2,sK3))
        & r1_tarski(sK2,sK3)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3))
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              & r1_tarski(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              & r1_tarski(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( r1_tarski(X0,X1)
                 => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

fof(f1301,plain,(
    ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f1300,f37])).

fof(f37,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f1300,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f1299,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f1299,plain,(
    ~ v1_relat_1(k5_relat_1(sK4,sK2)) ),
    inference(subsumption_resolution,[],[f1296,f41])).

fof(f41,plain,(
    ~ r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f1296,plain,
    ( r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3))
    | ~ v1_relat_1(k5_relat_1(sK4,sK2)) ),
    inference(duplicate_literal_removal,[],[f1291])).

fof(f1291,plain,
    ( r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3))
    | r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3))
    | ~ v1_relat_1(k5_relat_1(sK4,sK2)) ),
    inference(resolution,[],[f1289,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f1289,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK9(k5_relat_1(sK4,sK2),X0),sK10(k5_relat_1(sK4,sK2),X0)),k5_relat_1(sK4,sK3))
      | r1_tarski(k5_relat_1(sK4,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f1288,f37])).

fof(f1288,plain,(
    ! [X0] :
      ( r1_tarski(k5_relat_1(sK4,sK2),X0)
      | r2_hidden(k4_tarski(sK9(k5_relat_1(sK4,sK2),X0),sK10(k5_relat_1(sK4,sK2),X0)),k5_relat_1(sK4,sK3))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f1287,f39])).

fof(f1287,plain,(
    ! [X0] :
      ( r1_tarski(k5_relat_1(sK4,sK2),X0)
      | r2_hidden(k4_tarski(sK9(k5_relat_1(sK4,sK2),X0),sK10(k5_relat_1(sK4,sK2),X0)),k5_relat_1(sK4,sK3))
      | ~ v1_relat_1(sK4)
      | ~ v1_relat_1(sK2) ) ),
    inference(duplicate_literal_removal,[],[f1286])).

fof(f1286,plain,(
    ! [X0] :
      ( r1_tarski(k5_relat_1(sK4,sK2),X0)
      | r2_hidden(k4_tarski(sK9(k5_relat_1(sK4,sK2),X0),sK10(k5_relat_1(sK4,sK2),X0)),k5_relat_1(sK4,sK3))
      | ~ v1_relat_1(sK4)
      | ~ v1_relat_1(sK2)
      | r1_tarski(k5_relat_1(sK4,sK2),X0) ) ),
    inference(resolution,[],[f306,f193])).

fof(f193,plain,(
    ! [X8,X9] :
      ( r2_hidden(k4_tarski(sK9(k5_relat_1(sK4,X8),X9),sK8(X8,sK4,sK9(k5_relat_1(sK4,X8),X9),sK10(k5_relat_1(sK4,X8),X9))),sK4)
      | ~ v1_relat_1(X8)
      | r1_tarski(k5_relat_1(sK4,X8),X9) ) ),
    inference(resolution,[],[f101,f39])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK9(k5_relat_1(X0,X1),X2),sK8(X1,X0,sK9(k5_relat_1(X0,X1),X2),sK10(k5_relat_1(X0,X1),X2))),X0) ) ),
    inference(subsumption_resolution,[],[f100,f54])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK9(k5_relat_1(X0,X1),X2),sK8(X1,X0,sK9(k5_relat_1(X0,X1),X2),sK10(k5_relat_1(X0,X1),X2))),X0)
      | r1_tarski(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f80,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f65,f54])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,k5_relat_1(X1,X0))
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f58,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f9,f15,f14])).

fof(f14,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3,X4] :
          ( r2_hidden(k4_tarski(X3,X4),X2)
        <=> ? [X5] :
              ( r2_hidden(k4_tarski(X5,X4),X1)
              & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f58,plain,(
    ! [X2,X1] :
      ( ~ sP1(k5_relat_1(X1,X2),X1,X2)
      | sP0(X2,X1,k5_relat_1(X1,X2)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k5_relat_1(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( k5_relat_1(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k5_relat_1(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ( ( k5_relat_1(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k5_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X2,X3,X0)
      | r2_hidden(k4_tarski(sK9(X0,X1),sK8(X2,X3,sK9(X0,X1),sK10(X0,X1))),X3)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f44,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),X2)
      | r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0)
                | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X1) )
            | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
          & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0)
              & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X1) )
            | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) )
      & ( ! [X7,X8] :
            ( ( r2_hidden(k4_tarski(X7,X8),X2)
              | ! [X9] :
                  ( ~ r2_hidden(k4_tarski(X9,X8),X0)
                  | ~ r2_hidden(k4_tarski(X7,X9),X1) ) )
            & ( ( r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X0)
                & r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X1) )
              | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f24,f27,f26,f25])).

fof(f25,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0)
              | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X1) )
          | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK6(X0,X1,X2)),X0)
              & r2_hidden(k4_tarski(sK5(X0,X1,X2),X6),X1) )
          | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK6(X0,X1,X2)),X0)
          & r2_hidden(k4_tarski(sK5(X0,X1,X2),X6),X1) )
     => ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X0)
          & r2_hidden(k4_tarski(X7,X10),X1) )
     => ( r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X0)
        & r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f306,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(k4_tarski(X3,sK8(sK2,sK4,sK9(k5_relat_1(sK4,sK2),X2),sK10(k5_relat_1(sK4,sK2),X2))),X4)
      | r1_tarski(k5_relat_1(sK4,sK2),X2)
      | r2_hidden(k4_tarski(X3,sK10(k5_relat_1(sK4,sK2),X2)),k5_relat_1(X4,sK3))
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f303,f38])).

fof(f38,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f303,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k5_relat_1(sK4,sK2),X2)
      | ~ r2_hidden(k4_tarski(X3,sK8(sK2,sK4,sK9(k5_relat_1(sK4,sK2),X2),sK10(k5_relat_1(sK4,sK2),X2))),X4)
      | r2_hidden(k4_tarski(X3,sK10(k5_relat_1(sK4,sK2),X2)),k5_relat_1(X4,sK3))
      | ~ v1_relat_1(sK3)
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f300,f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(X3,X0),X4)
      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f46,f66])).

fof(f46,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X0)
      | ~ r2_hidden(k4_tarski(X7,X9),X1)
      | r2_hidden(k4_tarski(X7,X8),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f300,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK8(sK2,sK4,sK9(k5_relat_1(sK4,sK2),X0),sK10(k5_relat_1(sK4,sK2),X0)),sK10(k5_relat_1(sK4,sK2),X0)),sK3)
      | r1_tarski(k5_relat_1(sK4,sK2),X0) ) ),
    inference(resolution,[],[f267,f40])).

fof(f40,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f267,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2,X1)
      | r2_hidden(k4_tarski(sK8(sK2,sK4,sK9(k5_relat_1(sK4,sK2),X0),sK10(k5_relat_1(sK4,sK2),X0)),sK10(k5_relat_1(sK4,sK2),X0)),X1)
      | r1_tarski(k5_relat_1(sK4,sK2),X0) ) ),
    inference(resolution,[],[f264,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
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

fof(f264,plain,(
    ! [X3] :
      ( r2_hidden(k4_tarski(sK8(sK2,sK4,sK9(k5_relat_1(sK4,sK2),X3),sK10(k5_relat_1(sK4,sK2),X3)),sK10(k5_relat_1(sK4,sK2),X3)),sK2)
      | r1_tarski(k5_relat_1(sK4,sK2),X3) ) ),
    inference(resolution,[],[f212,f37])).

fof(f212,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | r2_hidden(k4_tarski(sK8(X8,sK4,sK9(k5_relat_1(sK4,X8),X9),sK10(k5_relat_1(sK4,X8),X9)),sK10(k5_relat_1(sK4,X8),X9)),X8)
      | r1_tarski(k5_relat_1(sK4,X8),X9) ) ),
    inference(resolution,[],[f95,f39])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK8(X0,X1,sK9(k5_relat_1(X1,X0),X2),sK10(k5_relat_1(X1,X0),X2)),sK10(k5_relat_1(X1,X0),X2)),X0)
      | r1_tarski(k5_relat_1(X1,X0),X2) ) ),
    inference(subsumption_resolution,[],[f94,f54])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,sK9(k5_relat_1(X1,X0),X2),sK10(k5_relat_1(X1,X0),X2)),sK10(k5_relat_1(X1,X0),X2)),X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,X0),X2)
      | ~ v1_relat_1(k5_relat_1(X1,X0)) ) ),
    inference(resolution,[],[f92,f52])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | r2_hidden(k4_tarski(sK8(X3,X2,X0,X1),X1),X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f45,f66])).

fof(f45,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X0) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.26/0.52  % (21720)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.26/0.52  % (21712)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.26/0.52  % (21713)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.26/0.52  % (21701)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.26/0.53  % (21696)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.26/0.53  % (21706)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.26/0.53  % (21699)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.26/0.53  % (21720)Refutation not found, incomplete strategy% (21720)------------------------------
% 1.26/0.53  % (21720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (21698)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.53  % (21720)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (21720)Memory used [KB]: 10746
% 1.26/0.53  % (21720)Time elapsed: 0.063 s
% 1.26/0.53  % (21720)------------------------------
% 1.26/0.53  % (21720)------------------------------
% 1.26/0.53  % (21698)Refutation not found, incomplete strategy% (21698)------------------------------
% 1.26/0.53  % (21698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (21698)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (21698)Memory used [KB]: 10618
% 1.26/0.53  % (21698)Time elapsed: 0.125 s
% 1.26/0.53  % (21698)------------------------------
% 1.26/0.53  % (21698)------------------------------
% 1.26/0.53  % (21727)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.54  % (21716)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.54  % (21723)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.54  % (21724)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (21721)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.54  % (21700)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.36/0.54  % (21725)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  % (21719)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.54  % (21714)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.54  % (21717)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.54  % (21714)Refutation not found, incomplete strategy% (21714)------------------------------
% 1.36/0.54  % (21714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (21714)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (21714)Memory used [KB]: 10618
% 1.36/0.54  % (21714)Time elapsed: 0.141 s
% 1.36/0.54  % (21714)------------------------------
% 1.36/0.54  % (21714)------------------------------
% 1.36/0.54  % (21709)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.54  % (21705)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.55  % (21707)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.55  % (21710)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.55  % (21704)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.55  % (21703)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.55  % (21697)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.55  % (21711)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.56  % (21702)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.56  % (21726)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.56  % (21715)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.56  % (21722)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.99/0.65  % (21794)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.99/0.67  % (21793)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.99/0.68  % (21795)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.02/0.79  % (21703)Refutation found. Thanks to Tanya!
% 3.02/0.79  % SZS status Theorem for theBenchmark
% 3.02/0.79  % SZS output start Proof for theBenchmark
% 3.02/0.79  fof(f1302,plain,(
% 3.02/0.79    $false),
% 3.02/0.79    inference(subsumption_resolution,[],[f1301,f39])).
% 3.02/0.79  fof(f39,plain,(
% 3.02/0.79    v1_relat_1(sK4)),
% 3.02/0.79    inference(cnf_transformation,[],[f20])).
% 3.02/0.79  fof(f20,plain,(
% 3.02/0.79    ((~r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK4)) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 3.02/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f8,f19,f18,f17])).
% 3.02/0.79  fof(f17,plain,(
% 3.02/0.79    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X2,sK2),k5_relat_1(X2,X1)) & r1_tarski(sK2,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 3.02/0.79    introduced(choice_axiom,[])).
% 3.02/0.79  fof(f18,plain,(
% 3.02/0.79    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X2,sK2),k5_relat_1(X2,X1)) & r1_tarski(sK2,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(X2,sK2),k5_relat_1(X2,sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(X2)) & v1_relat_1(sK3))),
% 3.02/0.79    introduced(choice_axiom,[])).
% 3.02/0.79  fof(f19,plain,(
% 3.02/0.79    ? [X2] : (~r1_tarski(k5_relat_1(X2,sK2),k5_relat_1(X2,sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK4))),
% 3.02/0.79    introduced(choice_axiom,[])).
% 3.02/0.79  fof(f8,plain,(
% 3.02/0.79    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.02/0.79    inference(flattening,[],[f7])).
% 3.02/0.79  fof(f7,plain,(
% 3.02/0.79    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.02/0.79    inference(ennf_transformation,[],[f6])).
% 3.02/0.79  fof(f6,negated_conjecture,(
% 3.02/0.79    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 3.02/0.79    inference(negated_conjecture,[],[f5])).
% 3.02/0.79  fof(f5,conjecture,(
% 3.02/0.79    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 3.02/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).
% 3.02/0.79  fof(f1301,plain,(
% 3.02/0.79    ~v1_relat_1(sK4)),
% 3.02/0.79    inference(subsumption_resolution,[],[f1300,f37])).
% 3.02/0.79  fof(f37,plain,(
% 3.02/0.79    v1_relat_1(sK2)),
% 3.02/0.79    inference(cnf_transformation,[],[f20])).
% 3.02/0.79  fof(f1300,plain,(
% 3.02/0.79    ~v1_relat_1(sK2) | ~v1_relat_1(sK4)),
% 3.02/0.79    inference(resolution,[],[f1299,f54])).
% 3.02/0.79  fof(f54,plain,(
% 3.02/0.79    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.02/0.79    inference(cnf_transformation,[],[f12])).
% 3.02/0.79  fof(f12,plain,(
% 3.02/0.79    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.02/0.79    inference(flattening,[],[f11])).
% 3.02/0.79  fof(f11,plain,(
% 3.02/0.79    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.02/0.79    inference(ennf_transformation,[],[f4])).
% 3.02/0.79  fof(f4,axiom,(
% 3.02/0.79    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.02/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 3.02/0.79  fof(f1299,plain,(
% 3.02/0.79    ~v1_relat_1(k5_relat_1(sK4,sK2))),
% 3.02/0.79    inference(subsumption_resolution,[],[f1296,f41])).
% 3.02/0.79  fof(f41,plain,(
% 3.02/0.79    ~r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3))),
% 3.02/0.79    inference(cnf_transformation,[],[f20])).
% 3.02/0.79  fof(f1296,plain,(
% 3.02/0.79    r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3)) | ~v1_relat_1(k5_relat_1(sK4,sK2))),
% 3.02/0.79    inference(duplicate_literal_removal,[],[f1291])).
% 3.02/0.79  fof(f1291,plain,(
% 3.02/0.79    r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3)) | r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3)) | ~v1_relat_1(k5_relat_1(sK4,sK2))),
% 3.02/0.79    inference(resolution,[],[f1289,f53])).
% 3.02/0.79  fof(f53,plain,(
% 3.02/0.79    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 3.02/0.79    inference(cnf_transformation,[],[f32])).
% 3.02/0.79  fof(f32,plain,(
% 3.02/0.79    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) & r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.02/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f30,f31])).
% 3.02/0.79  fof(f31,plain,(
% 3.02/0.79    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) & r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)))),
% 3.02/0.79    introduced(choice_axiom,[])).
% 3.02/0.79  fof(f30,plain,(
% 3.02/0.79    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.02/0.79    inference(rectify,[],[f29])).
% 3.02/0.79  fof(f29,plain,(
% 3.02/0.79    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.02/0.79    inference(nnf_transformation,[],[f10])).
% 3.02/0.79  fof(f10,plain,(
% 3.02/0.79    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 3.02/0.79    inference(ennf_transformation,[],[f2])).
% 3.02/0.79  fof(f2,axiom,(
% 3.02/0.79    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 3.02/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 3.02/0.79  fof(f1289,plain,(
% 3.02/0.79    ( ! [X0] : (r2_hidden(k4_tarski(sK9(k5_relat_1(sK4,sK2),X0),sK10(k5_relat_1(sK4,sK2),X0)),k5_relat_1(sK4,sK3)) | r1_tarski(k5_relat_1(sK4,sK2),X0)) )),
% 3.02/0.79    inference(subsumption_resolution,[],[f1288,f37])).
% 3.02/0.79  fof(f1288,plain,(
% 3.02/0.79    ( ! [X0] : (r1_tarski(k5_relat_1(sK4,sK2),X0) | r2_hidden(k4_tarski(sK9(k5_relat_1(sK4,sK2),X0),sK10(k5_relat_1(sK4,sK2),X0)),k5_relat_1(sK4,sK3)) | ~v1_relat_1(sK2)) )),
% 3.02/0.79    inference(subsumption_resolution,[],[f1287,f39])).
% 3.02/0.79  fof(f1287,plain,(
% 3.02/0.79    ( ! [X0] : (r1_tarski(k5_relat_1(sK4,sK2),X0) | r2_hidden(k4_tarski(sK9(k5_relat_1(sK4,sK2),X0),sK10(k5_relat_1(sK4,sK2),X0)),k5_relat_1(sK4,sK3)) | ~v1_relat_1(sK4) | ~v1_relat_1(sK2)) )),
% 3.02/0.79    inference(duplicate_literal_removal,[],[f1286])).
% 3.02/0.79  fof(f1286,plain,(
% 3.02/0.79    ( ! [X0] : (r1_tarski(k5_relat_1(sK4,sK2),X0) | r2_hidden(k4_tarski(sK9(k5_relat_1(sK4,sK2),X0),sK10(k5_relat_1(sK4,sK2),X0)),k5_relat_1(sK4,sK3)) | ~v1_relat_1(sK4) | ~v1_relat_1(sK2) | r1_tarski(k5_relat_1(sK4,sK2),X0)) )),
% 3.02/0.79    inference(resolution,[],[f306,f193])).
% 3.02/0.79  fof(f193,plain,(
% 3.02/0.79    ( ! [X8,X9] : (r2_hidden(k4_tarski(sK9(k5_relat_1(sK4,X8),X9),sK8(X8,sK4,sK9(k5_relat_1(sK4,X8),X9),sK10(k5_relat_1(sK4,X8),X9))),sK4) | ~v1_relat_1(X8) | r1_tarski(k5_relat_1(sK4,X8),X9)) )),
% 3.02/0.79    inference(resolution,[],[f101,f39])).
% 3.02/0.79  fof(f101,plain,(
% 3.02/0.79    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK9(k5_relat_1(X0,X1),X2),sK8(X1,X0,sK9(k5_relat_1(X0,X1),X2),sK10(k5_relat_1(X0,X1),X2))),X0)) )),
% 3.02/0.79    inference(subsumption_resolution,[],[f100,f54])).
% 3.02/0.79  fof(f100,plain,(
% 3.02/0.79    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK9(k5_relat_1(X0,X1),X2),sK8(X1,X0,sK9(k5_relat_1(X0,X1),X2),sK10(k5_relat_1(X0,X1),X2))),X0) | r1_tarski(k5_relat_1(X0,X1),X2) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.02/0.79    inference(resolution,[],[f80,f66])).
% 3.02/0.79  fof(f66,plain,(
% 3.02/0.79    ( ! [X0,X1] : (sP0(X0,X1,k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 3.02/0.79    inference(subsumption_resolution,[],[f65,f54])).
% 3.02/0.79  fof(f65,plain,(
% 3.02/0.79    ( ! [X0,X1] : (sP0(X0,X1,k5_relat_1(X1,X0)) | ~v1_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 3.02/0.79    inference(resolution,[],[f58,f50])).
% 3.02/0.79  fof(f50,plain,(
% 3.02/0.79    ( ! [X2,X0,X1] : (sP1(X2,X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.02/0.79    inference(cnf_transformation,[],[f16])).
% 3.02/0.79  fof(f16,plain,(
% 3.02/0.79    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.02/0.79    inference(definition_folding,[],[f9,f15,f14])).
% 3.02/0.79  fof(f14,plain,(
% 3.02/0.79    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0))))),
% 3.02/0.79    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.02/0.79  fof(f15,plain,(
% 3.02/0.79    ! [X2,X0,X1] : ((k5_relat_1(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 3.02/0.79    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.02/0.79  fof(f9,plain,(
% 3.02/0.79    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.02/0.79    inference(ennf_transformation,[],[f3])).
% 3.02/0.79  fof(f3,axiom,(
% 3.02/0.79    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 3.02/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 3.02/0.79  fof(f58,plain,(
% 3.02/0.79    ( ! [X2,X1] : (~sP1(k5_relat_1(X1,X2),X1,X2) | sP0(X2,X1,k5_relat_1(X1,X2))) )),
% 3.02/0.79    inference(equality_resolution,[],[f42])).
% 3.02/0.79  fof(f42,plain,(
% 3.02/0.79    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | k5_relat_1(X1,X2) != X0 | ~sP1(X0,X1,X2)) )),
% 3.02/0.79    inference(cnf_transformation,[],[f22])).
% 3.02/0.79  fof(f22,plain,(
% 3.02/0.79    ! [X0,X1,X2] : (((k5_relat_1(X1,X2) = X0 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k5_relat_1(X1,X2) != X0)) | ~sP1(X0,X1,X2))),
% 3.02/0.79    inference(rectify,[],[f21])).
% 3.02/0.79  fof(f21,plain,(
% 3.02/0.79    ! [X2,X0,X1] : (((k5_relat_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k5_relat_1(X0,X1) != X2)) | ~sP1(X2,X0,X1))),
% 3.02/0.79    inference(nnf_transformation,[],[f15])).
% 3.02/0.79  fof(f80,plain,(
% 3.02/0.79    ( ! [X2,X0,X3,X1] : (~sP0(X2,X3,X0) | r2_hidden(k4_tarski(sK9(X0,X1),sK8(X2,X3,sK9(X0,X1),sK10(X0,X1))),X3) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 3.02/0.79    inference(resolution,[],[f44,f52])).
% 3.02/0.79  fof(f52,plain,(
% 3.02/0.79    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 3.02/0.79    inference(cnf_transformation,[],[f32])).
% 3.02/0.79  fof(f44,plain,(
% 3.02/0.79    ( ! [X2,X0,X8,X7,X1] : (~r2_hidden(k4_tarski(X7,X8),X2) | r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X1) | ~sP0(X0,X1,X2)) )),
% 3.02/0.79    inference(cnf_transformation,[],[f28])).
% 3.02/0.79  fof(f28,plain,(
% 3.02/0.79    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X1)) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X0) | ~r2_hidden(k4_tarski(X7,X9),X1))) & ((r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X0) & r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X1)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | ~sP0(X0,X1,X2)))),
% 3.02/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f24,f27,f26,f25])).
% 3.02/0.79  fof(f25,plain,(
% 3.02/0.79    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X3,X5),X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X0) & r2_hidden(k4_tarski(X3,X6),X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X1)) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK6(X0,X1,X2)),X0) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X6),X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2))))),
% 3.02/0.79    introduced(choice_axiom,[])).
% 3.02/0.79  fof(f26,plain,(
% 3.02/0.79    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK6(X0,X1,X2)),X0) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X6),X1)) => (r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X1)))),
% 3.02/0.79    introduced(choice_axiom,[])).
% 3.02/0.79  fof(f27,plain,(
% 3.02/0.79    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X0) & r2_hidden(k4_tarski(X7,X10),X1)) => (r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X0) & r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X1)))),
% 3.02/0.79    introduced(choice_axiom,[])).
% 3.02/0.79  fof(f24,plain,(
% 3.02/0.79    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X3,X5),X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X0) & r2_hidden(k4_tarski(X3,X6),X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X0) | ~r2_hidden(k4_tarski(X7,X9),X1))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X0) & r2_hidden(k4_tarski(X7,X10),X1)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | ~sP0(X0,X1,X2)))),
% 3.02/0.79    inference(rectify,[],[f23])).
% 3.02/0.79  fof(f23,plain,(
% 3.02/0.79    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | ~sP0(X1,X0,X2)))),
% 3.02/0.79    inference(nnf_transformation,[],[f14])).
% 3.33/0.81  fof(f306,plain,(
% 3.33/0.81    ( ! [X4,X2,X3] : (~r2_hidden(k4_tarski(X3,sK8(sK2,sK4,sK9(k5_relat_1(sK4,sK2),X2),sK10(k5_relat_1(sK4,sK2),X2))),X4) | r1_tarski(k5_relat_1(sK4,sK2),X2) | r2_hidden(k4_tarski(X3,sK10(k5_relat_1(sK4,sK2),X2)),k5_relat_1(X4,sK3)) | ~v1_relat_1(X4)) )),
% 3.33/0.81    inference(subsumption_resolution,[],[f303,f38])).
% 3.33/0.81  fof(f38,plain,(
% 3.33/0.81    v1_relat_1(sK3)),
% 3.33/0.81    inference(cnf_transformation,[],[f20])).
% 3.33/0.81  fof(f303,plain,(
% 3.33/0.81    ( ! [X4,X2,X3] : (r1_tarski(k5_relat_1(sK4,sK2),X2) | ~r2_hidden(k4_tarski(X3,sK8(sK2,sK4,sK9(k5_relat_1(sK4,sK2),X2),sK10(k5_relat_1(sK4,sK2),X2))),X4) | r2_hidden(k4_tarski(X3,sK10(k5_relat_1(sK4,sK2),X2)),k5_relat_1(X4,sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(X4)) )),
% 3.33/0.81    inference(resolution,[],[f300,f93])).
% 3.33/0.81  fof(f93,plain,(
% 3.33/0.81    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(k4_tarski(X3,X0),X4) | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X4)) )),
% 3.33/0.81    inference(resolution,[],[f46,f66])).
% 3.33/0.81  fof(f46,plain,(
% 3.33/0.81    ( ! [X2,X0,X8,X7,X1,X9] : (~sP0(X0,X1,X2) | ~r2_hidden(k4_tarski(X9,X8),X0) | ~r2_hidden(k4_tarski(X7,X9),X1) | r2_hidden(k4_tarski(X7,X8),X2)) )),
% 3.33/0.81    inference(cnf_transformation,[],[f28])).
% 3.33/0.81  fof(f300,plain,(
% 3.33/0.81    ( ! [X0] : (r2_hidden(k4_tarski(sK8(sK2,sK4,sK9(k5_relat_1(sK4,sK2),X0),sK10(k5_relat_1(sK4,sK2),X0)),sK10(k5_relat_1(sK4,sK2),X0)),sK3) | r1_tarski(k5_relat_1(sK4,sK2),X0)) )),
% 3.33/0.81    inference(resolution,[],[f267,f40])).
% 3.33/0.81  fof(f40,plain,(
% 3.33/0.81    r1_tarski(sK2,sK3)),
% 3.33/0.81    inference(cnf_transformation,[],[f20])).
% 3.33/0.81  fof(f267,plain,(
% 3.33/0.81    ( ! [X0,X1] : (~r1_tarski(sK2,X1) | r2_hidden(k4_tarski(sK8(sK2,sK4,sK9(k5_relat_1(sK4,sK2),X0),sK10(k5_relat_1(sK4,sK2),X0)),sK10(k5_relat_1(sK4,sK2),X0)),X1) | r1_tarski(k5_relat_1(sK4,sK2),X0)) )),
% 3.33/0.81    inference(resolution,[],[f264,f55])).
% 3.33/0.81  fof(f55,plain,(
% 3.33/0.81    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 3.33/0.81    inference(cnf_transformation,[],[f36])).
% 3.33/0.81  fof(f36,plain,(
% 3.33/0.81    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK11(X0,X1),X1) & r2_hidden(sK11(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.33/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f34,f35])).
% 3.33/0.81  fof(f35,plain,(
% 3.33/0.81    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK11(X0,X1),X1) & r2_hidden(sK11(X0,X1),X0)))),
% 3.33/0.81    introduced(choice_axiom,[])).
% 3.33/0.81  fof(f34,plain,(
% 3.33/0.81    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.33/0.81    inference(rectify,[],[f33])).
% 3.33/0.81  fof(f33,plain,(
% 3.33/0.81    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.33/0.81    inference(nnf_transformation,[],[f13])).
% 3.33/0.81  fof(f13,plain,(
% 3.33/0.81    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.33/0.81    inference(ennf_transformation,[],[f1])).
% 3.33/0.81  fof(f1,axiom,(
% 3.33/0.81    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.33/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.33/0.81  fof(f264,plain,(
% 3.33/0.81    ( ! [X3] : (r2_hidden(k4_tarski(sK8(sK2,sK4,sK9(k5_relat_1(sK4,sK2),X3),sK10(k5_relat_1(sK4,sK2),X3)),sK10(k5_relat_1(sK4,sK2),X3)),sK2) | r1_tarski(k5_relat_1(sK4,sK2),X3)) )),
% 3.33/0.81    inference(resolution,[],[f212,f37])).
% 3.33/0.81  fof(f212,plain,(
% 3.33/0.81    ( ! [X8,X9] : (~v1_relat_1(X8) | r2_hidden(k4_tarski(sK8(X8,sK4,sK9(k5_relat_1(sK4,X8),X9),sK10(k5_relat_1(sK4,X8),X9)),sK10(k5_relat_1(sK4,X8),X9)),X8) | r1_tarski(k5_relat_1(sK4,X8),X9)) )),
% 3.33/0.81    inference(resolution,[],[f95,f39])).
% 3.33/0.81  fof(f95,plain,(
% 3.33/0.81    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK8(X0,X1,sK9(k5_relat_1(X1,X0),X2),sK10(k5_relat_1(X1,X0),X2)),sK10(k5_relat_1(X1,X0),X2)),X0) | r1_tarski(k5_relat_1(X1,X0),X2)) )),
% 3.33/0.81    inference(subsumption_resolution,[],[f94,f54])).
% 3.33/0.81  fof(f94,plain,(
% 3.33/0.81    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X1,sK9(k5_relat_1(X1,X0),X2),sK10(k5_relat_1(X1,X0),X2)),sK10(k5_relat_1(X1,X0),X2)),X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(k5_relat_1(X1,X0),X2) | ~v1_relat_1(k5_relat_1(X1,X0))) )),
% 3.33/0.81    inference(resolution,[],[f92,f52])).
% 3.33/0.81  fof(f92,plain,(
% 3.33/0.81    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) | r2_hidden(k4_tarski(sK8(X3,X2,X0,X1),X1),X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 3.33/0.81    inference(resolution,[],[f45,f66])).
% 3.33/0.81  fof(f45,plain,(
% 3.33/0.81    ( ! [X2,X0,X8,X7,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(k4_tarski(X7,X8),X2) | r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X0)) )),
% 3.33/0.81    inference(cnf_transformation,[],[f28])).
% 3.33/0.81  % SZS output end Proof for theBenchmark
% 3.33/0.81  % (21703)------------------------------
% 3.33/0.81  % (21703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.81  % (21703)Termination reason: Refutation
% 3.33/0.81  
% 3.33/0.81  % (21703)Memory used [KB]: 8443
% 3.33/0.81  % (21703)Time elapsed: 0.395 s
% 3.33/0.81  % (21703)------------------------------
% 3.33/0.81  % (21703)------------------------------
% 3.33/0.82  % (21692)Success in time 0.457 s
%------------------------------------------------------------------------------
