%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:24 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 212 expanded)
%              Number of leaves         :   13 (  74 expanded)
%              Depth                    :   24
%              Number of atoms          :  303 (1098 expanded)
%              Number of equality atoms :    8 (  27 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f394,plain,(
    $false ),
    inference(subsumption_resolution,[],[f393,f36])).

fof(f36,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3))
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK4)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f8,f18,f17,f16])).

fof(f16,plain,
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

fof(f17,plain,
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

fof(f18,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(f393,plain,(
    ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f392,f34])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f392,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f391,f51])).

fof(f51,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f391,plain,(
    ~ v1_relat_1(k5_relat_1(sK4,sK2)) ),
    inference(subsumption_resolution,[],[f390,f38])).

fof(f38,plain,(
    ~ r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f390,plain,
    ( r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3))
    | ~ v1_relat_1(k5_relat_1(sK4,sK2)) ),
    inference(duplicate_literal_removal,[],[f387])).

fof(f387,plain,
    ( r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3))
    | ~ v1_relat_1(k5_relat_1(sK4,sK2))
    | r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3))
    | ~ v1_relat_1(k5_relat_1(sK4,sK2)) ),
    inference(resolution,[],[f380,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f380,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK9(X0,k5_relat_1(sK4,sK3)),sK10(X0,k5_relat_1(sK4,sK3))),k5_relat_1(sK4,sK2))
      | r1_tarski(X0,k5_relat_1(sK4,sK3))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f378,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f378,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK3))
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK2)) ) ),
    inference(subsumption_resolution,[],[f377,f36])).

fof(f377,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK2))
      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK3))
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f376,f34])).

fof(f376,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK2))
      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK3))
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK4) ) ),
    inference(duplicate_literal_removal,[],[f374])).

fof(f374,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK2))
      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK3))
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK2))
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f269,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,sK8(X3,X2,X0,X1)),X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f41,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f60,f51])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,k5_relat_1(X1,X0))
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f55,f47])).

fof(f47,plain,(
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

fof(f55,plain,(
    ! [X2,X1] :
      ( ~ sP1(k5_relat_1(X1,X2),X1,X2)
      | sP0(X2,X1,k5_relat_1(X1,X2)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k5_relat_1(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( k5_relat_1(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k5_relat_1(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ( ( k5_relat_1(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k5_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f23,f26,f25,f24])).

fof(f24,plain,(
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

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK6(X0,X1,X2)),X0)
          & r2_hidden(k4_tarski(sK5(X0,X1,X2),X6),X1) )
     => ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X0)
          & r2_hidden(k4_tarski(X7,X10),X1) )
     => ( r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X0)
        & r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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

fof(f269,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X2,sK8(sK2,sK4,X0,X1)),sK4)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK2))
      | r2_hidden(k4_tarski(X2,X1),k5_relat_1(sK4,sK3)) ) ),
    inference(resolution,[],[f250,f149])).

fof(f149,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(k4_tarski(X10,X9),sK3)
      | ~ r2_hidden(k4_tarski(X8,X10),sK4)
      | r2_hidden(k4_tarski(X8,X9),k5_relat_1(sK4,sK3)) ) ),
    inference(resolution,[],[f84,f35])).

fof(f35,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f84,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v1_relat_1(X17)
      | r2_hidden(k4_tarski(X14,X16),k5_relat_1(sK4,X17))
      | ~ r2_hidden(k4_tarski(X14,X15),sK4)
      | ~ r2_hidden(k4_tarski(X15,X16),X17) ) ),
    inference(resolution,[],[f74,f36])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X4)
      | ~ r2_hidden(k4_tarski(X3,X0),X4)
      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(resolution,[],[f43,f61])).

fof(f43,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X0)
      | ~ r2_hidden(k4_tarski(X7,X9),X1)
      | r2_hidden(k4_tarski(X7,X8),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f250,plain,(
    ! [X8,X9] :
      ( r2_hidden(k4_tarski(sK8(sK2,sK4,X8,X9),X9),sK3)
      | ~ r2_hidden(k4_tarski(X8,X9),k5_relat_1(sK4,sK2)) ) ),
    inference(resolution,[],[f246,f36])).

fof(f246,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK8(sK2,X0,X1,X2),X2),sK3)
      | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK2)) ) ),
    inference(subsumption_resolution,[],[f244,f34])).

fof(f244,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK8(sK2,X0,X1,X2),X2),sK3)
      | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK2)) ) ),
    inference(resolution,[],[f80,f37])).

fof(f37,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,X4)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK8(X3,X2,X0,X1),X1),X4)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK8(X3,X2,X0,X1),X1),X4)
      | ~ r1_tarski(X3,X4)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f73,f48])).

fof(f48,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X5),X0)
      | r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK8(X3,X2,X0,X1),X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f42,f61])).

fof(f42,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X0) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (23442)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (23444)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (23453)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (23440)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (23437)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (23446)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (23444)Refutation not found, incomplete strategy% (23444)------------------------------
% 0.21/0.51  % (23444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23443)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (23441)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (23462)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (23448)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (23460)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (23445)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (23457)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (23438)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (23461)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (23450)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (23456)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.32/0.52  % (23449)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.32/0.52  % (23451)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.32/0.53  % (23452)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.32/0.53  % (23444)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (23444)Memory used [KB]: 10618
% 1.32/0.53  % (23444)Time elapsed: 0.102 s
% 1.32/0.53  % (23444)------------------------------
% 1.32/0.53  % (23444)------------------------------
% 1.32/0.53  % (23454)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.32/0.53  % (23438)Refutation not found, incomplete strategy% (23438)------------------------------
% 1.32/0.53  % (23438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (23438)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (23438)Memory used [KB]: 10618
% 1.32/0.53  % (23438)Time elapsed: 0.119 s
% 1.32/0.53  % (23438)------------------------------
% 1.32/0.53  % (23438)------------------------------
% 1.32/0.53  % (23463)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.32/0.53  % (23458)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.32/0.54  % (23455)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.45/0.55  % (23447)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.45/0.55  % (23464)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.45/0.58  % (23441)Refutation found. Thanks to Tanya!
% 1.45/0.58  % SZS status Theorem for theBenchmark
% 1.45/0.58  % SZS output start Proof for theBenchmark
% 1.45/0.58  fof(f394,plain,(
% 1.45/0.58    $false),
% 1.45/0.58    inference(subsumption_resolution,[],[f393,f36])).
% 1.45/0.58  fof(f36,plain,(
% 1.45/0.58    v1_relat_1(sK4)),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f19,plain,(
% 1.45/0.58    ((~r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK4)) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 1.45/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f8,f18,f17,f16])).
% 1.45/0.58  fof(f16,plain,(
% 1.45/0.58    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X2,sK2),k5_relat_1(X2,X1)) & r1_tarski(sK2,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f17,plain,(
% 1.45/0.58    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X2,sK2),k5_relat_1(X2,X1)) & r1_tarski(sK2,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(X2,sK2),k5_relat_1(X2,sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(X2)) & v1_relat_1(sK3))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f18,plain,(
% 1.45/0.58    ? [X2] : (~r1_tarski(k5_relat_1(X2,sK2),k5_relat_1(X2,sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK4))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f8,plain,(
% 1.45/0.58    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.45/0.58    inference(flattening,[],[f7])).
% 1.45/0.58  fof(f7,plain,(
% 1.45/0.58    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.45/0.58    inference(ennf_transformation,[],[f6])).
% 1.45/0.58  fof(f6,negated_conjecture,(
% 1.45/0.58    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 1.45/0.58    inference(negated_conjecture,[],[f5])).
% 1.45/0.58  fof(f5,conjecture,(
% 1.45/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).
% 1.45/0.58  fof(f393,plain,(
% 1.45/0.58    ~v1_relat_1(sK4)),
% 1.45/0.58    inference(subsumption_resolution,[],[f392,f34])).
% 1.45/0.58  fof(f34,plain,(
% 1.45/0.58    v1_relat_1(sK2)),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f392,plain,(
% 1.45/0.58    ~v1_relat_1(sK2) | ~v1_relat_1(sK4)),
% 1.45/0.58    inference(resolution,[],[f391,f51])).
% 1.45/0.58  fof(f51,plain,(
% 1.45/0.58    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f12])).
% 1.45/0.58  fof(f12,plain,(
% 1.45/0.58    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.45/0.58    inference(flattening,[],[f11])).
% 1.45/0.58  fof(f11,plain,(
% 1.45/0.58    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.45/0.58    inference(ennf_transformation,[],[f4])).
% 1.45/0.58  fof(f4,axiom,(
% 1.45/0.58    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.45/0.58  fof(f391,plain,(
% 1.45/0.58    ~v1_relat_1(k5_relat_1(sK4,sK2))),
% 1.45/0.58    inference(subsumption_resolution,[],[f390,f38])).
% 1.45/0.58  fof(f38,plain,(
% 1.45/0.58    ~r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3))),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f390,plain,(
% 1.45/0.58    r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3)) | ~v1_relat_1(k5_relat_1(sK4,sK2))),
% 1.45/0.58    inference(duplicate_literal_removal,[],[f387])).
% 1.45/0.58  fof(f387,plain,(
% 1.45/0.58    r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3)) | ~v1_relat_1(k5_relat_1(sK4,sK2)) | r1_tarski(k5_relat_1(sK4,sK2),k5_relat_1(sK4,sK3)) | ~v1_relat_1(k5_relat_1(sK4,sK2))),
% 1.45/0.58    inference(resolution,[],[f380,f49])).
% 1.45/0.58  fof(f49,plain,(
% 1.45/0.58    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f31])).
% 1.45/0.58  fof(f31,plain,(
% 1.45/0.58    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) & r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.45/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f29,f30])).
% 1.45/0.58  fof(f30,plain,(
% 1.45/0.58    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) & r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f29,plain,(
% 1.45/0.58    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.45/0.58    inference(rectify,[],[f28])).
% 1.45/0.58  fof(f28,plain,(
% 1.45/0.58    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.45/0.58    inference(nnf_transformation,[],[f10])).
% 1.45/0.58  fof(f10,plain,(
% 1.45/0.58    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 1.45/0.58    inference(ennf_transformation,[],[f2])).
% 1.45/0.58  fof(f2,axiom,(
% 1.45/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 1.45/0.58  fof(f380,plain,(
% 1.45/0.58    ( ! [X0] : (~r2_hidden(k4_tarski(sK9(X0,k5_relat_1(sK4,sK3)),sK10(X0,k5_relat_1(sK4,sK3))),k5_relat_1(sK4,sK2)) | r1_tarski(X0,k5_relat_1(sK4,sK3)) | ~v1_relat_1(X0)) )),
% 1.45/0.58    inference(resolution,[],[f378,f50])).
% 1.45/0.58  fof(f50,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f31])).
% 1.45/0.58  fof(f378,plain,(
% 1.45/0.58    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK3)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK2))) )),
% 1.45/0.58    inference(subsumption_resolution,[],[f377,f36])).
% 1.45/0.58  fof(f377,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK2)) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK3)) | ~v1_relat_1(sK4)) )),
% 1.45/0.58    inference(subsumption_resolution,[],[f376,f34])).
% 1.45/0.58  fof(f376,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK2)) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK3)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK4)) )),
% 1.45/0.58    inference(duplicate_literal_removal,[],[f374])).
% 1.45/0.58  fof(f374,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK2)) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK3)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK4)) )),
% 1.45/0.58    inference(resolution,[],[f269,f72])).
% 1.45/0.58  fof(f72,plain,(
% 1.45/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,sK8(X3,X2,X0,X1)),X2) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 1.45/0.58    inference(resolution,[],[f41,f61])).
% 1.45/0.58  fof(f61,plain,(
% 1.45/0.58    ( ! [X0,X1] : (sP0(X0,X1,k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 1.45/0.58    inference(subsumption_resolution,[],[f60,f51])).
% 1.45/0.58  fof(f60,plain,(
% 1.45/0.58    ( ! [X0,X1] : (sP0(X0,X1,k5_relat_1(X1,X0)) | ~v1_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 1.45/0.58    inference(resolution,[],[f55,f47])).
% 1.45/0.58  fof(f47,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (sP1(X2,X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f15])).
% 1.45/0.58  fof(f15,plain,(
% 1.45/0.58    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.45/0.58    inference(definition_folding,[],[f9,f14,f13])).
% 1.45/0.58  fof(f13,plain,(
% 1.45/0.58    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0))))),
% 1.45/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.45/0.58  fof(f14,plain,(
% 1.45/0.58    ! [X2,X0,X1] : ((k5_relat_1(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 1.45/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.45/0.58  fof(f9,plain,(
% 1.45/0.58    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.45/0.58    inference(ennf_transformation,[],[f3])).
% 1.45/0.58  fof(f3,axiom,(
% 1.45/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 1.45/0.58  fof(f55,plain,(
% 1.45/0.58    ( ! [X2,X1] : (~sP1(k5_relat_1(X1,X2),X1,X2) | sP0(X2,X1,k5_relat_1(X1,X2))) )),
% 1.45/0.58    inference(equality_resolution,[],[f39])).
% 1.45/0.58  fof(f39,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | k5_relat_1(X1,X2) != X0 | ~sP1(X0,X1,X2)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f21])).
% 1.45/0.58  fof(f21,plain,(
% 1.45/0.58    ! [X0,X1,X2] : (((k5_relat_1(X1,X2) = X0 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k5_relat_1(X1,X2) != X0)) | ~sP1(X0,X1,X2))),
% 1.45/0.58    inference(rectify,[],[f20])).
% 1.45/0.58  fof(f20,plain,(
% 1.45/0.58    ! [X2,X0,X1] : (((k5_relat_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k5_relat_1(X0,X1) != X2)) | ~sP1(X2,X0,X1))),
% 1.45/0.58    inference(nnf_transformation,[],[f14])).
% 1.45/0.58  fof(f41,plain,(
% 1.45/0.58    ( ! [X2,X0,X8,X7,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(k4_tarski(X7,X8),X2) | r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f27])).
% 1.45/0.58  fof(f27,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X1)) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X0) | ~r2_hidden(k4_tarski(X7,X9),X1))) & ((r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X0) & r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X1)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | ~sP0(X0,X1,X2)))),
% 1.45/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f23,f26,f25,f24])).
% 1.45/0.58  fof(f24,plain,(
% 1.45/0.58    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X3,X5),X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X0) & r2_hidden(k4_tarski(X3,X6),X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X1)) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK6(X0,X1,X2)),X0) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X6),X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2))))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f25,plain,(
% 1.45/0.58    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK6(X0,X1,X2)),X0) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X6),X1)) => (r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK7(X0,X1,X2)),X1)))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f26,plain,(
% 1.45/0.58    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X0) & r2_hidden(k4_tarski(X7,X10),X1)) => (r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X0) & r2_hidden(k4_tarski(X7,sK8(X0,X1,X7,X8)),X1)))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f23,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X3,X5),X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X0) & r2_hidden(k4_tarski(X3,X6),X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X0) | ~r2_hidden(k4_tarski(X7,X9),X1))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X0) & r2_hidden(k4_tarski(X7,X10),X1)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | ~sP0(X0,X1,X2)))),
% 1.45/0.58    inference(rectify,[],[f22])).
% 1.45/0.58  fof(f22,plain,(
% 1.45/0.58    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | ~sP0(X1,X0,X2)))),
% 1.45/0.58    inference(nnf_transformation,[],[f13])).
% 1.45/0.58  fof(f269,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X2,sK8(sK2,sK4,X0,X1)),sK4) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK4,sK2)) | r2_hidden(k4_tarski(X2,X1),k5_relat_1(sK4,sK3))) )),
% 1.45/0.58    inference(resolution,[],[f250,f149])).
% 1.45/0.58  fof(f149,plain,(
% 1.45/0.58    ( ! [X10,X8,X9] : (~r2_hidden(k4_tarski(X10,X9),sK3) | ~r2_hidden(k4_tarski(X8,X10),sK4) | r2_hidden(k4_tarski(X8,X9),k5_relat_1(sK4,sK3))) )),
% 1.45/0.58    inference(resolution,[],[f84,f35])).
% 1.45/0.58  fof(f35,plain,(
% 1.45/0.58    v1_relat_1(sK3)),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f84,plain,(
% 1.45/0.58    ( ! [X14,X17,X15,X16] : (~v1_relat_1(X17) | r2_hidden(k4_tarski(X14,X16),k5_relat_1(sK4,X17)) | ~r2_hidden(k4_tarski(X14,X15),sK4) | ~r2_hidden(k4_tarski(X15,X16),X17)) )),
% 1.45/0.58    inference(resolution,[],[f74,f36])).
% 1.45/0.58  fof(f74,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X4) | ~r2_hidden(k4_tarski(X3,X0),X4) | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.45/0.58    inference(resolution,[],[f43,f61])).
% 1.45/0.58  fof(f43,plain,(
% 1.45/0.58    ( ! [X2,X0,X8,X7,X1,X9] : (~sP0(X0,X1,X2) | ~r2_hidden(k4_tarski(X9,X8),X0) | ~r2_hidden(k4_tarski(X7,X9),X1) | r2_hidden(k4_tarski(X7,X8),X2)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f27])).
% 1.45/0.58  fof(f250,plain,(
% 1.45/0.58    ( ! [X8,X9] : (r2_hidden(k4_tarski(sK8(sK2,sK4,X8,X9),X9),sK3) | ~r2_hidden(k4_tarski(X8,X9),k5_relat_1(sK4,sK2))) )),
% 1.45/0.58    inference(resolution,[],[f246,f36])).
% 1.45/0.58  fof(f246,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK8(sK2,X0,X1,X2),X2),sK3) | ~r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK2))) )),
% 1.45/0.58    inference(subsumption_resolution,[],[f244,f34])).
% 1.45/0.58  fof(f244,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(sK2) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK8(sK2,X0,X1,X2),X2),sK3) | ~r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK2))) )),
% 1.45/0.58    inference(resolution,[],[f80,f37])).
% 1.45/0.58  fof(f37,plain,(
% 1.45/0.58    r1_tarski(sK2,sK3)),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f80,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(X3,X4) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK8(X3,X2,X0,X1),X1),X4) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))) )),
% 1.45/0.58    inference(duplicate_literal_removal,[],[f79])).
% 1.45/0.58  fof(f79,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK8(X3,X2,X0,X1),X1),X4) | ~r1_tarski(X3,X4) | ~v1_relat_1(X3)) )),
% 1.45/0.58    inference(resolution,[],[f73,f48])).
% 1.45/0.58  fof(f48,plain,(
% 1.45/0.58    ( ! [X4,X0,X5,X1] : (~r2_hidden(k4_tarski(X4,X5),X0) | r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f31])).
% 1.45/0.58  fof(f73,plain,(
% 1.45/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK8(X3,X2,X0,X1),X1),X3) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 1.45/0.58    inference(resolution,[],[f42,f61])).
% 1.45/0.58  fof(f42,plain,(
% 1.45/0.58    ( ! [X2,X0,X8,X7,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(k4_tarski(X7,X8),X2) | r2_hidden(k4_tarski(sK8(X0,X1,X7,X8),X8),X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f27])).
% 1.45/0.58  % SZS output end Proof for theBenchmark
% 1.45/0.58  % (23441)------------------------------
% 1.45/0.58  % (23441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (23441)Termination reason: Refutation
% 1.45/0.58  
% 1.45/0.58  % (23441)Memory used [KB]: 6908
% 1.45/0.58  % (23441)Time elapsed: 0.176 s
% 1.45/0.58  % (23441)------------------------------
% 1.45/0.58  % (23441)------------------------------
% 1.45/0.58  % (23434)Success in time 0.226 s
%------------------------------------------------------------------------------
