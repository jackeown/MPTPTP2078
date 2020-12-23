%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 800 expanded)
%              Number of leaves         :    9 ( 220 expanded)
%              Depth                    :   22
%              Number of atoms          :  306 (6549 expanded)
%              Number of equality atoms :   29 ( 197 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(subsumption_resolution,[],[f256,f169])).

fof(f169,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),sK1) ),
    inference(unit_resulting_resolution,[],[f25,f26,f160,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f160,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f122,f155,f31])).

fof(f31,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
    & ( ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
        & r2_hidden(sK0,k1_relat_1(sK2)) )
      | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2))
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
            | ~ r2_hidden(sK0,k1_relat_1(X2))
            | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
          & ( ( r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
              & r2_hidden(sK0,k1_relat_1(X2)) )
            | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
          | ~ r2_hidden(sK0,k1_relat_1(X2))
          | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
        & ( ( r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
            & r2_hidden(sK0,k1_relat_1(X2)) )
          | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
        | ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
      & ( ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
          & r2_hidden(sK0,k1_relat_1(sK2)) )
        | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
            | ~ r2_hidden(X0,k1_relat_1(X2))
            | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) )
            | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
            | ~ r2_hidden(X0,k1_relat_1(X2))
            | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) )
            | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
            <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(f155,plain,(
    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(forward_demodulation,[],[f153,f61])).

fof(f61,plain,(
    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f25,f27,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f153,plain,
    ( r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1)))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f143,f30])).

fof(f30,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f143,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK2,sK0),X0)
      | r2_hidden(sK0,k10_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f138,f69])).

fof(f69,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(k4_tarski(X10,X8),sK2)
      | ~ r2_hidden(X8,X9)
      | r2_hidden(X10,k10_relat_1(sK2,X9)) ) ),
    inference(resolution,[],[f27,f42])).

fof(f42,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | r2_hidden(X6,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f21,f20,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f138,plain,(
    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    inference(unit_resulting_resolution,[],[f27,f28,f122,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f122,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f117,f29])).

fof(f29,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f117,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,sK1)))
      | r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(superposition,[],[f104,f61])).

fof(f104,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k10_relat_1(sK2,X6))
      | r2_hidden(X5,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f71,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f72,f27])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | r2_hidden(X0,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f28,f39])).

fof(f71,plain,(
    ! [X14,X13] :
      ( r2_hidden(k4_tarski(X13,sK5(sK2,X14,X13)),sK2)
      | ~ r2_hidden(X13,k10_relat_1(sK2,X14)) ) ),
    inference(resolution,[],[f27,f44])).

fof(f44,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f256,plain,(
    r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK1,k1_funct_1(sK2,sK0))),sK1) ),
    inference(backward_demodulation,[],[f206,f248])).

fof(f248,plain,(
    k1_funct_1(sK2,sK0) = sK5(sK2,k1_relat_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f155,f202])).

fof(f202,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,sK1)))
      | k1_funct_1(sK2,X0) = sK5(sK2,k1_relat_1(sK1),X0) ) ),
    inference(superposition,[],[f103,f61])).

fof(f103,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k10_relat_1(sK2,X4))
      | k1_funct_1(sK2,X3) = sK5(sK2,X4,X3) ) ),
    inference(resolution,[],[f71,f76])).

fof(f76,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | k1_funct_1(sK2,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f73,f27])).

fof(f73,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | k1_funct_1(sK2,X2) = X3
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f28,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f206,plain,(
    r2_hidden(k4_tarski(sK5(sK2,k1_relat_1(sK1),sK0),k1_funct_1(sK1,sK5(sK2,k1_relat_1(sK1),sK0))),sK1) ),
    inference(unit_resulting_resolution,[],[f25,f26,f204,f45])).

fof(f204,plain,(
    r2_hidden(sK5(sK2,k1_relat_1(sK1),sK0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f155,f91])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,k1_relat_1(sK1),X0),k1_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,sK1))) ) ),
    inference(superposition,[],[f70,f61])).

fof(f70,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X11,k10_relat_1(sK2,X12))
      | r2_hidden(sK5(sK2,X12,X11),X12) ) ),
    inference(resolution,[],[f27,f43])).

fof(f43,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | r2_hidden(sK5(X0,X1,X6),X1) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (11351)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.44  % (11351)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f260,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(subsumption_resolution,[],[f256,f169])).
% 0.21/0.44  fof(f169,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),X0),sK1)) )),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f25,f26,f160,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(flattening,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(nnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(flattening,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.44  fof(f160,plain,(
% 0.21/0.44    ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f122,f155,f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ((~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))) & ((r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15,f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2] : ((~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(X2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))) & ((r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1)) & r2_hidden(sK0,k1_relat_1(X2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ? [X2] : ((~r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(X2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))) & ((r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1)) & r2_hidden(sK0,k1_relat_1(X2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))) & v1_funct_1(X2) & v1_relat_1(X2)) => ((~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))) & ((r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2] : ((~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2] : ((((~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <~> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f6])).
% 0.21/0.44  fof(f6,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <~> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.21/0.44    inference(negated_conjecture,[],[f4])).
% 0.21/0.44  fof(f4,conjecture,(
% 0.21/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).
% 0.21/0.44  fof(f155,plain,(
% 0.21/0.44    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f154])).
% 0.21/0.44  fof(f154,plain,(
% 0.21/0.44    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.44    inference(forward_demodulation,[],[f153,f61])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1))),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f25,f27,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    v1_relat_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f153,plain,(
% 0.21/0.44    r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.44    inference(resolution,[],[f143,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f143,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(k1_funct_1(sK2,sK0),X0) | r2_hidden(sK0,k10_relat_1(sK2,X0))) )),
% 0.21/0.44    inference(resolution,[],[f138,f69])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    ( ! [X10,X8,X9] : (~r2_hidden(k4_tarski(X10,X8),sK2) | ~r2_hidden(X8,X9) | r2_hidden(X10,k10_relat_1(sK2,X9))) )),
% 0.21/0.44    inference(resolution,[],[f27,f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X6,X0,X7,X1] : (~v1_relat_1(X0) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | r2_hidden(X6,k10_relat_1(X0,X1))) )),
% 0.21/0.44    inference(equality_resolution,[],[f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f21,f20,f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(rectify,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 0.21/0.44  fof(f138,plain,(
% 0.21/0.44    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f27,f28,f122,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(equality_resolution,[],[f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    v1_funct_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f119])).
% 0.21/0.44  fof(f119,plain,(
% 0.21/0.44    r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.44    inference(resolution,[],[f117,f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) | r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,sK1))) | r2_hidden(X0,k1_relat_1(sK2))) )),
% 0.21/0.44    inference(superposition,[],[f104,f61])).
% 0.21/0.44  fof(f104,plain,(
% 0.21/0.44    ( ! [X6,X5] : (~r2_hidden(X5,k10_relat_1(sK2,X6)) | r2_hidden(X5,k1_relat_1(sK2))) )),
% 0.21/0.44    inference(resolution,[],[f71,f75])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(X0,k1_relat_1(sK2))) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f72,f27])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.21/0.44    inference(resolution,[],[f28,f39])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    ( ! [X14,X13] : (r2_hidden(k4_tarski(X13,sK5(sK2,X14,X13)),sK2) | ~r2_hidden(X13,k10_relat_1(sK2,X14))) )),
% 0.21/0.44    inference(resolution,[],[f27,f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X6,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X6,k10_relat_1(X0,X1)) | r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)) )),
% 0.21/0.44    inference(equality_resolution,[],[f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X6,X2,X0,X1] : (r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    v1_funct_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f256,plain,(
% 0.21/0.44    r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK1,k1_funct_1(sK2,sK0))),sK1)),
% 0.21/0.44    inference(backward_demodulation,[],[f206,f248])).
% 0.21/0.44  fof(f248,plain,(
% 0.21/0.44    k1_funct_1(sK2,sK0) = sK5(sK2,k1_relat_1(sK1),sK0)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f155,f202])).
% 0.21/0.44  fof(f202,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,sK1))) | k1_funct_1(sK2,X0) = sK5(sK2,k1_relat_1(sK1),X0)) )),
% 0.21/0.44    inference(superposition,[],[f103,f61])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    ( ! [X4,X3] : (~r2_hidden(X3,k10_relat_1(sK2,X4)) | k1_funct_1(sK2,X3) = sK5(sK2,X4,X3)) )),
% 0.21/0.44    inference(resolution,[],[f71,f76])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | k1_funct_1(sK2,X2) = X3) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f73,f27])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | k1_funct_1(sK2,X2) = X3 | ~v1_relat_1(sK2)) )),
% 0.21/0.44    inference(resolution,[],[f28,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f206,plain,(
% 0.21/0.44    r2_hidden(k4_tarski(sK5(sK2,k1_relat_1(sK1),sK0),k1_funct_1(sK1,sK5(sK2,k1_relat_1(sK1),sK0))),sK1)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f25,f26,f204,f45])).
% 0.21/0.44  fof(f204,plain,(
% 0.21/0.44    r2_hidden(sK5(sK2,k1_relat_1(sK1),sK0),k1_relat_1(sK1))),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f155,f91])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    ( ! [X0] : (r2_hidden(sK5(sK2,k1_relat_1(sK1),X0),k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK2,sK1)))) )),
% 0.21/0.44    inference(superposition,[],[f70,f61])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ( ! [X12,X11] : (~r2_hidden(X11,k10_relat_1(sK2,X12)) | r2_hidden(sK5(sK2,X12,X11),X12)) )),
% 0.21/0.44    inference(resolution,[],[f27,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X6,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X6,k10_relat_1(X0,X1)) | r2_hidden(sK5(X0,X1,X6),X1)) )),
% 0.21/0.44    inference(equality_resolution,[],[f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X6,X2,X0,X1] : (r2_hidden(sK5(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (11351)------------------------------
% 0.21/0.44  % (11351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (11351)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (11351)Memory used [KB]: 6524
% 0.21/0.44  % (11351)Time elapsed: 0.015 s
% 0.21/0.44  % (11351)------------------------------
% 0.21/0.44  % (11351)------------------------------
% 0.21/0.44  % (11334)Success in time 0.084 s
%------------------------------------------------------------------------------
