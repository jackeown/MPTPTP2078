%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 826 expanded)
%              Number of leaves         :   12 ( 214 expanded)
%              Depth                    :   32
%              Number of atoms          :  383 (4586 expanded)
%              Number of equality atoms :  109 ( 909 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f273,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f57,f252,f261,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X2),sK2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X2,k9_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f53,f31])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
      | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
      | r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
        | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
        | r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r2_hidden(X1,k11_relat_1(X2,X0))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r2_hidden(X1,k11_relat_1(X2,X0))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r2_hidden(X1,k11_relat_1(X2,X0)) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f53,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | r2_hidden(X6,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f17,f20,f19,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X0) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f261,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(resolution,[],[f257,f32])).

fof(f32,plain,
    ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f257,plain,(
    ~ r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f256,f31])).

fof(f256,plain,
    ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f252,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f252,plain,(
    ~ r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,sK0))) ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,
    ( ~ r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,sK0)))
    | ~ r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,sK0))) ),
    inference(resolution,[],[f232,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(sK2,X1,X0),X1)
      | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f54,f31])).

fof(f54,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | r2_hidden(sK5(X0,X1,X6),X1) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f232,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK2,X0,sK1),k2_tarski(sK0,sK0))
      | ~ r2_hidden(sK1,k9_relat_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f230,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k9_relat_1(sK2,X2))
      | ~ r2_hidden(sK5(sK2,X1,X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f70,f68])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(sK2,X1,X0),X0),sK2)
      | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f55,f31])).

fof(f55,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f230,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,sK0)))
      | ~ r2_hidden(sK5(sK2,X0,sK1),k2_tarski(sK0,sK0))
      | ~ r2_hidden(sK1,k9_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f214,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(sK2,X0))
      | ~ r2_hidden(sK5(sK2,X2,X1),k2_tarski(X0,X0))
      | ~ r2_hidden(X1,k9_relat_1(sK2,X2)) ) ),
    inference(subsumption_resolution,[],[f76,f31])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(sK2,X0))
      | ~ r2_hidden(sK5(sK2,X2,X1),k2_tarski(X0,X0))
      | ~ r2_hidden(X1,k9_relat_1(sK2,X2))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f71,f52])).

fof(f214,plain,
    ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | ~ r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,sK0))) ),
    inference(resolution,[],[f197,f33])).

fof(f33,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f197,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,sK0))) ),
    inference(superposition,[],[f67,f187])).

fof(f187,plain,(
    sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2) ),
    inference(equality_resolution,[],[f186])).

fof(f186,plain,(
    ! [X0] :
      ( sK0 != X0
      | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2) ) ),
    inference(subsumption_resolution,[],[f185,f59])).

fof(f59,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK7(X0,X1,X2) != X1
              & sK7(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sK7(X0,X1,X2) = X1
            | sK7(X0,X1,X2) = X0
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK7(X0,X1,X2) != X1
            & sK7(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sK7(X0,X1,X2) = X1
          | sK7(X0,X1,X2) = X0
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f185,plain,(
    ! [X0] :
      ( sK0 != X0
      | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2)
      | ~ r2_hidden(sK0,k2_tarski(sK0,X0)) ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X0] :
      ( sK0 != X0
      | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2)
      | ~ r2_hidden(sK0,k2_tarski(sK0,X0))
      | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2) ) ),
    inference(resolution,[],[f160,f113])).

fof(f113,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k9_relat_1(sK2,X0))
      | ~ r2_hidden(sK0,X0)
      | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2) ) ),
    inference(resolution,[],[f104,f68])).

fof(f104,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2) ),
    inference(resolution,[],[f102,f32])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(sK2,X0))
      | sK6(X1,k2_tarski(X0,X0),sK2) = X0 ) ),
    inference(subsumption_resolution,[],[f101,f31])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(sK2,X0))
      | sK6(X1,k2_tarski(X0,X0),sK2) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f94,f52])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK2,k2_tarski(X1,X1)))
      | sK6(X0,k2_tarski(X1,X1),sK2) = X1 ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | sK6(X0,k2_tarski(X1,X2),sK2) = X1
      | ~ r2_hidden(X0,k9_relat_1(sK2,k2_tarski(X1,X2))) ) ),
    inference(equality_factoring,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( sK6(X0,k2_tarski(X1,X2),sK2) = X2
      | sK6(X0,k2_tarski(X1,X2),sK2) = X1
      | ~ r2_hidden(X0,k9_relat_1(sK2,k2_tarski(X1,X2))) ) ),
    inference(resolution,[],[f63,f60])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1,sK2),X1)
      | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f44,f31])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
            & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f160,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,X1)))
      | sK0 != X1
      | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2) ) ),
    inference(subsumption_resolution,[],[f157,f57])).

fof(f157,plain,(
    ! [X1] :
      ( sK0 != X1
      | ~ r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,X1)))
      | ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
      | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2) ) ),
    inference(resolution,[],[f153,f116])).

fof(f116,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k11_relat_1(sK2,X0))
      | ~ r2_hidden(sK0,k2_tarski(X0,X0))
      | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2) ) ),
    inference(subsumption_resolution,[],[f115,f31])).

fof(f115,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k11_relat_1(sK2,X0))
      | ~ r2_hidden(sK0,k2_tarski(X0,X0))
      | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f113,f52])).

fof(f153,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
      | sK0 != X0
      | ~ r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,X0))) ) ),
    inference(resolution,[],[f147,f33])).

fof(f147,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(k4_tarski(X3,X5),sK2)
      | ~ r2_hidden(X5,k9_relat_1(sK2,k2_tarski(X3,X4)))
      | X3 != X4 ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(k4_tarski(X3,X5),sK2)
      | ~ r2_hidden(X5,k9_relat_1(sK2,k2_tarski(X3,X4)))
      | X3 != X4
      | ~ r2_hidden(X5,k9_relat_1(sK2,k2_tarski(X3,X4))) ) ),
    inference(superposition,[],[f70,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( sK5(sK2,k2_tarski(X0,X1),X2) = X0
      | X0 != X1
      | ~ r2_hidden(X2,k9_relat_1(sK2,k2_tarski(X0,X1))) ) ),
    inference(equality_factoring,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sK5(sK2,k2_tarski(X1,X2),X0) = X2
      | sK5(sK2,k2_tarski(X1,X2),X0) = X1
      | ~ r2_hidden(X0,k9_relat_1(sK2,k2_tarski(X1,X2))) ) ),
    inference(resolution,[],[f64,f60])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,sK2),X0),sK2)
      | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f43,f31])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:16:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (14504)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (14516)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.50  % (14508)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (14512)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (14504)Refutation not found, incomplete strategy% (14504)------------------------------
% 0.20/0.51  % (14504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14500)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (14498)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (14498)Refutation not found, incomplete strategy% (14498)------------------------------
% 0.20/0.51  % (14498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14498)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (14498)Memory used [KB]: 1791
% 0.20/0.51  % (14498)Time elapsed: 0.109 s
% 0.20/0.51  % (14498)------------------------------
% 0.20/0.51  % (14498)------------------------------
% 0.20/0.51  % (14520)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (14504)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (14504)Memory used [KB]: 10746
% 0.20/0.51  % (14504)Time elapsed: 0.097 s
% 0.20/0.51  % (14504)------------------------------
% 0.20/0.51  % (14504)------------------------------
% 0.20/0.52  % (14499)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (14494)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (14495)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (14516)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f273,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f57,f252,f261,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X2),sK2) | ~r2_hidden(X0,X1) | r2_hidden(X2,k9_relat_1(sK2,X1))) )),
% 0.20/0.53    inference(resolution,[],[f53,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    v1_relat_1(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    (~r2_hidden(sK1,k11_relat_1(sK2,sK0)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & (r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & v1_relat_1(sK2)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((~r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2)) => ((~r2_hidden(sK1,k11_relat_1(sK2,sK0)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & (r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & v1_relat_1(sK2))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((~r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (((~r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2))) & v1_relat_1(X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r2_hidden(X1,k11_relat_1(X2,X0))) & v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.20/0.53    inference(negated_conjecture,[],[f6])).
% 0.20/0.53  fof(f6,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X6,X0,X7,X1] : (~v1_relat_1(X0) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | r2_hidden(X6,k9_relat_1(X0,X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f17,f20,f19,f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X0)) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(rectify,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).
% 0.20/0.53  fof(f261,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.20/0.53    inference(resolution,[],[f257,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f257,plain,(
% 0.20/0.53    ~r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f256,f31])).
% 0.20/0.53  fof(f256,plain,(
% 0.20/0.53    ~r2_hidden(sK1,k11_relat_1(sK2,sK0)) | ~v1_relat_1(sK2)),
% 0.20/0.53    inference(superposition,[],[f252,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f35,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.53  fof(f252,plain,(
% 0.20/0.53    ~r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,sK0)))),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f247])).
% 0.20/0.53  fof(f247,plain,(
% 0.20/0.53    ~r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,sK0))) | ~r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,sK0)))),
% 0.20/0.53    inference(resolution,[],[f232,f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK5(sK2,X1,X0),X1) | ~r2_hidden(X0,k9_relat_1(sK2,X1))) )),
% 0.20/0.53    inference(resolution,[],[f54,f31])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X6,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | r2_hidden(sK5(X0,X1,X6),X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X6,X2,X0,X1] : (r2_hidden(sK5(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f232,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(sK5(sK2,X0,sK1),k2_tarski(sK0,sK0)) | ~r2_hidden(sK1,k9_relat_1(sK2,X0))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f230,f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,k9_relat_1(sK2,X2)) | ~r2_hidden(sK5(sK2,X1,X0),X2) | ~r2_hidden(X0,k9_relat_1(sK2,X1))) )),
% 0.20/0.53    inference(resolution,[],[f70,f68])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(sK2,X1,X0),X0),sK2) | ~r2_hidden(X0,k9_relat_1(sK2,X1))) )),
% 0.20/0.53    inference(resolution,[],[f55,f31])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X6,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X6,X2,X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f230,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,sK0))) | ~r2_hidden(sK5(sK2,X0,sK1),k2_tarski(sK0,sK0)) | ~r2_hidden(sK1,k9_relat_1(sK2,X0))) )),
% 0.20/0.53    inference(resolution,[],[f214,f77])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(sK2,X0)) | ~r2_hidden(sK5(sK2,X2,X1),k2_tarski(X0,X0)) | ~r2_hidden(X1,k9_relat_1(sK2,X2))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f76,f31])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(sK2,X0)) | ~r2_hidden(sK5(sK2,X2,X1),k2_tarski(X0,X0)) | ~r2_hidden(X1,k9_relat_1(sK2,X2)) | ~v1_relat_1(sK2)) )),
% 0.20/0.53    inference(superposition,[],[f71,f52])).
% 0.20/0.53  fof(f214,plain,(
% 0.20/0.53    ~r2_hidden(sK1,k11_relat_1(sK2,sK0)) | ~r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,sK0)))),
% 0.20/0.53    inference(resolution,[],[f197,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f197,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,sK0)))),
% 0.20/0.53    inference(superposition,[],[f67,f187])).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2)),
% 0.20/0.53    inference(equality_resolution,[],[f186])).
% 0.20/0.53  fof(f186,plain,(
% 0.20/0.53    ( ! [X0] : (sK0 != X0 | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f185,f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 0.20/0.53    inference(equality_resolution,[],[f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK7(X0,X1,X2) != X1 & sK7(X0,X1,X2) != X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X1 | sK7(X0,X1,X2) = X0 | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK7(X0,X1,X2) != X1 & sK7(X0,X1,X2) != X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X1 | sK7(X0,X1,X2) = X0 | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(rectify,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(flattening,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.53  fof(f185,plain,(
% 0.20/0.53    ( ! [X0] : (sK0 != X0 | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2) | ~r2_hidden(sK0,k2_tarski(sK0,X0))) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f179])).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    ( ! [X0] : (sK0 != X0 | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2) | ~r2_hidden(sK0,k2_tarski(sK0,X0)) | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2)) )),
% 0.20/0.53    inference(resolution,[],[f160,f113])).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK1,k9_relat_1(sK2,X0)) | ~r2_hidden(sK0,X0) | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2)) )),
% 0.20/0.53    inference(resolution,[],[f104,f68])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK0,sK1),sK2) | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2)),
% 0.20/0.53    inference(resolution,[],[f102,f32])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k11_relat_1(sK2,X0)) | sK6(X1,k2_tarski(X0,X0),sK2) = X0) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f101,f31])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k11_relat_1(sK2,X0)) | sK6(X1,k2_tarski(X0,X0),sK2) = X0 | ~v1_relat_1(sK2)) )),
% 0.20/0.53    inference(superposition,[],[f94,f52])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK2,k2_tarski(X1,X1))) | sK6(X0,k2_tarski(X1,X1),sK2) = X1) )),
% 0.20/0.53    inference(equality_resolution,[],[f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (X1 != X2 | sK6(X0,k2_tarski(X1,X2),sK2) = X1 | ~r2_hidden(X0,k9_relat_1(sK2,k2_tarski(X1,X2)))) )),
% 0.20/0.53    inference(equality_factoring,[],[f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sK6(X0,k2_tarski(X1,X2),sK2) = X2 | sK6(X0,k2_tarski(X1,X2),sK2) = X1 | ~r2_hidden(X0,k9_relat_1(sK2,k2_tarski(X1,X2)))) )),
% 0.20/0.53    inference(resolution,[],[f63,f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.20/0.53    inference(equality_resolution,[],[f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1,sK2),X1) | ~r2_hidden(X0,k9_relat_1(sK2,X1))) )),
% 0.20/0.53    inference(resolution,[],[f44,f31])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(rectify,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.20/0.53  fof(f160,plain,(
% 0.20/0.53    ( ! [X1] : (~r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,X1))) | sK0 != X1 | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f157,f57])).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    ( ! [X1] : (sK0 != X1 | ~r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,X1))) | ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2)) )),
% 0.20/0.53    inference(resolution,[],[f153,f116])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK1,k11_relat_1(sK2,X0)) | ~r2_hidden(sK0,k2_tarski(X0,X0)) | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f115,f31])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK1,k11_relat_1(sK2,X0)) | ~r2_hidden(sK0,k2_tarski(X0,X0)) | sK0 = sK6(sK1,k2_tarski(sK0,sK0),sK2) | ~v1_relat_1(sK2)) )),
% 0.20/0.53    inference(superposition,[],[f113,f52])).
% 0.20/0.53  fof(f153,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(sK1,k11_relat_1(sK2,sK0)) | sK0 != X0 | ~r2_hidden(sK1,k9_relat_1(sK2,k2_tarski(sK0,X0)))) )),
% 0.20/0.53    inference(resolution,[],[f147,f33])).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    ( ! [X4,X5,X3] : (r2_hidden(k4_tarski(X3,X5),sK2) | ~r2_hidden(X5,k9_relat_1(sK2,k2_tarski(X3,X4))) | X3 != X4) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f144])).
% 0.20/0.53  fof(f144,plain,(
% 0.20/0.53    ( ! [X4,X5,X3] : (r2_hidden(k4_tarski(X3,X5),sK2) | ~r2_hidden(X5,k9_relat_1(sK2,k2_tarski(X3,X4))) | X3 != X4 | ~r2_hidden(X5,k9_relat_1(sK2,k2_tarski(X3,X4)))) )),
% 0.20/0.53    inference(superposition,[],[f70,f139])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sK5(sK2,k2_tarski(X0,X1),X2) = X0 | X0 != X1 | ~r2_hidden(X2,k9_relat_1(sK2,k2_tarski(X0,X1)))) )),
% 0.20/0.53    inference(equality_factoring,[],[f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sK5(sK2,k2_tarski(X1,X2),X0) = X2 | sK5(sK2,k2_tarski(X1,X2),X0) = X1 | ~r2_hidden(X0,k9_relat_1(sK2,k2_tarski(X1,X2)))) )),
% 0.20/0.53    inference(resolution,[],[f64,f60])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,sK2),X0),sK2) | ~r2_hidden(X0,k9_relat_1(sK2,X1))) )),
% 0.20/0.53    inference(resolution,[],[f43,f31])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.20/0.53    inference(equality_resolution,[],[f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.20/0.53    inference(equality_resolution,[],[f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (14516)------------------------------
% 0.20/0.53  % (14516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (14516)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (14516)Memory used [KB]: 6524
% 0.20/0.53  % (14516)Time elapsed: 0.070 s
% 0.20/0.53  % (14516)------------------------------
% 0.20/0.53  % (14516)------------------------------
% 0.20/0.53  % (14493)Success in time 0.167 s
%------------------------------------------------------------------------------
