%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 298 expanded)
%              Number of leaves         :   13 (  83 expanded)
%              Depth                    :   18
%              Number of atoms          :  396 (1679 expanded)
%              Number of equality atoms :   52 ( 187 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f248,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f66,f181,f243])).

fof(f243,plain,(
    ~ spl10_1 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl10_1 ),
    inference(global_subsumption,[],[f30,f54,f231,f233])).

fof(f233,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ spl10_1 ),
    inference(superposition,[],[f190,f202])).

fof(f202,plain,
    ( sK1 = sK7(sK3,k6_relat_1(sK2),sK0,sK1)
    | ~ spl10_1 ),
    inference(resolution,[],[f193,f69])).

fof(f69,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | X4 = X5 ) ),
    inference(subsumption_resolution,[],[f50,f31])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f50,plain,(
    ! [X4,X0,X5] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK8(X0,X1) != sK9(X0,X1)
              | ~ r2_hidden(sK8(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
            & ( ( sK8(X0,X1) = sK9(X0,X1)
                & r2_hidden(sK8(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK8(X0,X1) != sK9(X0,X1)
          | ~ r2_hidden(sK8(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
        & ( ( sK8(X0,X1) = sK9(X0,X1)
            & r2_hidden(sK8(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(f193,plain,
    ( r2_hidden(k4_tarski(sK7(sK3,k6_relat_1(sK2),sK0,sK1),sK1),k6_relat_1(sK2))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f192,f27])).

fof(f27,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
      | ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) )
    & ( ( r2_hidden(k4_tarski(sK0,sK1),sK3)
        & r2_hidden(sK1,sK2) )
      | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
        & v1_relat_1(X3) )
   => ( ( ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
        | ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) )
      & ( ( r2_hidden(k4_tarski(sK0,sK1),sK3)
          & r2_hidden(sK1,sK2) )
        | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
      & ( ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) )
        | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
      & v1_relat_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k4_tarski(X0,X1),X3)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
      & ( ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) )
        | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) )
      & v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <~> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      & v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
        <=> ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).

fof(f192,plain,
    ( r2_hidden(k4_tarski(sK7(sK3,k6_relat_1(sK2),sK0,sK1),sK1),k6_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f191,f31])).

fof(f191,plain,
    ( r2_hidden(k4_tarski(sK7(sK3,k6_relat_1(sK2),sK0,sK1),sK1),k6_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f184,f113])).

fof(f113,plain,(
    ! [X0] : v1_relat_1(k5_relat_1(sK3,k6_relat_1(X0))) ),
    inference(resolution,[],[f72,f27])).

fof(f72,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) ) ),
    inference(resolution,[],[f44,f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1))
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f184,plain,
    ( r2_hidden(k4_tarski(sK7(sK3,k6_relat_1(sK2),sK0,sK1),sK1),k6_relat_1(sK2))
    | ~ v1_relat_1(k5_relat_1(sK3,k6_relat_1(sK2)))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl10_1 ),
    inference(resolution,[],[f54,f46])).

fof(f46,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f17,f20,f19,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
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
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f190,plain,
    ( r2_hidden(k4_tarski(sK0,sK7(sK3,k6_relat_1(sK2),sK0,sK1)),sK3)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f189,f27])).

fof(f189,plain,
    ( r2_hidden(k4_tarski(sK0,sK7(sK3,k6_relat_1(sK2),sK0,sK1)),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f188,f31])).

fof(f188,plain,
    ( r2_hidden(k4_tarski(sK0,sK7(sK3,k6_relat_1(sK2),sK0,sK1)),sK3)
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f183,f113])).

fof(f183,plain,
    ( r2_hidden(k4_tarski(sK0,sK7(sK3,k6_relat_1(sK2),sK0,sK1)),sK3)
    | ~ v1_relat_1(k5_relat_1(sK3,k6_relat_1(sK2)))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl10_1 ),
    inference(resolution,[],[f54,f47])).

fof(f47,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f231,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl10_1 ),
    inference(superposition,[],[f201,f202])).

fof(f201,plain,
    ( r2_hidden(sK7(sK3,k6_relat_1(sK2),sK0,sK1),sK2)
    | ~ spl10_1 ),
    inference(resolution,[],[f193,f70])).

fof(f70,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f51,f31])).

fof(f51,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2)))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl10_1
  <=> r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f30,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f181,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f179,f27])).

fof(f179,plain,
    ( ~ v1_relat_1(sK3)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f177,f55])).

fof(f55,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2)))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f177,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2)))
    | ~ v1_relat_1(sK3)
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(resolution,[],[f106,f62])).

fof(f62,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl10_3
  <=> r2_hidden(k4_tarski(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,sK1),X1)
        | r2_hidden(k4_tarski(X0,sK1),k5_relat_1(X1,k6_relat_1(sK2)))
        | ~ v1_relat_1(X1) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f105,f72])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK1),k5_relat_1(X1,k6_relat_1(sK2)))
        | ~ r2_hidden(k4_tarski(X0,sK1),X1)
        | ~ v1_relat_1(k5_relat_1(X1,k6_relat_1(sK2)))
        | ~ v1_relat_1(X1) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f103,f31])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK1),k5_relat_1(X1,k6_relat_1(sK2)))
        | ~ r2_hidden(k4_tarski(X0,sK1),X1)
        | ~ v1_relat_1(k5_relat_1(X1,k6_relat_1(sK2)))
        | ~ v1_relat_1(k6_relat_1(sK2))
        | ~ v1_relat_1(X1) )
    | ~ spl10_2 ),
    inference(resolution,[],[f73,f45])).

fof(f45,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( ~ r2_hidden(k4_tarski(X9,X8),X1)
      | r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),k6_relat_1(sK2))
    | ~ spl10_2 ),
    inference(resolution,[],[f68,f58])).

fof(f58,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl10_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f68,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,X0)
      | r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f49,f31])).

fof(f49,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f28,f57,f53])).

fof(f28,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,
    ( spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f29,f61,f53])).

fof(f29,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK3)
    | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n012.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:33:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (8049)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (8043)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (8041)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (8044)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (8045)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (8047)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (8039)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (8063)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (8050)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (8049)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (8040)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (8062)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (8056)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (8042)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (8057)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (8040)Refutation not found, incomplete strategy% (8040)------------------------------
% 0.21/0.53  % (8040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8040)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8040)Memory used [KB]: 10618
% 0.21/0.53  % (8040)Time elapsed: 0.086 s
% 0.21/0.53  % (8040)------------------------------
% 0.21/0.53  % (8040)------------------------------
% 0.21/0.53  % (8060)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (8055)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (8054)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f248,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f65,f66,f181,f243])).
% 0.21/0.53  fof(f243,plain,(
% 0.21/0.53    ~spl10_1),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f242])).
% 0.21/0.53  fof(f242,plain,(
% 0.21/0.53    $false | ~spl10_1),
% 0.21/0.53    inference(global_subsumption,[],[f30,f54,f231,f233])).
% 0.21/0.53  fof(f233,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK0,sK1),sK3) | ~spl10_1),
% 0.21/0.53    inference(superposition,[],[f190,f202])).
% 0.21/0.53  fof(f202,plain,(
% 0.21/0.53    sK1 = sK7(sK3,k6_relat_1(sK2),sK0,sK1) | ~spl10_1),
% 0.21/0.53    inference(resolution,[],[f193,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X4,X0,X5] : (~r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0)) | X4 = X5) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f50,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X4,X0,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X4,X0,X5,X1] : (X4 = X5 | ~r2_hidden(k4_tarski(X4,X5),X1) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ((sK8(X0,X1) != sK9(X0,X1) | ~r2_hidden(sK8(X0,X1),X0) | ~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) & ((sK8(X0,X1) = sK9(X0,X1) & r2_hidden(sK8(X0,X1),X0)) | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f24,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1))) => ((sK8(X0,X1) != sK9(X0,X1) | ~r2_hidden(sK8(X0,X1),X0) | ~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) & ((sK8(X0,X1) = sK9(X0,X1) & r2_hidden(sK8(X0,X1),X0)) | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(rectify,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : (((X2 != X3 | ~r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK7(sK3,k6_relat_1(sK2),sK0,sK1),sK1),k6_relat_1(sK2)) | ~spl10_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f192,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    v1_relat_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    (~r2_hidden(k4_tarski(sK0,sK1),sK3) | ~r2_hidden(sK1,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2)))) & ((r2_hidden(k4_tarski(sK0,sK1),sK3) & r2_hidden(sK1,sK2)) | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2)))) & v1_relat_1(sK3)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))) & v1_relat_1(X3)) => ((~r2_hidden(k4_tarski(sK0,sK1),sK3) | ~r2_hidden(sK1,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2)))) & ((r2_hidden(k4_tarski(sK0,sK1),sK3) & r2_hidden(sK1,sK2)) | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2)))) & v1_relat_1(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))) & v1_relat_1(X3))),
% 0.21/0.53    inference(flattening,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((((~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) & v1_relat_1(X3))),
% 0.21/0.53    inference(nnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <~> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))) & v1_relat_1(X3))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))))),
% 0.21/0.53    inference(negated_conjecture,[],[f5])).
% 0.21/0.53  fof(f5,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK7(sK3,k6_relat_1(sK2),sK0,sK1),sK1),k6_relat_1(sK2)) | ~v1_relat_1(sK3) | ~spl10_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f191,f31])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK7(sK3,k6_relat_1(sK2),sK0,sK1),sK1),k6_relat_1(sK2)) | ~v1_relat_1(k6_relat_1(sK2)) | ~v1_relat_1(sK3) | ~spl10_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f184,f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(k5_relat_1(sK3,k6_relat_1(X0)))) )),
% 0.21/0.53    inference(resolution,[],[f72,f27])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))) )),
% 0.21/0.53    inference(resolution,[],[f44,f31])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK7(sK3,k6_relat_1(sK2),sK0,sK1),sK1),k6_relat_1(sK2)) | ~v1_relat_1(k5_relat_1(sK3,k6_relat_1(sK2))) | ~v1_relat_1(k6_relat_1(sK2)) | ~v1_relat_1(sK3) | ~spl10_1),
% 0.21/0.53    inference(resolution,[],[f54,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X8,X7,X1] : (~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f17,f20,f19,f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK5(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK6(X0,X1,X2)),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK7(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(rectify,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK0,sK7(sK3,k6_relat_1(sK2),sK0,sK1)),sK3) | ~spl10_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f189,f27])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK0,sK7(sK3,k6_relat_1(sK2),sK0,sK1)),sK3) | ~v1_relat_1(sK3) | ~spl10_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f188,f31])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK0,sK7(sK3,k6_relat_1(sK2),sK0,sK1)),sK3) | ~v1_relat_1(k6_relat_1(sK2)) | ~v1_relat_1(sK3) | ~spl10_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f183,f113])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK0,sK7(sK3,k6_relat_1(sK2),sK0,sK1)),sK3) | ~v1_relat_1(k5_relat_1(sK3,k6_relat_1(sK2))) | ~v1_relat_1(k6_relat_1(sK2)) | ~v1_relat_1(sK3) | ~spl10_1),
% 0.21/0.53    inference(resolution,[],[f54,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X8,X7,X1] : (~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK7(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    r2_hidden(sK1,sK2) | ~spl10_1),
% 0.21/0.53    inference(superposition,[],[f201,f202])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    r2_hidden(sK7(sK3,k6_relat_1(sK2),sK0,sK1),sK2) | ~spl10_1),
% 0.21/0.53    inference(resolution,[],[f193,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X4,X0,X5] : (~r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0)) | r2_hidden(X4,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f51,f31])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X4,X0,X5] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X4,X0,X5,X1] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X5),X1) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) | ~spl10_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    spl10_1 <=> r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ~r2_hidden(k4_tarski(sK0,sK1),sK3) | ~r2_hidden(sK1,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2)))),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    spl10_1 | ~spl10_2 | ~spl10_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f180])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    $false | (spl10_1 | ~spl10_2 | ~spl10_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f179,f27])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    ~v1_relat_1(sK3) | (spl10_1 | ~spl10_2 | ~spl10_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f177,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ~r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) | spl10_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f53])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2))) | ~v1_relat_1(sK3) | (~spl10_2 | ~spl10_3)),
% 0.21/0.53    inference(resolution,[],[f106,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK0,sK1),sK3) | ~spl10_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    spl10_3 <=> r2_hidden(k4_tarski(sK0,sK1),sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK1),X1) | r2_hidden(k4_tarski(X0,sK1),k5_relat_1(X1,k6_relat_1(sK2))) | ~v1_relat_1(X1)) ) | ~spl10_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f105,f72])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK1),k5_relat_1(X1,k6_relat_1(sK2))) | ~r2_hidden(k4_tarski(X0,sK1),X1) | ~v1_relat_1(k5_relat_1(X1,k6_relat_1(sK2))) | ~v1_relat_1(X1)) ) | ~spl10_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f103,f31])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK1),k5_relat_1(X1,k6_relat_1(sK2))) | ~r2_hidden(k4_tarski(X0,sK1),X1) | ~v1_relat_1(k5_relat_1(X1,k6_relat_1(sK2))) | ~v1_relat_1(k6_relat_1(sK2)) | ~v1_relat_1(X1)) ) | ~spl10_2),
% 0.21/0.53    inference(resolution,[],[f73,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X8,X7,X1,X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK1,sK1),k6_relat_1(sK2)) | ~spl10_2),
% 0.21/0.53    inference(resolution,[],[f68,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    r2_hidden(sK1,sK2) | ~spl10_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    spl10_2 <=> r2_hidden(sK1,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0,X5] : (~r2_hidden(X5,X0) | r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f49,f31])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0)) | ~r2_hidden(X5,X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,X5),X1) | ~r2_hidden(X5,X0) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    spl10_1 | spl10_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f28,f57,f53])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    r2_hidden(sK1,sK2) | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2)))),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    spl10_1 | spl10_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f29,f61,f53])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK0,sK1),sK3) | r2_hidden(k4_tarski(sK0,sK1),k5_relat_1(sK3,k6_relat_1(sK2)))),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (8049)------------------------------
% 0.21/0.53  % (8049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8049)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (8049)Memory used [KB]: 10874
% 0.21/0.53  % (8049)Time elapsed: 0.106 s
% 0.21/0.53  % (8049)------------------------------
% 0.21/0.53  % (8049)------------------------------
% 0.21/0.54  % (8038)Success in time 0.175 s
%------------------------------------------------------------------------------
