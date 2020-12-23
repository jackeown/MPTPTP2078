%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:19 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 520 expanded)
%              Number of clauses        :   87 ( 150 expanded)
%              Number of leaves         :   16 ( 152 expanded)
%              Depth                    :   13
%              Number of atoms          :  478 (3302 expanded)
%              Number of equality atoms :  167 ( 833 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ? [X1] :
              ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & v1_funct_1(X1)
              & v1_relat_1(X1) )
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k5_relat_1(X0,sK5) = k6_relat_1(k1_relat_1(X0))
        & v1_funct_1(sK5)
        & v1_relat_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK4)
      & ? [X1] :
          ( k5_relat_1(sK4,X1) = k6_relat_1(k1_relat_1(sK4))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ v2_funct_1(sK4)
    & k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4))
    & v1_funct_1(sK5)
    & v1_relat_1(sK5)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f15,f26,f25])).

fof(f48,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
              | k1_relat_1(X1) != k1_relat_1(X2)
              | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
              | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                & k1_relat_1(X1) = k1_relat_1(X2)
                & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) ) )
      & ( ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f21,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                & k1_relat_1(X1) = k1_relat_1(X2)
                & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( X3 = X4
                | k5_relat_1(X3,X0) != k5_relat_1(X4,X0)
                | k1_relat_1(X3) != k1_relat_1(X4)
                | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X0))
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
          & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( sK3(X0) != X1
        & k5_relat_1(X1,X0) = k5_relat_1(sK3(X0),X0)
        & k1_relat_1(X1) = k1_relat_1(sK3(X0))
        & r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))
        & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
              & k1_relat_1(X1) = k1_relat_1(X2)
              & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
              & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( sK2(X0) != X2
            & k5_relat_1(X2,X0) = k5_relat_1(sK2(X0),X0)
            & k1_relat_1(X2) = k1_relat_1(sK2(X0))
            & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
            & r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(sK2(X0))
        & v1_relat_1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK2(X0) != sK3(X0)
          & k5_relat_1(sK2(X0),X0) = k5_relat_1(sK3(X0),X0)
          & k1_relat_1(sK2(X0)) = k1_relat_1(sK3(X0))
          & r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))
          & r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))
          & v1_funct_1(sK3(X0))
          & v1_relat_1(sK3(X0))
          & v1_funct_1(sK2(X0))
          & v1_relat_1(sK2(X0)) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( X3 = X4
                | k5_relat_1(X3,X0) != k5_relat_1(X4,X0)
                | k1_relat_1(X3) != k1_relat_1(X4)
                | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X0))
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f23,f22])).

fof(f39,plain,(
    ! [X0] :
      ( sP0(X0)
      | v1_relat_1(sK3(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ sP0(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                    & k1_relat_1(X1) = k1_relat_1(X2)
                    & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                    & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) )
                 => X1 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f18,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f13,f17,f16])).

fof(f46,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0] :
      ( sP0(X0)
      | k5_relat_1(sK2(X0),X0) = k5_relat_1(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    ! [X0] :
      ( sP0(X0)
      | v1_relat_1(sK2(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k5_relat_1(X3,X0) != k5_relat_1(X4,X0)
      | k1_relat_1(X3) != k1_relat_1(X4)
      | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X0] :
      ( sP0(X0)
      | k1_relat_1(sK2(X0)) = k1_relat_1(sK3(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0] :
      ( sP0(X0)
      | sK2(X0) != sK3(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0] :
      ( sP0(X0)
      | r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X0] :
      ( sP0(X0)
      | r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X0] :
      ( sP0(X0)
      | v1_funct_1(sK3(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    ! [X0] :
      ( sP0(X0)
      | v1_funct_1(sK2(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_25,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1838,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1840,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( sP0(X0)
    | v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1845,plain,
    ( sP0(X0) = iProver_top
    | v1_relat_1(sK3(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1854,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2624,plain,
    ( k5_relat_1(sK3(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(sK3(X0),X1),X2)
    | sP0(X0) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1845,c_1854])).

cnf(c_10023,plain,
    ( k5_relat_1(k5_relat_1(sK3(X0),X1),sK5) = k5_relat_1(sK3(X0),k5_relat_1(X1,sK5))
    | sP0(X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1840,c_2624])).

cnf(c_10477,plain,
    ( k5_relat_1(k5_relat_1(sK3(X0),sK4),sK5) = k5_relat_1(sK3(X0),k5_relat_1(sK4,sK5))
    | sP0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_10023])).

cnf(c_21,negated_conjecture,
    ( k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_10478,plain,
    ( k5_relat_1(k5_relat_1(sK3(X0),sK4),sK5) = k5_relat_1(sK3(X0),k6_relat_1(k1_relat_1(sK4)))
    | sP0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10477,c_21])).

cnf(c_6,plain,
    ( ~ sP1(X0)
    | ~ sP0(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_20,negated_conjecture,
    ( ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_279,plain,
    ( ~ sP1(X0)
    | ~ sP0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_280,plain,
    ( ~ sP1(sK4)
    | ~ sP0(sK4) ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_18,plain,
    ( sP1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_35,plain,
    ( sP1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_69,plain,
    ( ~ sP1(sK4)
    | ~ sP0(sK4)
    | v2_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_282,plain,
    ( ~ sP0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_280,c_25,c_24,c_20,c_35,c_69])).

cnf(c_1837,plain,
    ( sP0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_10640,plain,
    ( k5_relat_1(k5_relat_1(sK3(sK4),sK4),sK5) = k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4))) ),
    inference(superposition,[status(thm)],[c_10478,c_1837])).

cnf(c_9,plain,
    ( sP0(X0)
    | k5_relat_1(sK3(X0),X0) = k5_relat_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1850,plain,
    ( k5_relat_1(sK3(X0),X0) = k5_relat_1(sK2(X0),X0)
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3381,plain,
    ( k5_relat_1(sK2(sK4),sK4) = k5_relat_1(sK3(sK4),sK4) ),
    inference(superposition,[status(thm)],[c_1850,c_1837])).

cnf(c_16,plain,
    ( sP0(X0)
    | v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1843,plain,
    ( sP0(X0) = iProver_top
    | v1_relat_1(sK2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2396,plain,
    ( k5_relat_1(sK2(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(sK2(X0),X1),X2)
    | sP0(X0) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1843,c_1854])).

cnf(c_4892,plain,
    ( k5_relat_1(k5_relat_1(sK2(X0),X1),sK5) = k5_relat_1(sK2(X0),k5_relat_1(X1,sK5))
    | sP0(X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1840,c_2396])).

cnf(c_6060,plain,
    ( k5_relat_1(k5_relat_1(sK2(X0),sK4),sK5) = k5_relat_1(sK2(X0),k5_relat_1(sK4,sK5))
    | sP0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_4892])).

cnf(c_6061,plain,
    ( k5_relat_1(k5_relat_1(sK2(X0),sK4),sK5) = k5_relat_1(sK2(X0),k6_relat_1(k1_relat_1(sK4)))
    | sP0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6060,c_21])).

cnf(c_6078,plain,
    ( k5_relat_1(k5_relat_1(sK2(sK4),sK4),sK5) = k5_relat_1(sK2(sK4),k6_relat_1(k1_relat_1(sK4))) ),
    inference(superposition,[status(thm)],[c_6061,c_1837])).

cnf(c_10641,plain,
    ( k5_relat_1(sK2(sK4),k6_relat_1(k1_relat_1(sK4))) = k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4))) ),
    inference(light_normalisation,[status(thm)],[c_10640,c_3381,c_6078])).

cnf(c_17,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
    | ~ sP0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | X0 = X2
    | k5_relat_1(X0,X1) != k5_relat_1(X2,X1)
    | k1_relat_1(X0) != k1_relat_1(X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2116,plain,
    ( ~ r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(X0))
    | ~ r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(X0))
    | ~ sP0(X0)
    | ~ v1_funct_1(sK3(sK4))
    | ~ v1_funct_1(sK2(sK4))
    | ~ v1_relat_1(sK3(sK4))
    | ~ v1_relat_1(sK2(sK4))
    | k5_relat_1(sK2(sK4),X0) != k5_relat_1(sK3(sK4),X0)
    | sK2(sK4) = sK3(sK4)
    | k1_relat_1(sK2(sK4)) != k1_relat_1(sK3(sK4)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4054,plain,
    ( ~ r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(k6_relat_1(X0)))
    | ~ r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(k6_relat_1(X0)))
    | ~ sP0(k6_relat_1(X0))
    | ~ v1_funct_1(sK3(sK4))
    | ~ v1_funct_1(sK2(sK4))
    | ~ v1_relat_1(sK3(sK4))
    | ~ v1_relat_1(sK2(sK4))
    | k5_relat_1(sK2(sK4),k6_relat_1(X0)) != k5_relat_1(sK3(sK4),k6_relat_1(X0))
    | sK2(sK4) = sK3(sK4)
    | k1_relat_1(sK2(sK4)) != k1_relat_1(sK3(sK4)) ),
    inference(instantiation,[status(thm)],[c_2116])).

cnf(c_6774,plain,
    ( ~ r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(k6_relat_1(k1_relat_1(sK4))))
    | ~ r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(k6_relat_1(k1_relat_1(sK4))))
    | ~ sP0(k6_relat_1(k1_relat_1(sK4)))
    | ~ v1_funct_1(sK3(sK4))
    | ~ v1_funct_1(sK2(sK4))
    | ~ v1_relat_1(sK3(sK4))
    | ~ v1_relat_1(sK2(sK4))
    | k5_relat_1(sK2(sK4),k6_relat_1(k1_relat_1(sK4))) != k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4)))
    | sK2(sK4) = sK3(sK4)
    | k1_relat_1(sK2(sK4)) != k1_relat_1(sK3(sK4)) ),
    inference(instantiation,[status(thm)],[c_4054])).

cnf(c_1485,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5315,plain,
    ( sK2(X0) = sK2(X0) ),
    inference(instantiation,[status(thm)],[c_1485])).

cnf(c_5316,plain,
    ( sK2(sK4) = sK2(sK4) ),
    inference(instantiation,[status(thm)],[c_5315])).

cnf(c_1490,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2055,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X2),k1_relat_1(k6_relat_1(X3)))
    | k2_relat_1(X2) != X0
    | k1_relat_1(k6_relat_1(X3)) != X1 ),
    inference(instantiation,[status(thm)],[c_1490])).

cnf(c_2217,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(k6_relat_1(X1)))
    | ~ r1_tarski(k2_relat_1(sK2(X2)),k1_relat_1(X2))
    | k2_relat_1(X0) != k2_relat_1(sK2(X2))
    | k1_relat_1(k6_relat_1(X1)) != k1_relat_1(X2) ),
    inference(instantiation,[status(thm)],[c_2055])).

cnf(c_2862,plain,
    ( ~ r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))
    | r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(k6_relat_1(X1)))
    | k2_relat_1(sK2(X0)) != k2_relat_1(sK2(X0))
    | k1_relat_1(k6_relat_1(X1)) != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_2217])).

cnf(c_4504,plain,
    ( r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(k6_relat_1(k1_relat_1(sK4))))
    | ~ r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(sK4))
    | k2_relat_1(sK2(sK4)) != k2_relat_1(sK2(sK4))
    | k1_relat_1(k6_relat_1(k1_relat_1(sK4))) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2862])).

cnf(c_2214,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(k6_relat_1(X1)))
    | ~ r1_tarski(k2_relat_1(sK3(X2)),k1_relat_1(X2))
    | k2_relat_1(X0) != k2_relat_1(sK3(X2))
    | k1_relat_1(k6_relat_1(X1)) != k1_relat_1(X2) ),
    inference(instantiation,[status(thm)],[c_2055])).

cnf(c_2849,plain,
    ( ~ r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))
    | r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(k6_relat_1(X1)))
    | k2_relat_1(sK3(X0)) != k2_relat_1(sK3(X0))
    | k1_relat_1(k6_relat_1(X1)) != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_2214])).

cnf(c_4480,plain,
    ( r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(k6_relat_1(k1_relat_1(sK4))))
    | ~ r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(sK4))
    | k2_relat_1(sK3(sK4)) != k2_relat_1(sK3(sK4))
    | k1_relat_1(k6_relat_1(k1_relat_1(sK4))) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2849])).

cnf(c_1489,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_2868,plain,
    ( X0 != sK2(X1)
    | k2_relat_1(X0) = k2_relat_1(sK2(X1)) ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_4275,plain,
    ( sK2(X0) != sK2(X0)
    | k2_relat_1(sK2(X0)) = k2_relat_1(sK2(X0)) ),
    inference(instantiation,[status(thm)],[c_2868])).

cnf(c_4276,plain,
    ( sK2(sK4) != sK2(sK4)
    | k2_relat_1(sK2(sK4)) = k2_relat_1(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_4275])).

cnf(c_2719,plain,
    ( k2_relat_1(sK3(sK4)) = k2_relat_1(sK3(sK4)) ),
    inference(instantiation,[status(thm)],[c_1485])).

cnf(c_10,plain,
    ( sP0(X0)
    | k1_relat_1(sK3(X0)) = k1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1849,plain,
    ( k1_relat_1(sK3(X0)) = k1_relat_1(sK2(X0))
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2680,plain,
    ( k1_relat_1(sK2(sK4)) = k1_relat_1(sK3(sK4)) ),
    inference(superposition,[status(thm)],[c_1849,c_1837])).

cnf(c_3,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2537,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(sK4))) = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( ~ sP1(X0)
    | sP0(X0)
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_19,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_267,plain,
    ( ~ sP1(X0)
    | sP0(X0)
    | k6_relat_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_268,plain,
    ( ~ sP1(k6_relat_1(X0))
    | sP0(k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_301,plain,
    ( sP0(k6_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k6_relat_1(X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_268])).

cnf(c_302,plain,
    ( sP0(k6_relat_1(X0))
    | ~ v1_funct_1(k6_relat_1(X0))
    | ~ v1_relat_1(k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_5,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_4,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_306,plain,
    ( sP0(k6_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_302,c_5,c_4])).

cnf(c_2109,plain,
    ( sP0(k6_relat_1(k1_relat_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_1964,plain,
    ( sK3(sK4) = sK3(sK4) ),
    inference(instantiation,[status(thm)],[c_1485])).

cnf(c_1486,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1894,plain,
    ( sK3(sK4) != X0
    | sK3(sK4) = sK2(sK4)
    | sK2(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_1925,plain,
    ( sK3(sK4) != sK3(sK4)
    | sK3(sK4) = sK2(sK4)
    | sK2(sK4) != sK3(sK4) ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_8,plain,
    ( sP0(X0)
    | sK3(X0) != sK2(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_65,plain,
    ( sP0(sK4)
    | sK3(sK4) != sK2(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_11,plain,
    ( r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_56,plain,
    ( r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(sK4))
    | sP0(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_53,plain,
    ( r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(sK4))
    | sP0(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( sP0(X0)
    | v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_50,plain,
    ( sP0(sK4)
    | v1_funct_1(sK3(sK4)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_47,plain,
    ( sP0(sK4)
    | v1_relat_1(sK3(sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_15,plain,
    ( sP0(X0)
    | v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_44,plain,
    ( sP0(sK4)
    | v1_funct_1(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_41,plain,
    ( sP0(sK4)
    | v1_relat_1(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10641,c_6774,c_5316,c_4504,c_4480,c_4276,c_2719,c_2680,c_2537,c_2109,c_1964,c_1925,c_69,c_65,c_56,c_53,c_50,c_47,c_44,c_41,c_35,c_20,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:16:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.07/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.07/0.98  
% 4.07/0.98  ------  iProver source info
% 4.07/0.98  
% 4.07/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.07/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.07/0.98  git: non_committed_changes: false
% 4.07/0.98  git: last_make_outside_of_git: false
% 4.07/0.98  
% 4.07/0.98  ------ 
% 4.07/0.98  
% 4.07/0.98  ------ Input Options
% 4.07/0.98  
% 4.07/0.98  --out_options                           all
% 4.07/0.98  --tptp_safe_out                         true
% 4.07/0.98  --problem_path                          ""
% 4.07/0.98  --include_path                          ""
% 4.07/0.98  --clausifier                            res/vclausify_rel
% 4.07/0.98  --clausifier_options                    ""
% 4.07/0.98  --stdin                                 false
% 4.07/0.98  --stats_out                             all
% 4.07/0.98  
% 4.07/0.98  ------ General Options
% 4.07/0.98  
% 4.07/0.98  --fof                                   false
% 4.07/0.98  --time_out_real                         305.
% 4.07/0.98  --time_out_virtual                      -1.
% 4.07/0.98  --symbol_type_check                     false
% 4.07/0.98  --clausify_out                          false
% 4.07/0.98  --sig_cnt_out                           false
% 4.07/0.98  --trig_cnt_out                          false
% 4.07/0.98  --trig_cnt_out_tolerance                1.
% 4.07/0.98  --trig_cnt_out_sk_spl                   false
% 4.07/0.98  --abstr_cl_out                          false
% 4.07/0.98  
% 4.07/0.98  ------ Global Options
% 4.07/0.98  
% 4.07/0.98  --schedule                              default
% 4.07/0.98  --add_important_lit                     false
% 4.07/0.98  --prop_solver_per_cl                    1000
% 4.07/0.98  --min_unsat_core                        false
% 4.07/0.98  --soft_assumptions                      false
% 4.07/0.98  --soft_lemma_size                       3
% 4.07/0.98  --prop_impl_unit_size                   0
% 4.07/0.98  --prop_impl_unit                        []
% 4.07/0.98  --share_sel_clauses                     true
% 4.07/0.98  --reset_solvers                         false
% 4.07/0.98  --bc_imp_inh                            [conj_cone]
% 4.07/0.98  --conj_cone_tolerance                   3.
% 4.07/0.98  --extra_neg_conj                        none
% 4.07/0.98  --large_theory_mode                     true
% 4.07/0.98  --prolific_symb_bound                   200
% 4.07/0.98  --lt_threshold                          2000
% 4.07/0.98  --clause_weak_htbl                      true
% 4.07/0.98  --gc_record_bc_elim                     false
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing Options
% 4.07/0.98  
% 4.07/0.98  --preprocessing_flag                    true
% 4.07/0.98  --time_out_prep_mult                    0.1
% 4.07/0.98  --splitting_mode                        input
% 4.07/0.98  --splitting_grd                         true
% 4.07/0.98  --splitting_cvd                         false
% 4.07/0.98  --splitting_cvd_svl                     false
% 4.07/0.98  --splitting_nvd                         32
% 4.07/0.98  --sub_typing                            true
% 4.07/0.98  --prep_gs_sim                           true
% 4.07/0.98  --prep_unflatten                        true
% 4.07/0.98  --prep_res_sim                          true
% 4.07/0.98  --prep_upred                            true
% 4.07/0.98  --prep_sem_filter                       exhaustive
% 4.07/0.98  --prep_sem_filter_out                   false
% 4.07/0.98  --pred_elim                             true
% 4.07/0.98  --res_sim_input                         true
% 4.07/0.98  --eq_ax_congr_red                       true
% 4.07/0.98  --pure_diseq_elim                       true
% 4.07/0.98  --brand_transform                       false
% 4.07/0.98  --non_eq_to_eq                          false
% 4.07/0.98  --prep_def_merge                        true
% 4.07/0.98  --prep_def_merge_prop_impl              false
% 4.07/0.98  --prep_def_merge_mbd                    true
% 4.07/0.98  --prep_def_merge_tr_red                 false
% 4.07/0.98  --prep_def_merge_tr_cl                  false
% 4.07/0.98  --smt_preprocessing                     true
% 4.07/0.98  --smt_ac_axioms                         fast
% 4.07/0.98  --preprocessed_out                      false
% 4.07/0.98  --preprocessed_stats                    false
% 4.07/0.98  
% 4.07/0.98  ------ Abstraction refinement Options
% 4.07/0.98  
% 4.07/0.98  --abstr_ref                             []
% 4.07/0.98  --abstr_ref_prep                        false
% 4.07/0.98  --abstr_ref_until_sat                   false
% 4.07/0.98  --abstr_ref_sig_restrict                funpre
% 4.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.07/0.98  --abstr_ref_under                       []
% 4.07/0.98  
% 4.07/0.98  ------ SAT Options
% 4.07/0.98  
% 4.07/0.98  --sat_mode                              false
% 4.07/0.98  --sat_fm_restart_options                ""
% 4.07/0.98  --sat_gr_def                            false
% 4.07/0.98  --sat_epr_types                         true
% 4.07/0.98  --sat_non_cyclic_types                  false
% 4.07/0.98  --sat_finite_models                     false
% 4.07/0.98  --sat_fm_lemmas                         false
% 4.07/0.98  --sat_fm_prep                           false
% 4.07/0.98  --sat_fm_uc_incr                        true
% 4.07/0.98  --sat_out_model                         small
% 4.07/0.98  --sat_out_clauses                       false
% 4.07/0.98  
% 4.07/0.98  ------ QBF Options
% 4.07/0.98  
% 4.07/0.98  --qbf_mode                              false
% 4.07/0.98  --qbf_elim_univ                         false
% 4.07/0.98  --qbf_dom_inst                          none
% 4.07/0.98  --qbf_dom_pre_inst                      false
% 4.07/0.98  --qbf_sk_in                             false
% 4.07/0.98  --qbf_pred_elim                         true
% 4.07/0.98  --qbf_split                             512
% 4.07/0.98  
% 4.07/0.98  ------ BMC1 Options
% 4.07/0.98  
% 4.07/0.98  --bmc1_incremental                      false
% 4.07/0.98  --bmc1_axioms                           reachable_all
% 4.07/0.98  --bmc1_min_bound                        0
% 4.07/0.98  --bmc1_max_bound                        -1
% 4.07/0.98  --bmc1_max_bound_default                -1
% 4.07/0.98  --bmc1_symbol_reachability              true
% 4.07/0.98  --bmc1_property_lemmas                  false
% 4.07/0.98  --bmc1_k_induction                      false
% 4.07/0.98  --bmc1_non_equiv_states                 false
% 4.07/0.98  --bmc1_deadlock                         false
% 4.07/0.98  --bmc1_ucm                              false
% 4.07/0.98  --bmc1_add_unsat_core                   none
% 4.07/0.98  --bmc1_unsat_core_children              false
% 4.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.07/0.98  --bmc1_out_stat                         full
% 4.07/0.98  --bmc1_ground_init                      false
% 4.07/0.98  --bmc1_pre_inst_next_state              false
% 4.07/0.98  --bmc1_pre_inst_state                   false
% 4.07/0.98  --bmc1_pre_inst_reach_state             false
% 4.07/0.98  --bmc1_out_unsat_core                   false
% 4.07/0.98  --bmc1_aig_witness_out                  false
% 4.07/0.98  --bmc1_verbose                          false
% 4.07/0.98  --bmc1_dump_clauses_tptp                false
% 4.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.07/0.98  --bmc1_dump_file                        -
% 4.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.07/0.98  --bmc1_ucm_extend_mode                  1
% 4.07/0.98  --bmc1_ucm_init_mode                    2
% 4.07/0.98  --bmc1_ucm_cone_mode                    none
% 4.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.07/0.98  --bmc1_ucm_relax_model                  4
% 4.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.07/0.98  --bmc1_ucm_layered_model                none
% 4.07/0.98  --bmc1_ucm_max_lemma_size               10
% 4.07/0.98  
% 4.07/0.98  ------ AIG Options
% 4.07/0.98  
% 4.07/0.98  --aig_mode                              false
% 4.07/0.98  
% 4.07/0.98  ------ Instantiation Options
% 4.07/0.98  
% 4.07/0.98  --instantiation_flag                    true
% 4.07/0.98  --inst_sos_flag                         true
% 4.07/0.98  --inst_sos_phase                        true
% 4.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.07/0.98  --inst_lit_sel_side                     num_symb
% 4.07/0.98  --inst_solver_per_active                1400
% 4.07/0.98  --inst_solver_calls_frac                1.
% 4.07/0.98  --inst_passive_queue_type               priority_queues
% 4.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.07/0.98  --inst_passive_queues_freq              [25;2]
% 4.07/0.98  --inst_dismatching                      true
% 4.07/0.98  --inst_eager_unprocessed_to_passive     true
% 4.07/0.98  --inst_prop_sim_given                   true
% 4.07/0.98  --inst_prop_sim_new                     false
% 4.07/0.98  --inst_subs_new                         false
% 4.07/0.98  --inst_eq_res_simp                      false
% 4.07/0.98  --inst_subs_given                       false
% 4.07/0.98  --inst_orphan_elimination               true
% 4.07/0.98  --inst_learning_loop_flag               true
% 4.07/0.98  --inst_learning_start                   3000
% 4.07/0.98  --inst_learning_factor                  2
% 4.07/0.98  --inst_start_prop_sim_after_learn       3
% 4.07/0.98  --inst_sel_renew                        solver
% 4.07/0.98  --inst_lit_activity_flag                true
% 4.07/0.98  --inst_restr_to_given                   false
% 4.07/0.98  --inst_activity_threshold               500
% 4.07/0.98  --inst_out_proof                        true
% 4.07/0.98  
% 4.07/0.98  ------ Resolution Options
% 4.07/0.98  
% 4.07/0.98  --resolution_flag                       true
% 4.07/0.98  --res_lit_sel                           adaptive
% 4.07/0.98  --res_lit_sel_side                      none
% 4.07/0.98  --res_ordering                          kbo
% 4.07/0.98  --res_to_prop_solver                    active
% 4.07/0.98  --res_prop_simpl_new                    false
% 4.07/0.98  --res_prop_simpl_given                  true
% 4.07/0.98  --res_passive_queue_type                priority_queues
% 4.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.07/0.98  --res_passive_queues_freq               [15;5]
% 4.07/0.98  --res_forward_subs                      full
% 4.07/0.98  --res_backward_subs                     full
% 4.07/0.98  --res_forward_subs_resolution           true
% 4.07/0.98  --res_backward_subs_resolution          true
% 4.07/0.98  --res_orphan_elimination                true
% 4.07/0.98  --res_time_limit                        2.
% 4.07/0.98  --res_out_proof                         true
% 4.07/0.98  
% 4.07/0.98  ------ Superposition Options
% 4.07/0.98  
% 4.07/0.98  --superposition_flag                    true
% 4.07/0.98  --sup_passive_queue_type                priority_queues
% 4.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.07/0.98  --demod_completeness_check              fast
% 4.07/0.98  --demod_use_ground                      true
% 4.07/0.98  --sup_to_prop_solver                    passive
% 4.07/0.98  --sup_prop_simpl_new                    true
% 4.07/0.98  --sup_prop_simpl_given                  true
% 4.07/0.98  --sup_fun_splitting                     true
% 4.07/0.98  --sup_smt_interval                      50000
% 4.07/0.98  
% 4.07/0.98  ------ Superposition Simplification Setup
% 4.07/0.98  
% 4.07/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.07/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.07/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.07/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.07/0.98  --sup_immed_triv                        [TrivRules]
% 4.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_immed_bw_main                     []
% 4.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_input_bw                          []
% 4.07/0.98  
% 4.07/0.98  ------ Combination Options
% 4.07/0.98  
% 4.07/0.98  --comb_res_mult                         3
% 4.07/0.98  --comb_sup_mult                         2
% 4.07/0.98  --comb_inst_mult                        10
% 4.07/0.98  
% 4.07/0.98  ------ Debug Options
% 4.07/0.98  
% 4.07/0.98  --dbg_backtrace                         false
% 4.07/0.98  --dbg_dump_prop_clauses                 false
% 4.07/0.98  --dbg_dump_prop_clauses_file            -
% 4.07/0.98  --dbg_out_stat                          false
% 4.07/0.98  ------ Parsing...
% 4.07/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.07/0.98  ------ Proving...
% 4.07/0.98  ------ Problem Properties 
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  clauses                                 24
% 4.07/0.98  conjectures                             5
% 4.07/0.98  EPR                                     5
% 4.07/0.98  Horn                                    16
% 4.07/0.98  unary                                   12
% 4.07/0.98  binary                                  9
% 4.07/0.98  lits                                    48
% 4.07/0.98  lits eq                                 12
% 4.07/0.98  fd_pure                                 0
% 4.07/0.98  fd_pseudo                               0
% 4.07/0.98  fd_cond                                 0
% 4.07/0.98  fd_pseudo_cond                          1
% 4.07/0.98  AC symbols                              0
% 4.07/0.98  
% 4.07/0.98  ------ Schedule dynamic 5 is on 
% 4.07/0.98  
% 4.07/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  ------ 
% 4.07/0.98  Current options:
% 4.07/0.98  ------ 
% 4.07/0.98  
% 4.07/0.98  ------ Input Options
% 4.07/0.98  
% 4.07/0.98  --out_options                           all
% 4.07/0.98  --tptp_safe_out                         true
% 4.07/0.98  --problem_path                          ""
% 4.07/0.98  --include_path                          ""
% 4.07/0.98  --clausifier                            res/vclausify_rel
% 4.07/0.98  --clausifier_options                    ""
% 4.07/0.98  --stdin                                 false
% 4.07/0.98  --stats_out                             all
% 4.07/0.98  
% 4.07/0.98  ------ General Options
% 4.07/0.98  
% 4.07/0.98  --fof                                   false
% 4.07/0.98  --time_out_real                         305.
% 4.07/0.98  --time_out_virtual                      -1.
% 4.07/0.98  --symbol_type_check                     false
% 4.07/0.98  --clausify_out                          false
% 4.07/0.98  --sig_cnt_out                           false
% 4.07/0.98  --trig_cnt_out                          false
% 4.07/0.98  --trig_cnt_out_tolerance                1.
% 4.07/0.98  --trig_cnt_out_sk_spl                   false
% 4.07/0.98  --abstr_cl_out                          false
% 4.07/0.98  
% 4.07/0.98  ------ Global Options
% 4.07/0.98  
% 4.07/0.98  --schedule                              default
% 4.07/0.98  --add_important_lit                     false
% 4.07/0.98  --prop_solver_per_cl                    1000
% 4.07/0.98  --min_unsat_core                        false
% 4.07/0.98  --soft_assumptions                      false
% 4.07/0.98  --soft_lemma_size                       3
% 4.07/0.98  --prop_impl_unit_size                   0
% 4.07/0.98  --prop_impl_unit                        []
% 4.07/0.98  --share_sel_clauses                     true
% 4.07/0.98  --reset_solvers                         false
% 4.07/0.98  --bc_imp_inh                            [conj_cone]
% 4.07/0.98  --conj_cone_tolerance                   3.
% 4.07/0.98  --extra_neg_conj                        none
% 4.07/0.98  --large_theory_mode                     true
% 4.07/0.98  --prolific_symb_bound                   200
% 4.07/0.98  --lt_threshold                          2000
% 4.07/0.98  --clause_weak_htbl                      true
% 4.07/0.98  --gc_record_bc_elim                     false
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing Options
% 4.07/0.98  
% 4.07/0.98  --preprocessing_flag                    true
% 4.07/0.98  --time_out_prep_mult                    0.1
% 4.07/0.98  --splitting_mode                        input
% 4.07/0.98  --splitting_grd                         true
% 4.07/0.98  --splitting_cvd                         false
% 4.07/0.98  --splitting_cvd_svl                     false
% 4.07/0.98  --splitting_nvd                         32
% 4.07/0.98  --sub_typing                            true
% 4.07/0.98  --prep_gs_sim                           true
% 4.07/0.98  --prep_unflatten                        true
% 4.07/0.98  --prep_res_sim                          true
% 4.07/0.98  --prep_upred                            true
% 4.07/0.98  --prep_sem_filter                       exhaustive
% 4.07/0.98  --prep_sem_filter_out                   false
% 4.07/0.98  --pred_elim                             true
% 4.07/0.98  --res_sim_input                         true
% 4.07/0.98  --eq_ax_congr_red                       true
% 4.07/0.98  --pure_diseq_elim                       true
% 4.07/0.98  --brand_transform                       false
% 4.07/0.98  --non_eq_to_eq                          false
% 4.07/0.98  --prep_def_merge                        true
% 4.07/0.98  --prep_def_merge_prop_impl              false
% 4.07/0.98  --prep_def_merge_mbd                    true
% 4.07/0.98  --prep_def_merge_tr_red                 false
% 4.07/0.98  --prep_def_merge_tr_cl                  false
% 4.07/0.98  --smt_preprocessing                     true
% 4.07/0.98  --smt_ac_axioms                         fast
% 4.07/0.98  --preprocessed_out                      false
% 4.07/0.98  --preprocessed_stats                    false
% 4.07/0.98  
% 4.07/0.98  ------ Abstraction refinement Options
% 4.07/0.98  
% 4.07/0.98  --abstr_ref                             []
% 4.07/0.98  --abstr_ref_prep                        false
% 4.07/0.98  --abstr_ref_until_sat                   false
% 4.07/0.98  --abstr_ref_sig_restrict                funpre
% 4.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.07/0.98  --abstr_ref_under                       []
% 4.07/0.98  
% 4.07/0.98  ------ SAT Options
% 4.07/0.98  
% 4.07/0.98  --sat_mode                              false
% 4.07/0.98  --sat_fm_restart_options                ""
% 4.07/0.98  --sat_gr_def                            false
% 4.07/0.98  --sat_epr_types                         true
% 4.07/0.98  --sat_non_cyclic_types                  false
% 4.07/0.98  --sat_finite_models                     false
% 4.07/0.98  --sat_fm_lemmas                         false
% 4.07/0.98  --sat_fm_prep                           false
% 4.07/0.98  --sat_fm_uc_incr                        true
% 4.07/0.98  --sat_out_model                         small
% 4.07/0.98  --sat_out_clauses                       false
% 4.07/0.98  
% 4.07/0.98  ------ QBF Options
% 4.07/0.98  
% 4.07/0.98  --qbf_mode                              false
% 4.07/0.98  --qbf_elim_univ                         false
% 4.07/0.98  --qbf_dom_inst                          none
% 4.07/0.98  --qbf_dom_pre_inst                      false
% 4.07/0.98  --qbf_sk_in                             false
% 4.07/0.98  --qbf_pred_elim                         true
% 4.07/0.98  --qbf_split                             512
% 4.07/0.98  
% 4.07/0.98  ------ BMC1 Options
% 4.07/0.98  
% 4.07/0.98  --bmc1_incremental                      false
% 4.07/0.98  --bmc1_axioms                           reachable_all
% 4.07/0.98  --bmc1_min_bound                        0
% 4.07/0.98  --bmc1_max_bound                        -1
% 4.07/0.98  --bmc1_max_bound_default                -1
% 4.07/0.98  --bmc1_symbol_reachability              true
% 4.07/0.98  --bmc1_property_lemmas                  false
% 4.07/0.98  --bmc1_k_induction                      false
% 4.07/0.98  --bmc1_non_equiv_states                 false
% 4.07/0.98  --bmc1_deadlock                         false
% 4.07/0.98  --bmc1_ucm                              false
% 4.07/0.98  --bmc1_add_unsat_core                   none
% 4.07/0.98  --bmc1_unsat_core_children              false
% 4.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.07/0.98  --bmc1_out_stat                         full
% 4.07/0.98  --bmc1_ground_init                      false
% 4.07/0.98  --bmc1_pre_inst_next_state              false
% 4.07/0.98  --bmc1_pre_inst_state                   false
% 4.07/0.98  --bmc1_pre_inst_reach_state             false
% 4.07/0.98  --bmc1_out_unsat_core                   false
% 4.07/0.98  --bmc1_aig_witness_out                  false
% 4.07/0.98  --bmc1_verbose                          false
% 4.07/0.98  --bmc1_dump_clauses_tptp                false
% 4.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.07/0.98  --bmc1_dump_file                        -
% 4.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.07/0.98  --bmc1_ucm_extend_mode                  1
% 4.07/0.98  --bmc1_ucm_init_mode                    2
% 4.07/0.98  --bmc1_ucm_cone_mode                    none
% 4.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.07/0.98  --bmc1_ucm_relax_model                  4
% 4.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.07/0.98  --bmc1_ucm_layered_model                none
% 4.07/0.98  --bmc1_ucm_max_lemma_size               10
% 4.07/0.98  
% 4.07/0.98  ------ AIG Options
% 4.07/0.98  
% 4.07/0.98  --aig_mode                              false
% 4.07/0.98  
% 4.07/0.98  ------ Instantiation Options
% 4.07/0.98  
% 4.07/0.98  --instantiation_flag                    true
% 4.07/0.98  --inst_sos_flag                         true
% 4.07/0.98  --inst_sos_phase                        true
% 4.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.07/0.98  --inst_lit_sel_side                     none
% 4.07/0.98  --inst_solver_per_active                1400
% 4.07/0.98  --inst_solver_calls_frac                1.
% 4.07/0.98  --inst_passive_queue_type               priority_queues
% 4.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.07/0.98  --inst_passive_queues_freq              [25;2]
% 4.07/0.98  --inst_dismatching                      true
% 4.07/0.98  --inst_eager_unprocessed_to_passive     true
% 4.07/0.98  --inst_prop_sim_given                   true
% 4.07/0.98  --inst_prop_sim_new                     false
% 4.07/0.98  --inst_subs_new                         false
% 4.07/0.98  --inst_eq_res_simp                      false
% 4.07/0.98  --inst_subs_given                       false
% 4.07/0.98  --inst_orphan_elimination               true
% 4.07/0.98  --inst_learning_loop_flag               true
% 4.07/0.98  --inst_learning_start                   3000
% 4.07/0.98  --inst_learning_factor                  2
% 4.07/0.98  --inst_start_prop_sim_after_learn       3
% 4.07/0.98  --inst_sel_renew                        solver
% 4.07/0.98  --inst_lit_activity_flag                true
% 4.07/0.98  --inst_restr_to_given                   false
% 4.07/0.98  --inst_activity_threshold               500
% 4.07/0.98  --inst_out_proof                        true
% 4.07/0.98  
% 4.07/0.98  ------ Resolution Options
% 4.07/0.98  
% 4.07/0.98  --resolution_flag                       false
% 4.07/0.98  --res_lit_sel                           adaptive
% 4.07/0.98  --res_lit_sel_side                      none
% 4.07/0.98  --res_ordering                          kbo
% 4.07/0.98  --res_to_prop_solver                    active
% 4.07/0.98  --res_prop_simpl_new                    false
% 4.07/0.98  --res_prop_simpl_given                  true
% 4.07/0.98  --res_passive_queue_type                priority_queues
% 4.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.07/0.98  --res_passive_queues_freq               [15;5]
% 4.07/0.98  --res_forward_subs                      full
% 4.07/0.98  --res_backward_subs                     full
% 4.07/0.98  --res_forward_subs_resolution           true
% 4.07/0.98  --res_backward_subs_resolution          true
% 4.07/0.98  --res_orphan_elimination                true
% 4.07/0.98  --res_time_limit                        2.
% 4.07/0.98  --res_out_proof                         true
% 4.07/0.98  
% 4.07/0.98  ------ Superposition Options
% 4.07/0.98  
% 4.07/0.98  --superposition_flag                    true
% 4.07/0.98  --sup_passive_queue_type                priority_queues
% 4.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.07/0.98  --demod_completeness_check              fast
% 4.07/0.98  --demod_use_ground                      true
% 4.07/0.98  --sup_to_prop_solver                    passive
% 4.07/0.98  --sup_prop_simpl_new                    true
% 4.07/0.98  --sup_prop_simpl_given                  true
% 4.07/0.98  --sup_fun_splitting                     true
% 4.07/0.98  --sup_smt_interval                      50000
% 4.07/0.98  
% 4.07/0.98  ------ Superposition Simplification Setup
% 4.07/0.98  
% 4.07/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.07/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.07/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.07/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.07/0.98  --sup_immed_triv                        [TrivRules]
% 4.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_immed_bw_main                     []
% 4.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_input_bw                          []
% 4.07/0.98  
% 4.07/0.98  ------ Combination Options
% 4.07/0.98  
% 4.07/0.98  --comb_res_mult                         3
% 4.07/0.98  --comb_sup_mult                         2
% 4.07/0.98  --comb_inst_mult                        10
% 4.07/0.98  
% 4.07/0.98  ------ Debug Options
% 4.07/0.98  
% 4.07/0.98  --dbg_backtrace                         false
% 4.07/0.98  --dbg_dump_prop_clauses                 false
% 4.07/0.98  --dbg_dump_prop_clauses_file            -
% 4.07/0.98  --dbg_out_stat                          false
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  ------ Proving...
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  % SZS status Theorem for theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  fof(f7,conjecture,(
% 4.07/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f8,negated_conjecture,(
% 4.07/0.98    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 4.07/0.98    inference(negated_conjecture,[],[f7])).
% 4.07/0.98  
% 4.07/0.98  fof(f14,plain,(
% 4.07/0.98    ? [X0] : ((~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 4.07/0.98    inference(ennf_transformation,[],[f8])).
% 4.07/0.98  
% 4.07/0.98  fof(f15,plain,(
% 4.07/0.98    ? [X0] : (~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 4.07/0.98    inference(flattening,[],[f14])).
% 4.07/0.98  
% 4.07/0.98  fof(f26,plain,(
% 4.07/0.98    ( ! [X0] : (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k5_relat_1(X0,sK5) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(sK5) & v1_relat_1(sK5))) )),
% 4.07/0.98    introduced(choice_axiom,[])).
% 4.07/0.98  
% 4.07/0.98  fof(f25,plain,(
% 4.07/0.98    ? [X0] : (~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v2_funct_1(sK4) & ? [X1] : (k5_relat_1(sK4,X1) = k6_relat_1(k1_relat_1(sK4)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 4.07/0.98    introduced(choice_axiom,[])).
% 4.07/0.98  
% 4.07/0.98  fof(f27,plain,(
% 4.07/0.98    ~v2_funct_1(sK4) & (k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4)) & v1_funct_1(sK5) & v1_relat_1(sK5)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 4.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f15,f26,f25])).
% 4.07/0.98  
% 4.07/0.98  fof(f48,plain,(
% 4.07/0.98    v1_relat_1(sK4)),
% 4.07/0.98    inference(cnf_transformation,[],[f27])).
% 4.07/0.98  
% 4.07/0.98  fof(f50,plain,(
% 4.07/0.98    v1_relat_1(sK5)),
% 4.07/0.98    inference(cnf_transformation,[],[f27])).
% 4.07/0.98  
% 4.07/0.98  fof(f16,plain,(
% 4.07/0.98    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.07/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.07/0.98  
% 4.07/0.98  fof(f20,plain,(
% 4.07/0.98    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))) & (! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~sP0(X0)))),
% 4.07/0.98    inference(nnf_transformation,[],[f16])).
% 4.07/0.98  
% 4.07/0.98  fof(f21,plain,(
% 4.07/0.98    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))) & (! [X3] : (! [X4] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~sP0(X0)))),
% 4.07/0.98    inference(rectify,[],[f20])).
% 4.07/0.98  
% 4.07/0.98  fof(f23,plain,(
% 4.07/0.98    ( ! [X1] : (! [X0] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) => (sK3(X0) != X1 & k5_relat_1(X1,X0) = k5_relat_1(sK3(X0),X0) & k1_relat_1(X1) = k1_relat_1(sK3(X0)) & r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))) )),
% 4.07/0.98    introduced(choice_axiom,[])).
% 4.07/0.98  
% 4.07/0.98  fof(f22,plain,(
% 4.07/0.98    ! [X0] : (? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (sK2(X0) != X2 & k5_relat_1(X2,X0) = k5_relat_1(sK2(X0),X0) & k1_relat_1(X2) = k1_relat_1(sK2(X0)) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0))))),
% 4.07/0.98    introduced(choice_axiom,[])).
% 4.07/0.98  
% 4.07/0.98  fof(f24,plain,(
% 4.07/0.98    ! [X0] : ((sP0(X0) | ((sK2(X0) != sK3(X0) & k5_relat_1(sK2(X0),X0) = k5_relat_1(sK3(X0),X0) & k1_relat_1(sK2(X0)) = k1_relat_1(sK3(X0)) & r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0)) & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))) & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0)))) & (! [X3] : (! [X4] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~sP0(X0)))),
% 4.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f23,f22])).
% 4.07/0.98  
% 4.07/0.98  fof(f39,plain,(
% 4.07/0.98    ( ! [X0] : (sP0(X0) | v1_relat_1(sK3(X0))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f24])).
% 4.07/0.98  
% 4.07/0.98  fof(f2,axiom,(
% 4.07/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f11,plain,(
% 4.07/0.98    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.07/0.98    inference(ennf_transformation,[],[f2])).
% 4.07/0.98  
% 4.07/0.98  fof(f29,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f11])).
% 4.07/0.98  
% 4.07/0.98  fof(f52,plain,(
% 4.07/0.98    k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4))),
% 4.07/0.98    inference(cnf_transformation,[],[f27])).
% 4.07/0.98  
% 4.07/0.98  fof(f17,plain,(
% 4.07/0.98    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 4.07/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 4.07/0.98  
% 4.07/0.98  fof(f19,plain,(
% 4.07/0.98    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 4.07/0.98    inference(nnf_transformation,[],[f17])).
% 4.07/0.98  
% 4.07/0.98  fof(f35,plain,(
% 4.07/0.98    ( ! [X0] : (v2_funct_1(X0) | ~sP0(X0) | ~sP1(X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f19])).
% 4.07/0.98  
% 4.07/0.98  fof(f53,plain,(
% 4.07/0.98    ~v2_funct_1(sK4)),
% 4.07/0.98    inference(cnf_transformation,[],[f27])).
% 4.07/0.98  
% 4.07/0.98  fof(f49,plain,(
% 4.07/0.98    v1_funct_1(sK4)),
% 4.07/0.98    inference(cnf_transformation,[],[f27])).
% 4.07/0.98  
% 4.07/0.98  fof(f5,axiom,(
% 4.07/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) => X1 = X2)))))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f12,plain,(
% 4.07/0.98    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : ((X1 = X2 | (k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.07/0.98    inference(ennf_transformation,[],[f5])).
% 4.07/0.98  
% 4.07/0.98  fof(f13,plain,(
% 4.07/0.98    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.07/0.98    inference(flattening,[],[f12])).
% 4.07/0.98  
% 4.07/0.98  fof(f18,plain,(
% 4.07/0.98    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.07/0.98    inference(definition_folding,[],[f13,f17,f16])).
% 4.07/0.98  
% 4.07/0.98  fof(f46,plain,(
% 4.07/0.98    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f18])).
% 4.07/0.98  
% 4.07/0.98  fof(f44,plain,(
% 4.07/0.98    ( ! [X0] : (sP0(X0) | k5_relat_1(sK2(X0),X0) = k5_relat_1(sK3(X0),X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f24])).
% 4.07/0.98  
% 4.07/0.98  fof(f37,plain,(
% 4.07/0.98    ( ! [X0] : (sP0(X0) | v1_relat_1(sK2(X0))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f24])).
% 4.07/0.98  
% 4.07/0.98  fof(f36,plain,(
% 4.07/0.98    ( ! [X4,X0,X3] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~sP0(X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f24])).
% 4.07/0.98  
% 4.07/0.98  fof(f43,plain,(
% 4.07/0.98    ( ! [X0] : (sP0(X0) | k1_relat_1(sK2(X0)) = k1_relat_1(sK3(X0))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f24])).
% 4.07/0.98  
% 4.07/0.98  fof(f3,axiom,(
% 4.07/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f30,plain,(
% 4.07/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 4.07/0.98    inference(cnf_transformation,[],[f3])).
% 4.07/0.98  
% 4.07/0.98  fof(f34,plain,(
% 4.07/0.98    ( ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~sP1(X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f19])).
% 4.07/0.98  
% 4.07/0.98  fof(f6,axiom,(
% 4.07/0.98    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f47,plain,(
% 4.07/0.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f6])).
% 4.07/0.98  
% 4.07/0.98  fof(f4,axiom,(
% 4.07/0.98    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f32,plain,(
% 4.07/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f4])).
% 4.07/0.98  
% 4.07/0.98  fof(f33,plain,(
% 4.07/0.98    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f4])).
% 4.07/0.98  
% 4.07/0.98  fof(f45,plain,(
% 4.07/0.98    ( ! [X0] : (sP0(X0) | sK2(X0) != sK3(X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f24])).
% 4.07/0.98  
% 4.07/0.98  fof(f42,plain,(
% 4.07/0.98    ( ! [X0] : (sP0(X0) | r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f24])).
% 4.07/0.98  
% 4.07/0.98  fof(f41,plain,(
% 4.07/0.98    ( ! [X0] : (sP0(X0) | r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f24])).
% 4.07/0.98  
% 4.07/0.98  fof(f40,plain,(
% 4.07/0.98    ( ! [X0] : (sP0(X0) | v1_funct_1(sK3(X0))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f24])).
% 4.07/0.99  
% 4.07/0.99  fof(f38,plain,(
% 4.07/0.99    ( ! [X0] : (sP0(X0) | v1_funct_1(sK2(X0))) )),
% 4.07/0.99    inference(cnf_transformation,[],[f24])).
% 4.07/0.99  
% 4.07/0.99  cnf(c_25,negated_conjecture,
% 4.07/0.99      ( v1_relat_1(sK4) ),
% 4.07/0.99      inference(cnf_transformation,[],[f48]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1838,plain,
% 4.07/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_23,negated_conjecture,
% 4.07/0.99      ( v1_relat_1(sK5) ),
% 4.07/0.99      inference(cnf_transformation,[],[f50]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1840,plain,
% 4.07/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_14,plain,
% 4.07/0.99      ( sP0(X0) | v1_relat_1(sK3(X0)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f39]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1845,plain,
% 4.07/0.99      ( sP0(X0) = iProver_top | v1_relat_1(sK3(X0)) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1,plain,
% 4.07/0.99      ( ~ v1_relat_1(X0)
% 4.07/0.99      | ~ v1_relat_1(X1)
% 4.07/0.99      | ~ v1_relat_1(X2)
% 4.07/0.99      | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f29]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1854,plain,
% 4.07/0.99      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 4.07/0.99      | v1_relat_1(X1) != iProver_top
% 4.07/0.99      | v1_relat_1(X2) != iProver_top
% 4.07/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2624,plain,
% 4.07/0.99      ( k5_relat_1(sK3(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(sK3(X0),X1),X2)
% 4.07/0.99      | sP0(X0) = iProver_top
% 4.07/0.99      | v1_relat_1(X2) != iProver_top
% 4.07/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1845,c_1854]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10023,plain,
% 4.07/0.99      ( k5_relat_1(k5_relat_1(sK3(X0),X1),sK5) = k5_relat_1(sK3(X0),k5_relat_1(X1,sK5))
% 4.07/0.99      | sP0(X0) = iProver_top
% 4.07/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1840,c_2624]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10477,plain,
% 4.07/0.99      ( k5_relat_1(k5_relat_1(sK3(X0),sK4),sK5) = k5_relat_1(sK3(X0),k5_relat_1(sK4,sK5))
% 4.07/0.99      | sP0(X0) = iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1838,c_10023]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_21,negated_conjecture,
% 4.07/0.99      ( k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f52]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10478,plain,
% 4.07/0.99      ( k5_relat_1(k5_relat_1(sK3(X0),sK4),sK5) = k5_relat_1(sK3(X0),k6_relat_1(k1_relat_1(sK4)))
% 4.07/0.99      | sP0(X0) = iProver_top ),
% 4.07/0.99      inference(light_normalisation,[status(thm)],[c_10477,c_21]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_6,plain,
% 4.07/0.99      ( ~ sP1(X0) | ~ sP0(X0) | v2_funct_1(X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f35]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_20,negated_conjecture,
% 4.07/0.99      ( ~ v2_funct_1(sK4) ),
% 4.07/0.99      inference(cnf_transformation,[],[f53]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_279,plain,
% 4.07/0.99      ( ~ sP1(X0) | ~ sP0(X0) | sK4 != X0 ),
% 4.07/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_20]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_280,plain,
% 4.07/0.99      ( ~ sP1(sK4) | ~ sP0(sK4) ),
% 4.07/0.99      inference(unflattening,[status(thm)],[c_279]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_24,negated_conjecture,
% 4.07/0.99      ( v1_funct_1(sK4) ),
% 4.07/0.99      inference(cnf_transformation,[],[f49]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_18,plain,
% 4.07/0.99      ( sP1(X0) | ~ v1_funct_1(X0) | ~ v1_relat_1(X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f46]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_35,plain,
% 4.07/0.99      ( sP1(sK4) | ~ v1_funct_1(sK4) | ~ v1_relat_1(sK4) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_69,plain,
% 4.07/0.99      ( ~ sP1(sK4) | ~ sP0(sK4) | v2_funct_1(sK4) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_282,plain,
% 4.07/0.99      ( ~ sP0(sK4) ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_280,c_25,c_24,c_20,c_35,c_69]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1837,plain,
% 4.07/0.99      ( sP0(sK4) != iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10640,plain,
% 4.07/0.99      ( k5_relat_1(k5_relat_1(sK3(sK4),sK4),sK5) = k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4))) ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_10478,c_1837]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_9,plain,
% 4.07/0.99      ( sP0(X0) | k5_relat_1(sK3(X0),X0) = k5_relat_1(sK2(X0),X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f44]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1850,plain,
% 4.07/0.99      ( k5_relat_1(sK3(X0),X0) = k5_relat_1(sK2(X0),X0)
% 4.07/0.99      | sP0(X0) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_3381,plain,
% 4.07/0.99      ( k5_relat_1(sK2(sK4),sK4) = k5_relat_1(sK3(sK4),sK4) ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1850,c_1837]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_16,plain,
% 4.07/0.99      ( sP0(X0) | v1_relat_1(sK2(X0)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f37]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1843,plain,
% 4.07/0.99      ( sP0(X0) = iProver_top | v1_relat_1(sK2(X0)) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2396,plain,
% 4.07/0.99      ( k5_relat_1(sK2(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(sK2(X0),X1),X2)
% 4.07/0.99      | sP0(X0) = iProver_top
% 4.07/0.99      | v1_relat_1(X2) != iProver_top
% 4.07/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1843,c_1854]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4892,plain,
% 4.07/0.99      ( k5_relat_1(k5_relat_1(sK2(X0),X1),sK5) = k5_relat_1(sK2(X0),k5_relat_1(X1,sK5))
% 4.07/0.99      | sP0(X0) = iProver_top
% 4.07/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1840,c_2396]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_6060,plain,
% 4.07/0.99      ( k5_relat_1(k5_relat_1(sK2(X0),sK4),sK5) = k5_relat_1(sK2(X0),k5_relat_1(sK4,sK5))
% 4.07/0.99      | sP0(X0) = iProver_top ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1838,c_4892]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_6061,plain,
% 4.07/0.99      ( k5_relat_1(k5_relat_1(sK2(X0),sK4),sK5) = k5_relat_1(sK2(X0),k6_relat_1(k1_relat_1(sK4)))
% 4.07/0.99      | sP0(X0) = iProver_top ),
% 4.07/0.99      inference(light_normalisation,[status(thm)],[c_6060,c_21]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_6078,plain,
% 4.07/0.99      ( k5_relat_1(k5_relat_1(sK2(sK4),sK4),sK5) = k5_relat_1(sK2(sK4),k6_relat_1(k1_relat_1(sK4))) ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_6061,c_1837]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10641,plain,
% 4.07/0.99      ( k5_relat_1(sK2(sK4),k6_relat_1(k1_relat_1(sK4))) = k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4))) ),
% 4.07/0.99      inference(light_normalisation,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_10640,c_3381,c_6078]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_17,plain,
% 4.07/0.99      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 4.07/0.99      | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
% 4.07/0.99      | ~ sP0(X1)
% 4.07/0.99      | ~ v1_funct_1(X0)
% 4.07/0.99      | ~ v1_funct_1(X2)
% 4.07/0.99      | ~ v1_relat_1(X0)
% 4.07/0.99      | ~ v1_relat_1(X2)
% 4.07/0.99      | X0 = X2
% 4.07/0.99      | k5_relat_1(X0,X1) != k5_relat_1(X2,X1)
% 4.07/0.99      | k1_relat_1(X0) != k1_relat_1(X2) ),
% 4.07/0.99      inference(cnf_transformation,[],[f36]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2116,plain,
% 4.07/0.99      ( ~ r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(X0))
% 4.07/0.99      | ~ r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(X0))
% 4.07/0.99      | ~ sP0(X0)
% 4.07/0.99      | ~ v1_funct_1(sK3(sK4))
% 4.07/0.99      | ~ v1_funct_1(sK2(sK4))
% 4.07/0.99      | ~ v1_relat_1(sK3(sK4))
% 4.07/0.99      | ~ v1_relat_1(sK2(sK4))
% 4.07/0.99      | k5_relat_1(sK2(sK4),X0) != k5_relat_1(sK3(sK4),X0)
% 4.07/0.99      | sK2(sK4) = sK3(sK4)
% 4.07/0.99      | k1_relat_1(sK2(sK4)) != k1_relat_1(sK3(sK4)) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4054,plain,
% 4.07/0.99      ( ~ r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(k6_relat_1(X0)))
% 4.07/0.99      | ~ r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(k6_relat_1(X0)))
% 4.07/0.99      | ~ sP0(k6_relat_1(X0))
% 4.07/0.99      | ~ v1_funct_1(sK3(sK4))
% 4.07/0.99      | ~ v1_funct_1(sK2(sK4))
% 4.07/0.99      | ~ v1_relat_1(sK3(sK4))
% 4.07/0.99      | ~ v1_relat_1(sK2(sK4))
% 4.07/0.99      | k5_relat_1(sK2(sK4),k6_relat_1(X0)) != k5_relat_1(sK3(sK4),k6_relat_1(X0))
% 4.07/0.99      | sK2(sK4) = sK3(sK4)
% 4.07/0.99      | k1_relat_1(sK2(sK4)) != k1_relat_1(sK3(sK4)) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_2116]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_6774,plain,
% 4.07/0.99      ( ~ r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(k6_relat_1(k1_relat_1(sK4))))
% 4.07/0.99      | ~ r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(k6_relat_1(k1_relat_1(sK4))))
% 4.07/0.99      | ~ sP0(k6_relat_1(k1_relat_1(sK4)))
% 4.07/0.99      | ~ v1_funct_1(sK3(sK4))
% 4.07/0.99      | ~ v1_funct_1(sK2(sK4))
% 4.07/0.99      | ~ v1_relat_1(sK3(sK4))
% 4.07/0.99      | ~ v1_relat_1(sK2(sK4))
% 4.07/0.99      | k5_relat_1(sK2(sK4),k6_relat_1(k1_relat_1(sK4))) != k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4)))
% 4.07/0.99      | sK2(sK4) = sK3(sK4)
% 4.07/0.99      | k1_relat_1(sK2(sK4)) != k1_relat_1(sK3(sK4)) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_4054]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1485,plain,( X0 = X0 ),theory(equality) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_5315,plain,
% 4.07/0.99      ( sK2(X0) = sK2(X0) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_1485]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_5316,plain,
% 4.07/0.99      ( sK2(sK4) = sK2(sK4) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_5315]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1490,plain,
% 4.07/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.07/0.99      theory(equality) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2055,plain,
% 4.07/0.99      ( ~ r1_tarski(X0,X1)
% 4.07/0.99      | r1_tarski(k2_relat_1(X2),k1_relat_1(k6_relat_1(X3)))
% 4.07/0.99      | k2_relat_1(X2) != X0
% 4.07/0.99      | k1_relat_1(k6_relat_1(X3)) != X1 ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_1490]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2217,plain,
% 4.07/0.99      ( r1_tarski(k2_relat_1(X0),k1_relat_1(k6_relat_1(X1)))
% 4.07/0.99      | ~ r1_tarski(k2_relat_1(sK2(X2)),k1_relat_1(X2))
% 4.07/0.99      | k2_relat_1(X0) != k2_relat_1(sK2(X2))
% 4.07/0.99      | k1_relat_1(k6_relat_1(X1)) != k1_relat_1(X2) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_2055]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2862,plain,
% 4.07/0.99      ( ~ r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))
% 4.07/0.99      | r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(k6_relat_1(X1)))
% 4.07/0.99      | k2_relat_1(sK2(X0)) != k2_relat_1(sK2(X0))
% 4.07/0.99      | k1_relat_1(k6_relat_1(X1)) != k1_relat_1(X0) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_2217]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4504,plain,
% 4.07/0.99      ( r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(k6_relat_1(k1_relat_1(sK4))))
% 4.07/0.99      | ~ r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(sK4))
% 4.07/0.99      | k2_relat_1(sK2(sK4)) != k2_relat_1(sK2(sK4))
% 4.07/0.99      | k1_relat_1(k6_relat_1(k1_relat_1(sK4))) != k1_relat_1(sK4) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_2862]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2214,plain,
% 4.07/0.99      ( r1_tarski(k2_relat_1(X0),k1_relat_1(k6_relat_1(X1)))
% 4.07/0.99      | ~ r1_tarski(k2_relat_1(sK3(X2)),k1_relat_1(X2))
% 4.07/0.99      | k2_relat_1(X0) != k2_relat_1(sK3(X2))
% 4.07/0.99      | k1_relat_1(k6_relat_1(X1)) != k1_relat_1(X2) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_2055]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2849,plain,
% 4.07/0.99      ( ~ r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))
% 4.07/0.99      | r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(k6_relat_1(X1)))
% 4.07/0.99      | k2_relat_1(sK3(X0)) != k2_relat_1(sK3(X0))
% 4.07/0.99      | k1_relat_1(k6_relat_1(X1)) != k1_relat_1(X0) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_2214]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4480,plain,
% 4.07/0.99      ( r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(k6_relat_1(k1_relat_1(sK4))))
% 4.07/0.99      | ~ r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(sK4))
% 4.07/0.99      | k2_relat_1(sK3(sK4)) != k2_relat_1(sK3(sK4))
% 4.07/0.99      | k1_relat_1(k6_relat_1(k1_relat_1(sK4))) != k1_relat_1(sK4) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_2849]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1489,plain,
% 4.07/0.99      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 4.07/0.99      theory(equality) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2868,plain,
% 4.07/0.99      ( X0 != sK2(X1) | k2_relat_1(X0) = k2_relat_1(sK2(X1)) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_1489]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4275,plain,
% 4.07/0.99      ( sK2(X0) != sK2(X0) | k2_relat_1(sK2(X0)) = k2_relat_1(sK2(X0)) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_2868]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4276,plain,
% 4.07/0.99      ( sK2(sK4) != sK2(sK4)
% 4.07/0.99      | k2_relat_1(sK2(sK4)) = k2_relat_1(sK2(sK4)) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_4275]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2719,plain,
% 4.07/0.99      ( k2_relat_1(sK3(sK4)) = k2_relat_1(sK3(sK4)) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_1485]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_10,plain,
% 4.07/0.99      ( sP0(X0) | k1_relat_1(sK3(X0)) = k1_relat_1(sK2(X0)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f43]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1849,plain,
% 4.07/0.99      ( k1_relat_1(sK3(X0)) = k1_relat_1(sK2(X0))
% 4.07/0.99      | sP0(X0) = iProver_top ),
% 4.07/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2680,plain,
% 4.07/0.99      ( k1_relat_1(sK2(sK4)) = k1_relat_1(sK3(sK4)) ),
% 4.07/0.99      inference(superposition,[status(thm)],[c_1849,c_1837]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_3,plain,
% 4.07/0.99      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 4.07/0.99      inference(cnf_transformation,[],[f30]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2537,plain,
% 4.07/0.99      ( k1_relat_1(k6_relat_1(k1_relat_1(sK4))) = k1_relat_1(sK4) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_7,plain,
% 4.07/0.99      ( ~ sP1(X0) | sP0(X0) | ~ v2_funct_1(X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f34]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_19,plain,
% 4.07/0.99      ( v2_funct_1(k6_relat_1(X0)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f47]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_267,plain,
% 4.07/0.99      ( ~ sP1(X0) | sP0(X0) | k6_relat_1(X1) != X0 ),
% 4.07/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_268,plain,
% 4.07/0.99      ( ~ sP1(k6_relat_1(X0)) | sP0(k6_relat_1(X0)) ),
% 4.07/0.99      inference(unflattening,[status(thm)],[c_267]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_301,plain,
% 4.07/0.99      ( sP0(k6_relat_1(X0))
% 4.07/0.99      | ~ v1_funct_1(X1)
% 4.07/0.99      | ~ v1_relat_1(X1)
% 4.07/0.99      | k6_relat_1(X0) != X1 ),
% 4.07/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_268]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_302,plain,
% 4.07/0.99      ( sP0(k6_relat_1(X0))
% 4.07/0.99      | ~ v1_funct_1(k6_relat_1(X0))
% 4.07/0.99      | ~ v1_relat_1(k6_relat_1(X0)) ),
% 4.07/0.99      inference(unflattening,[status(thm)],[c_301]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_5,plain,
% 4.07/0.99      ( v1_relat_1(k6_relat_1(X0)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f32]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_4,plain,
% 4.07/0.99      ( v1_funct_1(k6_relat_1(X0)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f33]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_306,plain,
% 4.07/0.99      ( sP0(k6_relat_1(X0)) ),
% 4.07/0.99      inference(global_propositional_subsumption,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_302,c_5,c_4]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_2109,plain,
% 4.07/0.99      ( sP0(k6_relat_1(k1_relat_1(sK4))) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_306]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1964,plain,
% 4.07/0.99      ( sK3(sK4) = sK3(sK4) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_1485]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1486,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1894,plain,
% 4.07/0.99      ( sK3(sK4) != X0 | sK3(sK4) = sK2(sK4) | sK2(sK4) != X0 ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_1486]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_1925,plain,
% 4.07/0.99      ( sK3(sK4) != sK3(sK4)
% 4.07/0.99      | sK3(sK4) = sK2(sK4)
% 4.07/0.99      | sK2(sK4) != sK3(sK4) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_1894]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_8,plain,
% 4.07/0.99      ( sP0(X0) | sK3(X0) != sK2(X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f45]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_65,plain,
% 4.07/0.99      ( sP0(sK4) | sK3(sK4) != sK2(sK4) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_11,plain,
% 4.07/0.99      ( r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) | sP0(X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f42]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_56,plain,
% 4.07/0.99      ( r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(sK4)) | sP0(sK4) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_12,plain,
% 4.07/0.99      ( r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0)) | sP0(X0) ),
% 4.07/0.99      inference(cnf_transformation,[],[f41]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_53,plain,
% 4.07/0.99      ( r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(sK4)) | sP0(sK4) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_13,plain,
% 4.07/0.99      ( sP0(X0) | v1_funct_1(sK3(X0)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f40]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_50,plain,
% 4.07/0.99      ( sP0(sK4) | v1_funct_1(sK3(sK4)) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_47,plain,
% 4.07/0.99      ( sP0(sK4) | v1_relat_1(sK3(sK4)) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_15,plain,
% 4.07/0.99      ( sP0(X0) | v1_funct_1(sK2(X0)) ),
% 4.07/0.99      inference(cnf_transformation,[],[f38]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_44,plain,
% 4.07/0.99      ( sP0(sK4) | v1_funct_1(sK2(sK4)) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(c_41,plain,
% 4.07/0.99      ( sP0(sK4) | v1_relat_1(sK2(sK4)) ),
% 4.07/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 4.07/0.99  
% 4.07/0.99  cnf(contradiction,plain,
% 4.07/0.99      ( $false ),
% 4.07/0.99      inference(minisat,
% 4.07/0.99                [status(thm)],
% 4.07/0.99                [c_10641,c_6774,c_5316,c_4504,c_4480,c_4276,c_2719,
% 4.07/0.99                 c_2680,c_2537,c_2109,c_1964,c_1925,c_69,c_65,c_56,c_53,
% 4.07/0.99                 c_50,c_47,c_44,c_41,c_35,c_20,c_24,c_25]) ).
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.07/0.99  
% 4.07/0.99  ------                               Statistics
% 4.07/0.99  
% 4.07/0.99  ------ General
% 4.07/0.99  
% 4.07/0.99  abstr_ref_over_cycles:                  0
% 4.07/0.99  abstr_ref_under_cycles:                 0
% 4.07/0.99  gc_basic_clause_elim:                   0
% 4.07/0.99  forced_gc_time:                         0
% 4.07/0.99  parsing_time:                           0.008
% 4.07/0.99  unif_index_cands_time:                  0.
% 4.07/0.99  unif_index_add_time:                    0.
% 4.07/0.99  orderings_time:                         0.
% 4.07/0.99  out_proof_time:                         0.01
% 4.07/0.99  total_time:                             0.398
% 4.07/0.99  num_of_symbols:                         45
% 4.07/0.99  num_of_terms:                           13840
% 4.07/0.99  
% 4.07/0.99  ------ Preprocessing
% 4.07/0.99  
% 4.07/0.99  num_of_splits:                          0
% 4.07/0.99  num_of_split_atoms:                     0
% 4.07/0.99  num_of_reused_defs:                     0
% 4.07/0.99  num_eq_ax_congr_red:                    8
% 4.07/0.99  num_of_sem_filtered_clauses:            1
% 4.07/0.99  num_of_subtypes:                        0
% 4.07/0.99  monotx_restored_types:                  0
% 4.07/0.99  sat_num_of_epr_types:                   0
% 4.07/0.99  sat_num_of_non_cyclic_types:            0
% 4.07/0.99  sat_guarded_non_collapsed_types:        0
% 4.07/0.99  num_pure_diseq_elim:                    0
% 4.07/0.99  simp_replaced_by:                       0
% 4.07/0.99  res_preprocessed:                       119
% 4.07/0.99  prep_upred:                             0
% 4.07/0.99  prep_unflattend:                        41
% 4.07/0.99  smt_new_axioms:                         0
% 4.07/0.99  pred_elim_cands:                        4
% 4.07/0.99  pred_elim:                              2
% 4.07/0.99  pred_elim_cl:                           2
% 4.07/0.99  pred_elim_cycles:                       4
% 4.07/0.99  merged_defs:                            0
% 4.07/0.99  merged_defs_ncl:                        0
% 4.07/0.99  bin_hyper_res:                          0
% 4.07/0.99  prep_cycles:                            4
% 4.07/0.99  pred_elim_time:                         0.018
% 4.07/0.99  splitting_time:                         0.
% 4.07/0.99  sem_filter_time:                        0.
% 4.07/0.99  monotx_time:                            0.
% 4.07/0.99  subtype_inf_time:                       0.
% 4.07/0.99  
% 4.07/0.99  ------ Problem properties
% 4.07/0.99  
% 4.07/0.99  clauses:                                24
% 4.07/0.99  conjectures:                            5
% 4.07/0.99  epr:                                    5
% 4.07/0.99  horn:                                   16
% 4.07/0.99  ground:                                 6
% 4.07/0.99  unary:                                  12
% 4.07/0.99  binary:                                 9
% 4.07/0.99  lits:                                   48
% 4.07/0.99  lits_eq:                                12
% 4.07/0.99  fd_pure:                                0
% 4.07/0.99  fd_pseudo:                              0
% 4.07/0.99  fd_cond:                                0
% 4.07/0.99  fd_pseudo_cond:                         1
% 4.07/0.99  ac_symbols:                             0
% 4.07/0.99  
% 4.07/0.99  ------ Propositional Solver
% 4.07/0.99  
% 4.07/0.99  prop_solver_calls:                      30
% 4.07/0.99  prop_fast_solver_calls:                 1341
% 4.07/0.99  smt_solver_calls:                       0
% 4.07/0.99  smt_fast_solver_calls:                  0
% 4.07/0.99  prop_num_of_clauses:                    3970
% 4.07/0.99  prop_preprocess_simplified:             10753
% 4.07/0.99  prop_fo_subsumed:                       15
% 4.07/0.99  prop_solver_time:                       0.
% 4.07/0.99  smt_solver_time:                        0.
% 4.07/0.99  smt_fast_solver_time:                   0.
% 4.07/0.99  prop_fast_solver_time:                  0.
% 4.07/0.99  prop_unsat_core_time:                   0.
% 4.07/0.99  
% 4.07/0.99  ------ QBF
% 4.07/0.99  
% 4.07/0.99  qbf_q_res:                              0
% 4.07/0.99  qbf_num_tautologies:                    0
% 4.07/0.99  qbf_prep_cycles:                        0
% 4.07/0.99  
% 4.07/0.99  ------ BMC1
% 4.07/0.99  
% 4.07/0.99  bmc1_current_bound:                     -1
% 4.07/0.99  bmc1_last_solved_bound:                 -1
% 4.07/0.99  bmc1_unsat_core_size:                   -1
% 4.07/0.99  bmc1_unsat_core_parents_size:           -1
% 4.07/0.99  bmc1_merge_next_fun:                    0
% 4.07/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.07/0.99  
% 4.07/0.99  ------ Instantiation
% 4.07/0.99  
% 4.07/0.99  inst_num_of_clauses:                    1497
% 4.07/0.99  inst_num_in_passive:                    548
% 4.07/0.99  inst_num_in_active:                     669
% 4.07/0.99  inst_num_in_unprocessed:                280
% 4.07/0.99  inst_num_of_loops:                      730
% 4.07/0.99  inst_num_of_learning_restarts:          0
% 4.07/0.99  inst_num_moves_active_passive:          57
% 4.07/0.99  inst_lit_activity:                      0
% 4.07/0.99  inst_lit_activity_moves:                0
% 4.07/0.99  inst_num_tautologies:                   0
% 4.07/0.99  inst_num_prop_implied:                  0
% 4.07/0.99  inst_num_existing_simplified:           0
% 4.07/0.99  inst_num_eq_res_simplified:             0
% 4.07/0.99  inst_num_child_elim:                    0
% 4.07/0.99  inst_num_of_dismatching_blockings:      1265
% 4.07/0.99  inst_num_of_non_proper_insts:           2231
% 4.07/0.99  inst_num_of_duplicates:                 0
% 4.07/0.99  inst_inst_num_from_inst_to_res:         0
% 4.07/0.99  inst_dismatching_checking_time:         0.
% 4.07/0.99  
% 4.07/0.99  ------ Resolution
% 4.07/0.99  
% 4.07/0.99  res_num_of_clauses:                     0
% 4.07/0.99  res_num_in_passive:                     0
% 4.07/0.99  res_num_in_active:                      0
% 4.07/0.99  res_num_of_loops:                       123
% 4.07/0.99  res_forward_subset_subsumed:            340
% 4.07/0.99  res_backward_subset_subsumed:           0
% 4.07/0.99  res_forward_subsumed:                   0
% 4.07/0.99  res_backward_subsumed:                  0
% 4.07/0.99  res_forward_subsumption_resolution:     0
% 4.07/0.99  res_backward_subsumption_resolution:    0
% 4.07/0.99  res_clause_to_clause_subsumption:       716
% 4.07/0.99  res_orphan_elimination:                 0
% 4.07/0.99  res_tautology_del:                      188
% 4.07/0.99  res_num_eq_res_simplified:              0
% 4.07/0.99  res_num_sel_changes:                    0
% 4.07/0.99  res_moves_from_active_to_pass:          0
% 4.07/0.99  
% 4.07/0.99  ------ Superposition
% 4.07/0.99  
% 4.07/0.99  sup_time_total:                         0.
% 4.07/0.99  sup_time_generating:                    0.
% 4.07/0.99  sup_time_sim_full:                      0.
% 4.07/0.99  sup_time_sim_immed:                     0.
% 4.07/0.99  
% 4.07/0.99  sup_num_of_clauses:                     305
% 4.07/0.99  sup_num_in_active:                      145
% 4.07/0.99  sup_num_in_passive:                     160
% 4.07/0.99  sup_num_of_loops:                       144
% 4.07/0.99  sup_fw_superposition:                   168
% 4.07/0.99  sup_bw_superposition:                   204
% 4.07/0.99  sup_immediate_simplified:               56
% 4.07/0.99  sup_given_eliminated:                   0
% 4.07/0.99  comparisons_done:                       0
% 4.07/0.99  comparisons_avoided:                    0
% 4.07/0.99  
% 4.07/0.99  ------ Simplifications
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  sim_fw_subset_subsumed:                 16
% 4.07/0.99  sim_bw_subset_subsumed:                 0
% 4.07/0.99  sim_fw_subsumed:                        1
% 4.07/0.99  sim_bw_subsumed:                        0
% 4.07/0.99  sim_fw_subsumption_res:                 0
% 4.07/0.99  sim_bw_subsumption_res:                 0
% 4.07/0.99  sim_tautology_del:                      0
% 4.07/0.99  sim_eq_tautology_del:                   13
% 4.07/0.99  sim_eq_res_simp:                        1
% 4.07/0.99  sim_fw_demodulated:                     24
% 4.07/0.99  sim_bw_demodulated:                     0
% 4.07/0.99  sim_light_normalised:                   25
% 4.07/0.99  sim_joinable_taut:                      0
% 4.07/0.99  sim_joinable_simp:                      0
% 4.07/0.99  sim_ac_normalised:                      0
% 4.07/0.99  sim_smt_subsumption:                    0
% 4.07/0.99  
%------------------------------------------------------------------------------
