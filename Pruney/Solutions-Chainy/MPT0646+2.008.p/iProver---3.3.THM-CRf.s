%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:20 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 565 expanded)
%              Number of clauses        :   74 ( 166 expanded)
%              Number of leaves         :   10 ( 152 expanded)
%              Depth                    :   15
%              Number of atoms          :  396 (3321 expanded)
%              Number of equality atoms :  153 ( 808 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ? [X1] :
              ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & v1_funct_1(X1)
              & v1_relat_1(X1) )
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k5_relat_1(X0,sK5) = k6_relat_1(k1_relat_1(X0))
        & v1_funct_1(sK5)
        & v1_relat_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
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

fof(f24,plain,
    ( ~ v2_funct_1(sK4)
    & k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4))
    & v1_funct_1(sK5)
    & v1_relat_1(sK5)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f12,f23,f22])).

fof(f42,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,plain,(
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

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f20,plain,(
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

fof(f19,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f20,f19])).

fof(f32,plain,(
    ! [X0] :
      ( sP0(X0)
      | v1_relat_1(sK3(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f44,plain,(
    k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ sP0(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
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

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f15,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f10,f14,f13])).

fof(f39,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( sP0(X0)
      | k5_relat_1(sK2(X0),X0) = k5_relat_1(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0] :
      ( sP0(X0)
      | r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0] :
      ( sP0(X0)
      | r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X0] :
      ( sP0(X0)
      | v1_relat_1(sK2(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0] :
      ( sP0(X0)
      | sK2(X0) != sK3(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1310,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1682,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1310])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1308,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1684,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1308])).

cnf(c_10,plain,
    ( sP0(X0)
    | v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1316,plain,
    ( sP0(X0_42)
    | v1_relat_1(sK3(X0_42)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1677,plain,
    ( sP0(X0_42) = iProver_top
    | v1_relat_1(sK3(X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1316])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1324,plain,
    ( ~ v1_relat_1(X0_42)
    | ~ v1_relat_1(X1_42)
    | ~ v1_relat_1(X2_42)
    | k5_relat_1(k5_relat_1(X2_42,X1_42),X0_42) = k5_relat_1(X2_42,k5_relat_1(X1_42,X0_42)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1669,plain,
    ( k5_relat_1(k5_relat_1(X0_42,X1_42),X2_42) = k5_relat_1(X0_42,k5_relat_1(X1_42,X2_42))
    | v1_relat_1(X2_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1324])).

cnf(c_2074,plain,
    ( k5_relat_1(sK3(X0_42),k5_relat_1(X1_42,X2_42)) = k5_relat_1(k5_relat_1(sK3(X0_42),X1_42),X2_42)
    | sP0(X0_42) = iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_relat_1(X2_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_1677,c_1669])).

cnf(c_4267,plain,
    ( k5_relat_1(k5_relat_1(sK3(X0_42),sK4),X1_42) = k5_relat_1(sK3(X0_42),k5_relat_1(sK4,X1_42))
    | sP0(X0_42) = iProver_top
    | v1_relat_1(X1_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_1684,c_2074])).

cnf(c_4868,plain,
    ( k5_relat_1(sK3(X0_42),k5_relat_1(sK4,sK5)) = k5_relat_1(k5_relat_1(sK3(X0_42),sK4),sK5)
    | sP0(X0_42) = iProver_top ),
    inference(superposition,[status(thm)],[c_1682,c_4267])).

cnf(c_16,negated_conjecture,
    ( k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1312,negated_conjecture,
    ( k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_4890,plain,
    ( k5_relat_1(sK3(X0_42),k6_relat_1(k1_relat_1(sK4))) = k5_relat_1(k5_relat_1(sK3(X0_42),sK4),sK5)
    | sP0(X0_42) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4868,c_1312])).

cnf(c_2,plain,
    ( ~ sP1(X0)
    | ~ sP0(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_15,negated_conjecture,
    ( ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_230,plain,
    ( ~ sP1(X0)
    | ~ sP0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_15])).

cnf(c_231,plain,
    ( ~ sP1(sK4)
    | ~ sP0(sK4) ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | sP1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_27,plain,
    ( ~ v1_funct_1(sK4)
    | sP1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_61,plain,
    ( ~ sP1(sK4)
    | ~ sP0(sK4)
    | v2_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_233,plain,
    ( ~ sP0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_231,c_20,c_19,c_15,c_27,c_61])).

cnf(c_1307,plain,
    ( ~ sP0(sK4) ),
    inference(subtyping,[status(esa)],[c_233])).

cnf(c_1685,plain,
    ( sP0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1307])).

cnf(c_5014,plain,
    ( k5_relat_1(k5_relat_1(sK3(sK4),sK4),sK5) = k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4))) ),
    inference(superposition,[status(thm)],[c_4890,c_1685])).

cnf(c_5,plain,
    ( sP0(X0)
    | k5_relat_1(sK3(X0),X0) = k5_relat_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1321,plain,
    ( sP0(X0_42)
    | k5_relat_1(sK3(X0_42),X0_42) = k5_relat_1(sK2(X0_42),X0_42) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1672,plain,
    ( k5_relat_1(sK3(X0_42),X0_42) = k5_relat_1(sK2(X0_42),X0_42)
    | sP0(X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1321])).

cnf(c_2466,plain,
    ( k5_relat_1(sK2(sK4),sK4) = k5_relat_1(sK3(sK4),sK4) ),
    inference(superposition,[status(thm)],[c_1672,c_1685])).

cnf(c_5015,plain,
    ( k5_relat_1(k5_relat_1(sK2(sK4),sK4),sK5) = k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4))) ),
    inference(light_normalisation,[status(thm)],[c_5014,c_2466])).

cnf(c_7,plain,
    ( r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1319,plain,
    ( r1_tarski(k2_relat_1(sK3(X0_42)),k1_relat_1(X0_42))
    | sP0(X0_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1674,plain,
    ( r1_tarski(k2_relat_1(sK3(X0_42)),k1_relat_1(X0_42)) = iProver_top
    | sP0(X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_1,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1323,plain,
    ( ~ r1_tarski(k2_relat_1(X0_42),X0_43)
    | ~ v1_relat_1(X0_42)
    | k5_relat_1(X0_42,k6_relat_1(X0_43)) = X0_42 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1670,plain,
    ( k5_relat_1(X0_42,k6_relat_1(X0_43)) = X0_42
    | r1_tarski(k2_relat_1(X0_42),X0_43) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1323])).

cnf(c_2523,plain,
    ( k5_relat_1(sK3(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK3(X0_42)
    | sP0(X0_42) = iProver_top
    | v1_relat_1(sK3(X0_42)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1674,c_1670])).

cnf(c_1366,plain,
    ( r1_tarski(k2_relat_1(sK3(X0_42)),k1_relat_1(X0_42)) = iProver_top
    | sP0(X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_1369,plain,
    ( sP0(X0_42) = iProver_top
    | v1_relat_1(sK3(X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1316])).

cnf(c_1818,plain,
    ( ~ r1_tarski(k2_relat_1(sK3(X0_42)),k1_relat_1(X0_42))
    | ~ v1_relat_1(sK3(X0_42))
    | k5_relat_1(sK3(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK3(X0_42) ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(c_1819,plain,
    ( k5_relat_1(sK3(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK3(X0_42)
    | r1_tarski(k2_relat_1(sK3(X0_42)),k1_relat_1(X0_42)) != iProver_top
    | v1_relat_1(sK3(X0_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1818])).

cnf(c_5474,plain,
    ( sP0(X0_42) = iProver_top
    | k5_relat_1(sK3(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK3(X0_42) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2523,c_1366,c_1369,c_1819])).

cnf(c_5475,plain,
    ( k5_relat_1(sK3(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK3(X0_42)
    | sP0(X0_42) = iProver_top ),
    inference(renaming,[status(thm)],[c_5474])).

cnf(c_5482,plain,
    ( k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4))) = sK3(sK4) ),
    inference(superposition,[status(thm)],[c_5475,c_1685])).

cnf(c_8,plain,
    ( r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1318,plain,
    ( r1_tarski(k2_relat_1(sK2(X0_42)),k1_relat_1(X0_42))
    | sP0(X0_42) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1675,plain,
    ( r1_tarski(k2_relat_1(sK2(X0_42)),k1_relat_1(X0_42)) = iProver_top
    | sP0(X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1318])).

cnf(c_2618,plain,
    ( k5_relat_1(sK2(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK2(X0_42)
    | sP0(X0_42) = iProver_top
    | v1_relat_1(sK2(X0_42)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1675,c_1670])).

cnf(c_1367,plain,
    ( r1_tarski(k2_relat_1(sK2(X0_42)),k1_relat_1(X0_42)) = iProver_top
    | sP0(X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1318])).

cnf(c_12,plain,
    ( sP0(X0)
    | v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1314,plain,
    ( sP0(X0_42)
    | v1_relat_1(sK2(X0_42)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1371,plain,
    ( sP0(X0_42) = iProver_top
    | v1_relat_1(sK2(X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1314])).

cnf(c_1813,plain,
    ( ~ r1_tarski(k2_relat_1(sK2(X0_42)),k1_relat_1(X0_42))
    | ~ v1_relat_1(sK2(X0_42))
    | k5_relat_1(sK2(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK2(X0_42) ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(c_1814,plain,
    ( k5_relat_1(sK2(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK2(X0_42)
    | r1_tarski(k2_relat_1(sK2(X0_42)),k1_relat_1(X0_42)) != iProver_top
    | v1_relat_1(sK2(X0_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1813])).

cnf(c_5600,plain,
    ( sP0(X0_42) = iProver_top
    | k5_relat_1(sK2(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK2(X0_42) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2618,c_1367,c_1371,c_1814])).

cnf(c_5601,plain,
    ( k5_relat_1(sK2(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK2(X0_42)
    | sP0(X0_42) = iProver_top ),
    inference(renaming,[status(thm)],[c_5600])).

cnf(c_5608,plain,
    ( k5_relat_1(sK2(sK4),k6_relat_1(k1_relat_1(sK4))) = sK2(sK4) ),
    inference(superposition,[status(thm)],[c_5601,c_1685])).

cnf(c_1679,plain,
    ( sP0(X0_42) = iProver_top
    | v1_relat_1(sK2(X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1314])).

cnf(c_2117,plain,
    ( k5_relat_1(sK2(X0_42),k5_relat_1(X1_42,X2_42)) = k5_relat_1(k5_relat_1(sK2(X0_42),X1_42),X2_42)
    | sP0(X0_42) = iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_relat_1(X2_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_1679,c_1669])).

cnf(c_5250,plain,
    ( k5_relat_1(k5_relat_1(sK2(X0_42),sK4),X1_42) = k5_relat_1(sK2(X0_42),k5_relat_1(sK4,X1_42))
    | sP0(X0_42) = iProver_top
    | v1_relat_1(X1_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_1684,c_2117])).

cnf(c_5868,plain,
    ( k5_relat_1(sK2(X0_42),k5_relat_1(sK4,sK5)) = k5_relat_1(k5_relat_1(sK2(X0_42),sK4),sK5)
    | sP0(X0_42) = iProver_top ),
    inference(superposition,[status(thm)],[c_1682,c_5250])).

cnf(c_5890,plain,
    ( k5_relat_1(sK2(X0_42),k6_relat_1(k1_relat_1(sK4))) = k5_relat_1(k5_relat_1(sK2(X0_42),sK4),sK5)
    | sP0(X0_42) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5868,c_1312])).

cnf(c_5908,plain,
    ( k5_relat_1(k5_relat_1(sK2(sK4),sK4),sK5) = k5_relat_1(sK2(sK4),k6_relat_1(k1_relat_1(sK4))) ),
    inference(superposition,[status(thm)],[c_5890,c_1685])).

cnf(c_6987,plain,
    ( k5_relat_1(k5_relat_1(sK2(sK4),sK4),sK5) = sK2(sK4) ),
    inference(demodulation,[status(thm)],[c_5608,c_5908])).

cnf(c_8504,plain,
    ( sK3(sK4) = sK2(sK4) ),
    inference(light_normalisation,[status(thm)],[c_5015,c_5482,c_6987])).

cnf(c_4,plain,
    ( sP0(X0)
    | sK3(X0) != sK2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1322,plain,
    ( sP0(X0_42)
    | sK3(X0_42) != sK2(X0_42) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1358,plain,
    ( sP0(sK4)
    | sK3(sK4) != sK2(sK4) ),
    inference(instantiation,[status(thm)],[c_1322])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8504,c_1358,c_61,c_27,c_15,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:02:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.39/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/0.98  
% 3.39/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.39/0.98  
% 3.39/0.98  ------  iProver source info
% 3.39/0.98  
% 3.39/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.39/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.39/0.98  git: non_committed_changes: false
% 3.39/0.98  git: last_make_outside_of_git: false
% 3.39/0.98  
% 3.39/0.98  ------ 
% 3.39/0.98  
% 3.39/0.98  ------ Input Options
% 3.39/0.98  
% 3.39/0.98  --out_options                           all
% 3.39/0.98  --tptp_safe_out                         true
% 3.39/0.98  --problem_path                          ""
% 3.39/0.98  --include_path                          ""
% 3.39/0.98  --clausifier                            res/vclausify_rel
% 3.39/0.98  --clausifier_options                    --mode clausify
% 3.39/0.98  --stdin                                 false
% 3.39/0.98  --stats_out                             all
% 3.39/0.98  
% 3.39/0.98  ------ General Options
% 3.39/0.98  
% 3.39/0.98  --fof                                   false
% 3.39/0.98  --time_out_real                         305.
% 3.39/0.98  --time_out_virtual                      -1.
% 3.39/0.98  --symbol_type_check                     false
% 3.39/0.98  --clausify_out                          false
% 3.39/0.98  --sig_cnt_out                           false
% 3.39/0.98  --trig_cnt_out                          false
% 3.39/0.98  --trig_cnt_out_tolerance                1.
% 3.39/0.98  --trig_cnt_out_sk_spl                   false
% 3.39/0.98  --abstr_cl_out                          false
% 3.39/0.98  
% 3.39/0.98  ------ Global Options
% 3.39/0.98  
% 3.39/0.98  --schedule                              default
% 3.39/0.98  --add_important_lit                     false
% 3.39/0.98  --prop_solver_per_cl                    1000
% 3.39/0.98  --min_unsat_core                        false
% 3.39/0.98  --soft_assumptions                      false
% 3.39/0.98  --soft_lemma_size                       3
% 3.39/0.98  --prop_impl_unit_size                   0
% 3.39/0.98  --prop_impl_unit                        []
% 3.39/0.98  --share_sel_clauses                     true
% 3.39/0.98  --reset_solvers                         false
% 3.39/0.98  --bc_imp_inh                            [conj_cone]
% 3.39/0.98  --conj_cone_tolerance                   3.
% 3.39/0.98  --extra_neg_conj                        none
% 3.39/0.98  --large_theory_mode                     true
% 3.39/0.98  --prolific_symb_bound                   200
% 3.39/0.98  --lt_threshold                          2000
% 3.39/0.98  --clause_weak_htbl                      true
% 3.39/0.98  --gc_record_bc_elim                     false
% 3.39/0.98  
% 3.39/0.98  ------ Preprocessing Options
% 3.39/0.98  
% 3.39/0.98  --preprocessing_flag                    true
% 3.39/0.98  --time_out_prep_mult                    0.1
% 3.39/0.98  --splitting_mode                        input
% 3.39/0.98  --splitting_grd                         true
% 3.39/0.98  --splitting_cvd                         false
% 3.39/0.98  --splitting_cvd_svl                     false
% 3.39/0.98  --splitting_nvd                         32
% 3.39/0.98  --sub_typing                            true
% 3.39/0.98  --prep_gs_sim                           true
% 3.39/0.98  --prep_unflatten                        true
% 3.39/0.98  --prep_res_sim                          true
% 3.39/0.98  --prep_upred                            true
% 3.39/0.98  --prep_sem_filter                       exhaustive
% 3.39/0.98  --prep_sem_filter_out                   false
% 3.39/0.98  --pred_elim                             true
% 3.39/0.98  --res_sim_input                         true
% 3.39/0.98  --eq_ax_congr_red                       true
% 3.39/0.98  --pure_diseq_elim                       true
% 3.39/0.98  --brand_transform                       false
% 3.39/0.98  --non_eq_to_eq                          false
% 3.39/0.98  --prep_def_merge                        true
% 3.39/0.98  --prep_def_merge_prop_impl              false
% 3.39/0.98  --prep_def_merge_mbd                    true
% 3.39/0.98  --prep_def_merge_tr_red                 false
% 3.39/0.98  --prep_def_merge_tr_cl                  false
% 3.39/0.98  --smt_preprocessing                     true
% 3.39/0.98  --smt_ac_axioms                         fast
% 3.39/0.98  --preprocessed_out                      false
% 3.39/0.98  --preprocessed_stats                    false
% 3.39/0.98  
% 3.39/0.98  ------ Abstraction refinement Options
% 3.39/0.98  
% 3.39/0.98  --abstr_ref                             []
% 3.39/0.98  --abstr_ref_prep                        false
% 3.39/0.98  --abstr_ref_until_sat                   false
% 3.39/0.98  --abstr_ref_sig_restrict                funpre
% 3.39/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/0.98  --abstr_ref_under                       []
% 3.39/0.98  
% 3.39/0.98  ------ SAT Options
% 3.39/0.98  
% 3.39/0.98  --sat_mode                              false
% 3.39/0.98  --sat_fm_restart_options                ""
% 3.39/0.98  --sat_gr_def                            false
% 3.39/0.98  --sat_epr_types                         true
% 3.39/0.98  --sat_non_cyclic_types                  false
% 3.39/0.98  --sat_finite_models                     false
% 3.39/0.98  --sat_fm_lemmas                         false
% 3.39/0.98  --sat_fm_prep                           false
% 3.39/0.98  --sat_fm_uc_incr                        true
% 3.39/0.98  --sat_out_model                         small
% 3.39/0.98  --sat_out_clauses                       false
% 3.39/0.98  
% 3.39/0.98  ------ QBF Options
% 3.39/0.98  
% 3.39/0.98  --qbf_mode                              false
% 3.39/0.98  --qbf_elim_univ                         false
% 3.39/0.98  --qbf_dom_inst                          none
% 3.39/0.98  --qbf_dom_pre_inst                      false
% 3.39/0.98  --qbf_sk_in                             false
% 3.39/0.98  --qbf_pred_elim                         true
% 3.39/0.98  --qbf_split                             512
% 3.39/0.98  
% 3.39/0.98  ------ BMC1 Options
% 3.39/0.98  
% 3.39/0.98  --bmc1_incremental                      false
% 3.39/0.98  --bmc1_axioms                           reachable_all
% 3.39/0.98  --bmc1_min_bound                        0
% 3.39/0.98  --bmc1_max_bound                        -1
% 3.39/0.98  --bmc1_max_bound_default                -1
% 3.39/0.98  --bmc1_symbol_reachability              true
% 3.39/0.98  --bmc1_property_lemmas                  false
% 3.39/0.98  --bmc1_k_induction                      false
% 3.39/0.98  --bmc1_non_equiv_states                 false
% 3.39/0.98  --bmc1_deadlock                         false
% 3.39/0.98  --bmc1_ucm                              false
% 3.39/0.98  --bmc1_add_unsat_core                   none
% 3.39/0.98  --bmc1_unsat_core_children              false
% 3.39/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/0.98  --bmc1_out_stat                         full
% 3.39/0.98  --bmc1_ground_init                      false
% 3.39/0.98  --bmc1_pre_inst_next_state              false
% 3.39/0.98  --bmc1_pre_inst_state                   false
% 3.39/0.98  --bmc1_pre_inst_reach_state             false
% 3.39/0.98  --bmc1_out_unsat_core                   false
% 3.39/0.98  --bmc1_aig_witness_out                  false
% 3.39/0.98  --bmc1_verbose                          false
% 3.39/0.98  --bmc1_dump_clauses_tptp                false
% 3.39/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.39/0.98  --bmc1_dump_file                        -
% 3.39/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.39/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.39/0.98  --bmc1_ucm_extend_mode                  1
% 3.39/0.98  --bmc1_ucm_init_mode                    2
% 3.39/0.98  --bmc1_ucm_cone_mode                    none
% 3.39/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.39/0.98  --bmc1_ucm_relax_model                  4
% 3.39/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.39/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/0.98  --bmc1_ucm_layered_model                none
% 3.39/0.98  --bmc1_ucm_max_lemma_size               10
% 3.39/0.98  
% 3.39/0.98  ------ AIG Options
% 3.39/0.98  
% 3.39/0.98  --aig_mode                              false
% 3.39/0.98  
% 3.39/0.98  ------ Instantiation Options
% 3.39/0.98  
% 3.39/0.98  --instantiation_flag                    true
% 3.39/0.98  --inst_sos_flag                         false
% 3.39/0.98  --inst_sos_phase                        true
% 3.39/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/0.98  --inst_lit_sel_side                     num_symb
% 3.39/0.98  --inst_solver_per_active                1400
% 3.39/0.98  --inst_solver_calls_frac                1.
% 3.39/0.98  --inst_passive_queue_type               priority_queues
% 3.39/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/0.98  --inst_passive_queues_freq              [25;2]
% 3.39/0.98  --inst_dismatching                      true
% 3.39/0.98  --inst_eager_unprocessed_to_passive     true
% 3.39/0.98  --inst_prop_sim_given                   true
% 3.39/0.98  --inst_prop_sim_new                     false
% 3.39/0.98  --inst_subs_new                         false
% 3.39/0.98  --inst_eq_res_simp                      false
% 3.39/0.98  --inst_subs_given                       false
% 3.39/0.98  --inst_orphan_elimination               true
% 3.39/0.98  --inst_learning_loop_flag               true
% 3.39/0.98  --inst_learning_start                   3000
% 3.39/0.98  --inst_learning_factor                  2
% 3.39/0.98  --inst_start_prop_sim_after_learn       3
% 3.39/0.98  --inst_sel_renew                        solver
% 3.39/0.98  --inst_lit_activity_flag                true
% 3.39/0.98  --inst_restr_to_given                   false
% 3.39/0.98  --inst_activity_threshold               500
% 3.39/0.98  --inst_out_proof                        true
% 3.39/0.98  
% 3.39/0.98  ------ Resolution Options
% 3.39/0.98  
% 3.39/0.98  --resolution_flag                       true
% 3.39/0.98  --res_lit_sel                           adaptive
% 3.39/0.98  --res_lit_sel_side                      none
% 3.39/0.98  --res_ordering                          kbo
% 3.39/0.98  --res_to_prop_solver                    active
% 3.39/0.98  --res_prop_simpl_new                    false
% 3.39/0.98  --res_prop_simpl_given                  true
% 3.39/0.98  --res_passive_queue_type                priority_queues
% 3.39/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/0.98  --res_passive_queues_freq               [15;5]
% 3.39/0.98  --res_forward_subs                      full
% 3.39/0.98  --res_backward_subs                     full
% 3.39/0.98  --res_forward_subs_resolution           true
% 3.39/0.98  --res_backward_subs_resolution          true
% 3.39/0.98  --res_orphan_elimination                true
% 3.39/0.98  --res_time_limit                        2.
% 3.39/0.98  --res_out_proof                         true
% 3.39/0.98  
% 3.39/0.98  ------ Superposition Options
% 3.39/0.98  
% 3.39/0.98  --superposition_flag                    true
% 3.39/0.98  --sup_passive_queue_type                priority_queues
% 3.39/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.39/0.98  --demod_completeness_check              fast
% 3.39/0.98  --demod_use_ground                      true
% 3.39/0.98  --sup_to_prop_solver                    passive
% 3.39/0.98  --sup_prop_simpl_new                    true
% 3.39/0.98  --sup_prop_simpl_given                  true
% 3.39/0.98  --sup_fun_splitting                     false
% 3.39/0.98  --sup_smt_interval                      50000
% 3.39/0.98  
% 3.39/0.98  ------ Superposition Simplification Setup
% 3.39/0.98  
% 3.39/0.98  --sup_indices_passive                   []
% 3.39/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.98  --sup_full_bw                           [BwDemod]
% 3.39/0.98  --sup_immed_triv                        [TrivRules]
% 3.39/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.98  --sup_immed_bw_main                     []
% 3.39/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.98  
% 3.39/0.98  ------ Combination Options
% 3.39/0.98  
% 3.39/0.98  --comb_res_mult                         3
% 3.39/0.98  --comb_sup_mult                         2
% 3.39/0.98  --comb_inst_mult                        10
% 3.39/0.98  
% 3.39/0.98  ------ Debug Options
% 3.39/0.98  
% 3.39/0.98  --dbg_backtrace                         false
% 3.39/0.98  --dbg_dump_prop_clauses                 false
% 3.39/0.98  --dbg_dump_prop_clauses_file            -
% 3.39/0.98  --dbg_out_stat                          false
% 3.39/0.98  ------ Parsing...
% 3.39/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.39/0.98  
% 3.39/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.39/0.98  
% 3.39/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.39/0.98  
% 3.39/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/0.98  ------ Proving...
% 3.39/0.98  ------ Problem Properties 
% 3.39/0.98  
% 3.39/0.98  
% 3.39/0.98  clauses                                 18
% 3.39/0.98  conjectures                             5
% 3.39/0.98  EPR                                     5
% 3.39/0.98  Horn                                    10
% 3.39/0.98  unary                                   6
% 3.39/0.98  binary                                  9
% 3.39/0.98  lits                                    41
% 3.39/0.98  lits eq                                 9
% 3.39/0.98  fd_pure                                 0
% 3.39/0.98  fd_pseudo                               0
% 3.39/0.98  fd_cond                                 0
% 3.39/0.98  fd_pseudo_cond                          1
% 3.39/0.98  AC symbols                              0
% 3.39/0.98  
% 3.39/0.98  ------ Schedule dynamic 5 is on 
% 3.39/0.98  
% 3.39/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.39/0.98  
% 3.39/0.98  
% 3.39/0.98  ------ 
% 3.39/0.98  Current options:
% 3.39/0.98  ------ 
% 3.39/0.98  
% 3.39/0.98  ------ Input Options
% 3.39/0.98  
% 3.39/0.98  --out_options                           all
% 3.39/0.98  --tptp_safe_out                         true
% 3.39/0.98  --problem_path                          ""
% 3.39/0.98  --include_path                          ""
% 3.39/0.98  --clausifier                            res/vclausify_rel
% 3.39/0.98  --clausifier_options                    --mode clausify
% 3.39/0.98  --stdin                                 false
% 3.39/0.98  --stats_out                             all
% 3.39/0.98  
% 3.39/0.98  ------ General Options
% 3.39/0.98  
% 3.39/0.98  --fof                                   false
% 3.39/0.98  --time_out_real                         305.
% 3.39/0.98  --time_out_virtual                      -1.
% 3.39/0.98  --symbol_type_check                     false
% 3.39/0.98  --clausify_out                          false
% 3.39/0.98  --sig_cnt_out                           false
% 3.39/0.98  --trig_cnt_out                          false
% 3.39/0.98  --trig_cnt_out_tolerance                1.
% 3.39/0.98  --trig_cnt_out_sk_spl                   false
% 3.39/0.98  --abstr_cl_out                          false
% 3.39/0.98  
% 3.39/0.98  ------ Global Options
% 3.39/0.98  
% 3.39/0.98  --schedule                              default
% 3.39/0.98  --add_important_lit                     false
% 3.39/0.98  --prop_solver_per_cl                    1000
% 3.39/0.98  --min_unsat_core                        false
% 3.39/0.98  --soft_assumptions                      false
% 3.39/0.98  --soft_lemma_size                       3
% 3.39/0.98  --prop_impl_unit_size                   0
% 3.39/0.98  --prop_impl_unit                        []
% 3.39/0.98  --share_sel_clauses                     true
% 3.39/0.98  --reset_solvers                         false
% 3.39/0.98  --bc_imp_inh                            [conj_cone]
% 3.39/0.98  --conj_cone_tolerance                   3.
% 3.39/0.98  --extra_neg_conj                        none
% 3.39/0.98  --large_theory_mode                     true
% 3.39/0.98  --prolific_symb_bound                   200
% 3.39/0.98  --lt_threshold                          2000
% 3.39/0.98  --clause_weak_htbl                      true
% 3.39/0.98  --gc_record_bc_elim                     false
% 3.39/0.98  
% 3.39/0.98  ------ Preprocessing Options
% 3.39/0.98  
% 3.39/0.98  --preprocessing_flag                    true
% 3.39/0.98  --time_out_prep_mult                    0.1
% 3.39/0.98  --splitting_mode                        input
% 3.39/0.98  --splitting_grd                         true
% 3.39/0.98  --splitting_cvd                         false
% 3.39/0.98  --splitting_cvd_svl                     false
% 3.39/0.98  --splitting_nvd                         32
% 3.39/0.98  --sub_typing                            true
% 3.39/0.98  --prep_gs_sim                           true
% 3.39/0.98  --prep_unflatten                        true
% 3.39/0.98  --prep_res_sim                          true
% 3.39/0.98  --prep_upred                            true
% 3.39/0.98  --prep_sem_filter                       exhaustive
% 3.39/0.98  --prep_sem_filter_out                   false
% 3.39/0.98  --pred_elim                             true
% 3.39/0.98  --res_sim_input                         true
% 3.39/0.98  --eq_ax_congr_red                       true
% 3.39/0.98  --pure_diseq_elim                       true
% 3.39/0.98  --brand_transform                       false
% 3.39/0.98  --non_eq_to_eq                          false
% 3.39/0.98  --prep_def_merge                        true
% 3.39/0.98  --prep_def_merge_prop_impl              false
% 3.39/0.98  --prep_def_merge_mbd                    true
% 3.39/0.98  --prep_def_merge_tr_red                 false
% 3.39/0.98  --prep_def_merge_tr_cl                  false
% 3.39/0.98  --smt_preprocessing                     true
% 3.39/0.98  --smt_ac_axioms                         fast
% 3.39/0.98  --preprocessed_out                      false
% 3.39/0.98  --preprocessed_stats                    false
% 3.39/0.98  
% 3.39/0.98  ------ Abstraction refinement Options
% 3.39/0.98  
% 3.39/0.98  --abstr_ref                             []
% 3.39/0.98  --abstr_ref_prep                        false
% 3.39/0.98  --abstr_ref_until_sat                   false
% 3.39/0.98  --abstr_ref_sig_restrict                funpre
% 3.39/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/0.98  --abstr_ref_under                       []
% 3.39/0.98  
% 3.39/0.98  ------ SAT Options
% 3.39/0.98  
% 3.39/0.98  --sat_mode                              false
% 3.39/0.98  --sat_fm_restart_options                ""
% 3.39/0.98  --sat_gr_def                            false
% 3.39/0.98  --sat_epr_types                         true
% 3.39/0.98  --sat_non_cyclic_types                  false
% 3.39/0.98  --sat_finite_models                     false
% 3.39/0.98  --sat_fm_lemmas                         false
% 3.39/0.98  --sat_fm_prep                           false
% 3.39/0.98  --sat_fm_uc_incr                        true
% 3.39/0.98  --sat_out_model                         small
% 3.39/0.98  --sat_out_clauses                       false
% 3.39/0.98  
% 3.39/0.98  ------ QBF Options
% 3.39/0.98  
% 3.39/0.98  --qbf_mode                              false
% 3.39/0.98  --qbf_elim_univ                         false
% 3.39/0.98  --qbf_dom_inst                          none
% 3.39/0.98  --qbf_dom_pre_inst                      false
% 3.39/0.98  --qbf_sk_in                             false
% 3.39/0.98  --qbf_pred_elim                         true
% 3.39/0.98  --qbf_split                             512
% 3.39/0.98  
% 3.39/0.98  ------ BMC1 Options
% 3.39/0.98  
% 3.39/0.98  --bmc1_incremental                      false
% 3.39/0.98  --bmc1_axioms                           reachable_all
% 3.39/0.98  --bmc1_min_bound                        0
% 3.39/0.98  --bmc1_max_bound                        -1
% 3.39/0.98  --bmc1_max_bound_default                -1
% 3.39/0.98  --bmc1_symbol_reachability              true
% 3.39/0.98  --bmc1_property_lemmas                  false
% 3.39/0.98  --bmc1_k_induction                      false
% 3.39/0.98  --bmc1_non_equiv_states                 false
% 3.39/0.98  --bmc1_deadlock                         false
% 3.39/0.98  --bmc1_ucm                              false
% 3.39/0.98  --bmc1_add_unsat_core                   none
% 3.39/0.98  --bmc1_unsat_core_children              false
% 3.39/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/0.98  --bmc1_out_stat                         full
% 3.39/0.98  --bmc1_ground_init                      false
% 3.39/0.98  --bmc1_pre_inst_next_state              false
% 3.39/0.98  --bmc1_pre_inst_state                   false
% 3.39/0.98  --bmc1_pre_inst_reach_state             false
% 3.39/0.98  --bmc1_out_unsat_core                   false
% 3.39/0.98  --bmc1_aig_witness_out                  false
% 3.39/0.98  --bmc1_verbose                          false
% 3.39/0.98  --bmc1_dump_clauses_tptp                false
% 3.39/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.39/0.98  --bmc1_dump_file                        -
% 3.39/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.39/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.39/0.98  --bmc1_ucm_extend_mode                  1
% 3.39/0.98  --bmc1_ucm_init_mode                    2
% 3.39/0.98  --bmc1_ucm_cone_mode                    none
% 3.39/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.39/0.98  --bmc1_ucm_relax_model                  4
% 3.39/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.39/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/0.98  --bmc1_ucm_layered_model                none
% 3.39/0.98  --bmc1_ucm_max_lemma_size               10
% 3.39/0.98  
% 3.39/0.98  ------ AIG Options
% 3.39/0.98  
% 3.39/0.98  --aig_mode                              false
% 3.39/0.98  
% 3.39/0.98  ------ Instantiation Options
% 3.39/0.98  
% 3.39/0.98  --instantiation_flag                    true
% 3.39/0.98  --inst_sos_flag                         false
% 3.39/0.98  --inst_sos_phase                        true
% 3.39/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/0.98  --inst_lit_sel_side                     none
% 3.39/0.98  --inst_solver_per_active                1400
% 3.39/0.98  --inst_solver_calls_frac                1.
% 3.39/0.98  --inst_passive_queue_type               priority_queues
% 3.39/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/0.98  --inst_passive_queues_freq              [25;2]
% 3.39/0.98  --inst_dismatching                      true
% 3.39/0.98  --inst_eager_unprocessed_to_passive     true
% 3.39/0.98  --inst_prop_sim_given                   true
% 3.39/0.98  --inst_prop_sim_new                     false
% 3.39/0.98  --inst_subs_new                         false
% 3.39/0.98  --inst_eq_res_simp                      false
% 3.39/0.98  --inst_subs_given                       false
% 3.39/0.98  --inst_orphan_elimination               true
% 3.39/0.98  --inst_learning_loop_flag               true
% 3.39/0.98  --inst_learning_start                   3000
% 3.39/0.98  --inst_learning_factor                  2
% 3.39/0.98  --inst_start_prop_sim_after_learn       3
% 3.39/0.98  --inst_sel_renew                        solver
% 3.39/0.98  --inst_lit_activity_flag                true
% 3.39/0.98  --inst_restr_to_given                   false
% 3.39/0.98  --inst_activity_threshold               500
% 3.39/0.98  --inst_out_proof                        true
% 3.39/0.98  
% 3.39/0.98  ------ Resolution Options
% 3.39/0.98  
% 3.39/0.98  --resolution_flag                       false
% 3.39/0.98  --res_lit_sel                           adaptive
% 3.39/0.98  --res_lit_sel_side                      none
% 3.39/0.98  --res_ordering                          kbo
% 3.39/0.98  --res_to_prop_solver                    active
% 3.39/0.98  --res_prop_simpl_new                    false
% 3.39/0.98  --res_prop_simpl_given                  true
% 3.39/0.98  --res_passive_queue_type                priority_queues
% 3.39/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/0.98  --res_passive_queues_freq               [15;5]
% 3.39/0.98  --res_forward_subs                      full
% 3.39/0.98  --res_backward_subs                     full
% 3.39/0.98  --res_forward_subs_resolution           true
% 3.39/0.98  --res_backward_subs_resolution          true
% 3.39/0.98  --res_orphan_elimination                true
% 3.39/0.98  --res_time_limit                        2.
% 3.39/0.98  --res_out_proof                         true
% 3.39/0.98  
% 3.39/0.98  ------ Superposition Options
% 3.39/0.98  
% 3.39/0.98  --superposition_flag                    true
% 3.39/0.98  --sup_passive_queue_type                priority_queues
% 3.39/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.39/0.98  --demod_completeness_check              fast
% 3.39/0.98  --demod_use_ground                      true
% 3.39/0.98  --sup_to_prop_solver                    passive
% 3.39/0.98  --sup_prop_simpl_new                    true
% 3.39/0.98  --sup_prop_simpl_given                  true
% 3.39/0.98  --sup_fun_splitting                     false
% 3.39/0.98  --sup_smt_interval                      50000
% 3.39/0.98  
% 3.39/0.98  ------ Superposition Simplification Setup
% 3.39/0.98  
% 3.39/0.98  --sup_indices_passive                   []
% 3.39/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.98  --sup_full_bw                           [BwDemod]
% 3.39/0.98  --sup_immed_triv                        [TrivRules]
% 3.39/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.98  --sup_immed_bw_main                     []
% 3.39/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.98  
% 3.39/0.98  ------ Combination Options
% 3.39/0.98  
% 3.39/0.98  --comb_res_mult                         3
% 3.39/0.98  --comb_sup_mult                         2
% 3.39/0.98  --comb_inst_mult                        10
% 3.39/0.98  
% 3.39/0.98  ------ Debug Options
% 3.39/0.98  
% 3.39/0.98  --dbg_backtrace                         false
% 3.39/0.98  --dbg_dump_prop_clauses                 false
% 3.39/0.98  --dbg_dump_prop_clauses_file            -
% 3.39/0.98  --dbg_out_stat                          false
% 3.39/0.98  
% 3.39/0.98  
% 3.39/0.98  
% 3.39/0.98  
% 3.39/0.98  ------ Proving...
% 3.39/0.98  
% 3.39/0.98  
% 3.39/0.98  % SZS status Theorem for theBenchmark.p
% 3.39/0.98  
% 3.39/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.39/0.98  
% 3.39/0.98  fof(f4,conjecture,(
% 3.39/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 3.39/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.98  
% 3.39/0.98  fof(f5,negated_conjecture,(
% 3.39/0.98    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 3.39/0.98    inference(negated_conjecture,[],[f4])).
% 3.39/0.98  
% 3.39/0.98  fof(f11,plain,(
% 3.39/0.98    ? [X0] : ((~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.39/0.98    inference(ennf_transformation,[],[f5])).
% 3.39/0.98  
% 3.39/0.98  fof(f12,plain,(
% 3.39/0.98    ? [X0] : (~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.39/0.98    inference(flattening,[],[f11])).
% 3.39/0.98  
% 3.39/0.98  fof(f23,plain,(
% 3.39/0.98    ( ! [X0] : (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k5_relat_1(X0,sK5) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(sK5) & v1_relat_1(sK5))) )),
% 3.39/0.98    introduced(choice_axiom,[])).
% 3.39/0.98  
% 3.39/0.98  fof(f22,plain,(
% 3.39/0.98    ? [X0] : (~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v2_funct_1(sK4) & ? [X1] : (k5_relat_1(sK4,X1) = k6_relat_1(k1_relat_1(sK4)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 3.39/0.98    introduced(choice_axiom,[])).
% 3.39/0.98  
% 3.39/0.98  fof(f24,plain,(
% 3.39/0.98    ~v2_funct_1(sK4) & (k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4)) & v1_funct_1(sK5) & v1_relat_1(sK5)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 3.39/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f12,f23,f22])).
% 3.39/0.98  
% 3.39/0.98  fof(f42,plain,(
% 3.39/0.98    v1_relat_1(sK5)),
% 3.39/0.98    inference(cnf_transformation,[],[f24])).
% 3.39/0.98  
% 3.39/0.98  fof(f40,plain,(
% 3.39/0.98    v1_relat_1(sK4)),
% 3.39/0.98    inference(cnf_transformation,[],[f24])).
% 3.39/0.98  
% 3.39/0.98  fof(f13,plain,(
% 3.39/0.98    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.39/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.39/0.98  
% 3.39/0.98  fof(f17,plain,(
% 3.39/0.98    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))) & (! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~sP0(X0)))),
% 3.39/0.98    inference(nnf_transformation,[],[f13])).
% 3.39/0.98  
% 3.39/0.98  fof(f18,plain,(
% 3.39/0.98    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))) & (! [X3] : (! [X4] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~sP0(X0)))),
% 3.39/0.98    inference(rectify,[],[f17])).
% 3.39/0.98  
% 3.39/0.98  fof(f20,plain,(
% 3.39/0.98    ( ! [X1] : (! [X0] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) => (sK3(X0) != X1 & k5_relat_1(X1,X0) = k5_relat_1(sK3(X0),X0) & k1_relat_1(X1) = k1_relat_1(sK3(X0)) & r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))) )),
% 3.39/0.98    introduced(choice_axiom,[])).
% 3.39/0.98  
% 3.39/0.98  fof(f19,plain,(
% 3.39/0.98    ! [X0] : (? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (sK2(X0) != X2 & k5_relat_1(X2,X0) = k5_relat_1(sK2(X0),X0) & k1_relat_1(X2) = k1_relat_1(sK2(X0)) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0))))),
% 3.39/0.98    introduced(choice_axiom,[])).
% 3.39/0.98  
% 3.39/0.98  fof(f21,plain,(
% 3.39/0.98    ! [X0] : ((sP0(X0) | ((sK2(X0) != sK3(X0) & k5_relat_1(sK2(X0),X0) = k5_relat_1(sK3(X0),X0) & k1_relat_1(sK2(X0)) = k1_relat_1(sK3(X0)) & r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0)) & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))) & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0)))) & (! [X3] : (! [X4] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~sP0(X0)))),
% 3.39/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f20,f19])).
% 3.39/0.98  
% 3.39/0.98  fof(f32,plain,(
% 3.39/0.98    ( ! [X0] : (sP0(X0) | v1_relat_1(sK3(X0))) )),
% 3.39/0.98    inference(cnf_transformation,[],[f21])).
% 3.39/0.98  
% 3.39/0.98  fof(f1,axiom,(
% 3.39/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 3.39/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.98  
% 3.39/0.98  fof(f6,plain,(
% 3.39/0.98    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.39/0.98    inference(ennf_transformation,[],[f1])).
% 3.39/0.98  
% 3.39/0.98  fof(f25,plain,(
% 3.39/0.98    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.39/0.98    inference(cnf_transformation,[],[f6])).
% 3.39/0.98  
% 3.39/0.98  fof(f44,plain,(
% 3.39/0.98    k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4))),
% 3.39/0.98    inference(cnf_transformation,[],[f24])).
% 3.39/0.98  
% 3.39/0.98  fof(f14,plain,(
% 3.39/0.98    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 3.39/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.39/0.98  
% 3.39/0.98  fof(f16,plain,(
% 3.39/0.98    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 3.39/0.98    inference(nnf_transformation,[],[f14])).
% 3.39/0.98  
% 3.39/0.98  fof(f28,plain,(
% 3.39/0.98    ( ! [X0] : (v2_funct_1(X0) | ~sP0(X0) | ~sP1(X0)) )),
% 3.39/0.98    inference(cnf_transformation,[],[f16])).
% 3.39/0.98  
% 3.39/0.98  fof(f45,plain,(
% 3.39/0.98    ~v2_funct_1(sK4)),
% 3.39/0.98    inference(cnf_transformation,[],[f24])).
% 3.39/0.98  
% 3.39/0.98  fof(f41,plain,(
% 3.39/0.98    v1_funct_1(sK4)),
% 3.39/0.98    inference(cnf_transformation,[],[f24])).
% 3.39/0.98  
% 3.39/0.98  fof(f3,axiom,(
% 3.39/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) => X1 = X2)))))),
% 3.39/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.98  
% 3.39/0.98  fof(f9,plain,(
% 3.39/0.98    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : ((X1 = X2 | (k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.39/0.98    inference(ennf_transformation,[],[f3])).
% 3.39/0.98  
% 3.39/0.98  fof(f10,plain,(
% 3.39/0.98    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.39/0.98    inference(flattening,[],[f9])).
% 3.39/0.98  
% 3.39/0.98  fof(f15,plain,(
% 3.39/0.98    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.39/0.98    inference(definition_folding,[],[f10,f14,f13])).
% 3.39/0.98  
% 3.39/0.98  fof(f39,plain,(
% 3.39/0.98    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.39/0.98    inference(cnf_transformation,[],[f15])).
% 3.39/0.98  
% 3.39/0.98  fof(f37,plain,(
% 3.39/0.98    ( ! [X0] : (sP0(X0) | k5_relat_1(sK2(X0),X0) = k5_relat_1(sK3(X0),X0)) )),
% 3.39/0.98    inference(cnf_transformation,[],[f21])).
% 3.39/0.98  
% 3.39/0.98  fof(f35,plain,(
% 3.39/0.98    ( ! [X0] : (sP0(X0) | r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))) )),
% 3.39/0.98    inference(cnf_transformation,[],[f21])).
% 3.39/0.98  
% 3.39/0.98  fof(f2,axiom,(
% 3.39/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.39/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/0.98  
% 3.39/0.98  fof(f7,plain,(
% 3.39/0.98    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.39/0.98    inference(ennf_transformation,[],[f2])).
% 3.39/0.98  
% 3.39/0.98  fof(f8,plain,(
% 3.39/0.98    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.39/0.98    inference(flattening,[],[f7])).
% 3.39/0.98  
% 3.39/0.98  fof(f26,plain,(
% 3.39/0.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.39/0.98    inference(cnf_transformation,[],[f8])).
% 3.39/0.98  
% 3.39/0.98  fof(f34,plain,(
% 3.39/0.98    ( ! [X0] : (sP0(X0) | r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))) )),
% 3.39/0.98    inference(cnf_transformation,[],[f21])).
% 3.39/0.98  
% 3.39/0.98  fof(f30,plain,(
% 3.39/0.98    ( ! [X0] : (sP0(X0) | v1_relat_1(sK2(X0))) )),
% 3.39/0.98    inference(cnf_transformation,[],[f21])).
% 3.39/0.98  
% 3.39/0.98  fof(f38,plain,(
% 3.39/0.98    ( ! [X0] : (sP0(X0) | sK2(X0) != sK3(X0)) )),
% 3.39/0.98    inference(cnf_transformation,[],[f21])).
% 3.39/0.98  
% 3.39/0.98  cnf(c_18,negated_conjecture,
% 3.39/0.98      ( v1_relat_1(sK5) ),
% 3.39/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1310,negated_conjecture,
% 3.39/0.98      ( v1_relat_1(sK5) ),
% 3.39/0.98      inference(subtyping,[status(esa)],[c_18]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1682,plain,
% 3.39/0.98      ( v1_relat_1(sK5) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1310]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_20,negated_conjecture,
% 3.39/0.98      ( v1_relat_1(sK4) ),
% 3.39/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1308,negated_conjecture,
% 3.39/0.98      ( v1_relat_1(sK4) ),
% 3.39/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1684,plain,
% 3.39/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1308]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_10,plain,
% 3.39/0.98      ( sP0(X0) | v1_relat_1(sK3(X0)) ),
% 3.39/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1316,plain,
% 3.39/0.98      ( sP0(X0_42) | v1_relat_1(sK3(X0_42)) ),
% 3.39/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1677,plain,
% 3.39/0.98      ( sP0(X0_42) = iProver_top | v1_relat_1(sK3(X0_42)) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1316]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_0,plain,
% 3.39/0.98      ( ~ v1_relat_1(X0)
% 3.39/0.98      | ~ v1_relat_1(X1)
% 3.39/0.98      | ~ v1_relat_1(X2)
% 3.39/0.98      | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
% 3.39/0.98      inference(cnf_transformation,[],[f25]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1324,plain,
% 3.39/0.98      ( ~ v1_relat_1(X0_42)
% 3.39/0.98      | ~ v1_relat_1(X1_42)
% 3.39/0.98      | ~ v1_relat_1(X2_42)
% 3.39/0.98      | k5_relat_1(k5_relat_1(X2_42,X1_42),X0_42) = k5_relat_1(X2_42,k5_relat_1(X1_42,X0_42)) ),
% 3.39/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1669,plain,
% 3.39/0.98      ( k5_relat_1(k5_relat_1(X0_42,X1_42),X2_42) = k5_relat_1(X0_42,k5_relat_1(X1_42,X2_42))
% 3.39/0.98      | v1_relat_1(X2_42) != iProver_top
% 3.39/0.98      | v1_relat_1(X1_42) != iProver_top
% 3.39/0.98      | v1_relat_1(X0_42) != iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1324]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_2074,plain,
% 3.39/0.98      ( k5_relat_1(sK3(X0_42),k5_relat_1(X1_42,X2_42)) = k5_relat_1(k5_relat_1(sK3(X0_42),X1_42),X2_42)
% 3.39/0.98      | sP0(X0_42) = iProver_top
% 3.39/0.98      | v1_relat_1(X1_42) != iProver_top
% 3.39/0.98      | v1_relat_1(X2_42) != iProver_top ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_1677,c_1669]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_4267,plain,
% 3.39/0.98      ( k5_relat_1(k5_relat_1(sK3(X0_42),sK4),X1_42) = k5_relat_1(sK3(X0_42),k5_relat_1(sK4,X1_42))
% 3.39/0.98      | sP0(X0_42) = iProver_top
% 3.39/0.98      | v1_relat_1(X1_42) != iProver_top ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_1684,c_2074]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_4868,plain,
% 3.39/0.98      ( k5_relat_1(sK3(X0_42),k5_relat_1(sK4,sK5)) = k5_relat_1(k5_relat_1(sK3(X0_42),sK4),sK5)
% 3.39/0.98      | sP0(X0_42) = iProver_top ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_1682,c_4267]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_16,negated_conjecture,
% 3.39/0.98      ( k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4)) ),
% 3.39/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1312,negated_conjecture,
% 3.39/0.98      ( k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4)) ),
% 3.39/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_4890,plain,
% 3.39/0.98      ( k5_relat_1(sK3(X0_42),k6_relat_1(k1_relat_1(sK4))) = k5_relat_1(k5_relat_1(sK3(X0_42),sK4),sK5)
% 3.39/0.98      | sP0(X0_42) = iProver_top ),
% 3.39/0.98      inference(light_normalisation,[status(thm)],[c_4868,c_1312]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_2,plain,
% 3.39/0.98      ( ~ sP1(X0) | ~ sP0(X0) | v2_funct_1(X0) ),
% 3.39/0.98      inference(cnf_transformation,[],[f28]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_15,negated_conjecture,
% 3.39/0.98      ( ~ v2_funct_1(sK4) ),
% 3.39/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_230,plain,
% 3.39/0.98      ( ~ sP1(X0) | ~ sP0(X0) | sK4 != X0 ),
% 3.39/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_15]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_231,plain,
% 3.39/0.98      ( ~ sP1(sK4) | ~ sP0(sK4) ),
% 3.39/0.98      inference(unflattening,[status(thm)],[c_230]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_19,negated_conjecture,
% 3.39/0.98      ( v1_funct_1(sK4) ),
% 3.39/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_14,plain,
% 3.39/0.98      ( ~ v1_funct_1(X0) | sP1(X0) | ~ v1_relat_1(X0) ),
% 3.39/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_27,plain,
% 3.39/0.98      ( ~ v1_funct_1(sK4) | sP1(sK4) | ~ v1_relat_1(sK4) ),
% 3.39/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_61,plain,
% 3.39/0.98      ( ~ sP1(sK4) | ~ sP0(sK4) | v2_funct_1(sK4) ),
% 3.39/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_233,plain,
% 3.39/0.98      ( ~ sP0(sK4) ),
% 3.39/0.98      inference(global_propositional_subsumption,
% 3.39/0.98                [status(thm)],
% 3.39/0.98                [c_231,c_20,c_19,c_15,c_27,c_61]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1307,plain,
% 3.39/0.98      ( ~ sP0(sK4) ),
% 3.39/0.98      inference(subtyping,[status(esa)],[c_233]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1685,plain,
% 3.39/0.98      ( sP0(sK4) != iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1307]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_5014,plain,
% 3.39/0.98      ( k5_relat_1(k5_relat_1(sK3(sK4),sK4),sK5) = k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4))) ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_4890,c_1685]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_5,plain,
% 3.39/0.98      ( sP0(X0) | k5_relat_1(sK3(X0),X0) = k5_relat_1(sK2(X0),X0) ),
% 3.39/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1321,plain,
% 3.39/0.98      ( sP0(X0_42)
% 3.39/0.98      | k5_relat_1(sK3(X0_42),X0_42) = k5_relat_1(sK2(X0_42),X0_42) ),
% 3.39/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1672,plain,
% 3.39/0.98      ( k5_relat_1(sK3(X0_42),X0_42) = k5_relat_1(sK2(X0_42),X0_42)
% 3.39/0.98      | sP0(X0_42) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1321]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_2466,plain,
% 3.39/0.98      ( k5_relat_1(sK2(sK4),sK4) = k5_relat_1(sK3(sK4),sK4) ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_1672,c_1685]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_5015,plain,
% 3.39/0.98      ( k5_relat_1(k5_relat_1(sK2(sK4),sK4),sK5) = k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4))) ),
% 3.39/0.98      inference(light_normalisation,[status(thm)],[c_5014,c_2466]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_7,plain,
% 3.39/0.98      ( r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) | sP0(X0) ),
% 3.39/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1319,plain,
% 3.39/0.98      ( r1_tarski(k2_relat_1(sK3(X0_42)),k1_relat_1(X0_42))
% 3.39/0.98      | sP0(X0_42) ),
% 3.39/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1674,plain,
% 3.39/0.98      ( r1_tarski(k2_relat_1(sK3(X0_42)),k1_relat_1(X0_42)) = iProver_top
% 3.39/0.98      | sP0(X0_42) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1319]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1,plain,
% 3.39/0.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.39/0.98      | ~ v1_relat_1(X0)
% 3.39/0.98      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 3.39/0.98      inference(cnf_transformation,[],[f26]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1323,plain,
% 3.39/0.98      ( ~ r1_tarski(k2_relat_1(X0_42),X0_43)
% 3.39/0.98      | ~ v1_relat_1(X0_42)
% 3.39/0.98      | k5_relat_1(X0_42,k6_relat_1(X0_43)) = X0_42 ),
% 3.39/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1670,plain,
% 3.39/0.98      ( k5_relat_1(X0_42,k6_relat_1(X0_43)) = X0_42
% 3.39/0.98      | r1_tarski(k2_relat_1(X0_42),X0_43) != iProver_top
% 3.39/0.98      | v1_relat_1(X0_42) != iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1323]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_2523,plain,
% 3.39/0.98      ( k5_relat_1(sK3(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK3(X0_42)
% 3.39/0.98      | sP0(X0_42) = iProver_top
% 3.39/0.98      | v1_relat_1(sK3(X0_42)) != iProver_top ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_1674,c_1670]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1366,plain,
% 3.39/0.98      ( r1_tarski(k2_relat_1(sK3(X0_42)),k1_relat_1(X0_42)) = iProver_top
% 3.39/0.98      | sP0(X0_42) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1319]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1369,plain,
% 3.39/0.98      ( sP0(X0_42) = iProver_top | v1_relat_1(sK3(X0_42)) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1316]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1818,plain,
% 3.39/0.98      ( ~ r1_tarski(k2_relat_1(sK3(X0_42)),k1_relat_1(X0_42))
% 3.39/0.98      | ~ v1_relat_1(sK3(X0_42))
% 3.39/0.98      | k5_relat_1(sK3(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK3(X0_42) ),
% 3.39/0.98      inference(instantiation,[status(thm)],[c_1323]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1819,plain,
% 3.39/0.98      ( k5_relat_1(sK3(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK3(X0_42)
% 3.39/0.98      | r1_tarski(k2_relat_1(sK3(X0_42)),k1_relat_1(X0_42)) != iProver_top
% 3.39/0.98      | v1_relat_1(sK3(X0_42)) != iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1818]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_5474,plain,
% 3.39/0.98      ( sP0(X0_42) = iProver_top
% 3.39/0.98      | k5_relat_1(sK3(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK3(X0_42) ),
% 3.39/0.98      inference(global_propositional_subsumption,
% 3.39/0.98                [status(thm)],
% 3.39/0.98                [c_2523,c_1366,c_1369,c_1819]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_5475,plain,
% 3.39/0.98      ( k5_relat_1(sK3(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK3(X0_42)
% 3.39/0.98      | sP0(X0_42) = iProver_top ),
% 3.39/0.98      inference(renaming,[status(thm)],[c_5474]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_5482,plain,
% 3.39/0.98      ( k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4))) = sK3(sK4) ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_5475,c_1685]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_8,plain,
% 3.39/0.98      ( r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0)) | sP0(X0) ),
% 3.39/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1318,plain,
% 3.39/0.98      ( r1_tarski(k2_relat_1(sK2(X0_42)),k1_relat_1(X0_42))
% 3.39/0.98      | sP0(X0_42) ),
% 3.39/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1675,plain,
% 3.39/0.98      ( r1_tarski(k2_relat_1(sK2(X0_42)),k1_relat_1(X0_42)) = iProver_top
% 3.39/0.98      | sP0(X0_42) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1318]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_2618,plain,
% 3.39/0.98      ( k5_relat_1(sK2(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK2(X0_42)
% 3.39/0.98      | sP0(X0_42) = iProver_top
% 3.39/0.98      | v1_relat_1(sK2(X0_42)) != iProver_top ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_1675,c_1670]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1367,plain,
% 3.39/0.98      ( r1_tarski(k2_relat_1(sK2(X0_42)),k1_relat_1(X0_42)) = iProver_top
% 3.39/0.98      | sP0(X0_42) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1318]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_12,plain,
% 3.39/0.98      ( sP0(X0) | v1_relat_1(sK2(X0)) ),
% 3.39/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1314,plain,
% 3.39/0.98      ( sP0(X0_42) | v1_relat_1(sK2(X0_42)) ),
% 3.39/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1371,plain,
% 3.39/0.98      ( sP0(X0_42) = iProver_top | v1_relat_1(sK2(X0_42)) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1314]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1813,plain,
% 3.39/0.98      ( ~ r1_tarski(k2_relat_1(sK2(X0_42)),k1_relat_1(X0_42))
% 3.39/0.98      | ~ v1_relat_1(sK2(X0_42))
% 3.39/0.98      | k5_relat_1(sK2(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK2(X0_42) ),
% 3.39/0.98      inference(instantiation,[status(thm)],[c_1323]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1814,plain,
% 3.39/0.98      ( k5_relat_1(sK2(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK2(X0_42)
% 3.39/0.98      | r1_tarski(k2_relat_1(sK2(X0_42)),k1_relat_1(X0_42)) != iProver_top
% 3.39/0.98      | v1_relat_1(sK2(X0_42)) != iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1813]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_5600,plain,
% 3.39/0.98      ( sP0(X0_42) = iProver_top
% 3.39/0.98      | k5_relat_1(sK2(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK2(X0_42) ),
% 3.39/0.98      inference(global_propositional_subsumption,
% 3.39/0.98                [status(thm)],
% 3.39/0.98                [c_2618,c_1367,c_1371,c_1814]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_5601,plain,
% 3.39/0.98      ( k5_relat_1(sK2(X0_42),k6_relat_1(k1_relat_1(X0_42))) = sK2(X0_42)
% 3.39/0.98      | sP0(X0_42) = iProver_top ),
% 3.39/0.98      inference(renaming,[status(thm)],[c_5600]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_5608,plain,
% 3.39/0.98      ( k5_relat_1(sK2(sK4),k6_relat_1(k1_relat_1(sK4))) = sK2(sK4) ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_5601,c_1685]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1679,plain,
% 3.39/0.98      ( sP0(X0_42) = iProver_top | v1_relat_1(sK2(X0_42)) = iProver_top ),
% 3.39/0.98      inference(predicate_to_equality,[status(thm)],[c_1314]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_2117,plain,
% 3.39/0.98      ( k5_relat_1(sK2(X0_42),k5_relat_1(X1_42,X2_42)) = k5_relat_1(k5_relat_1(sK2(X0_42),X1_42),X2_42)
% 3.39/0.98      | sP0(X0_42) = iProver_top
% 3.39/0.98      | v1_relat_1(X1_42) != iProver_top
% 3.39/0.98      | v1_relat_1(X2_42) != iProver_top ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_1679,c_1669]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_5250,plain,
% 3.39/0.98      ( k5_relat_1(k5_relat_1(sK2(X0_42),sK4),X1_42) = k5_relat_1(sK2(X0_42),k5_relat_1(sK4,X1_42))
% 3.39/0.98      | sP0(X0_42) = iProver_top
% 3.39/0.98      | v1_relat_1(X1_42) != iProver_top ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_1684,c_2117]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_5868,plain,
% 3.39/0.98      ( k5_relat_1(sK2(X0_42),k5_relat_1(sK4,sK5)) = k5_relat_1(k5_relat_1(sK2(X0_42),sK4),sK5)
% 3.39/0.98      | sP0(X0_42) = iProver_top ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_1682,c_5250]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_5890,plain,
% 3.39/0.98      ( k5_relat_1(sK2(X0_42),k6_relat_1(k1_relat_1(sK4))) = k5_relat_1(k5_relat_1(sK2(X0_42),sK4),sK5)
% 3.39/0.98      | sP0(X0_42) = iProver_top ),
% 3.39/0.98      inference(light_normalisation,[status(thm)],[c_5868,c_1312]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_5908,plain,
% 3.39/0.98      ( k5_relat_1(k5_relat_1(sK2(sK4),sK4),sK5) = k5_relat_1(sK2(sK4),k6_relat_1(k1_relat_1(sK4))) ),
% 3.39/0.98      inference(superposition,[status(thm)],[c_5890,c_1685]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_6987,plain,
% 3.39/0.98      ( k5_relat_1(k5_relat_1(sK2(sK4),sK4),sK5) = sK2(sK4) ),
% 3.39/0.98      inference(demodulation,[status(thm)],[c_5608,c_5908]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_8504,plain,
% 3.39/0.98      ( sK3(sK4) = sK2(sK4) ),
% 3.39/0.98      inference(light_normalisation,[status(thm)],[c_5015,c_5482,c_6987]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_4,plain,
% 3.39/0.98      ( sP0(X0) | sK3(X0) != sK2(X0) ),
% 3.39/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1322,plain,
% 3.39/0.98      ( sP0(X0_42) | sK3(X0_42) != sK2(X0_42) ),
% 3.39/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(c_1358,plain,
% 3.39/0.98      ( sP0(sK4) | sK3(sK4) != sK2(sK4) ),
% 3.39/0.98      inference(instantiation,[status(thm)],[c_1322]) ).
% 3.39/0.98  
% 3.39/0.98  cnf(contradiction,plain,
% 3.39/0.98      ( $false ),
% 3.39/0.98      inference(minisat,
% 3.39/0.98                [status(thm)],
% 3.39/0.98                [c_8504,c_1358,c_61,c_27,c_15,c_19,c_20]) ).
% 3.39/0.98  
% 3.39/0.98  
% 3.39/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.39/0.98  
% 3.39/0.98  ------                               Statistics
% 3.39/0.98  
% 3.39/0.98  ------ General
% 3.39/0.98  
% 3.39/0.98  abstr_ref_over_cycles:                  0
% 3.39/0.98  abstr_ref_under_cycles:                 0
% 3.39/0.98  gc_basic_clause_elim:                   0
% 3.39/0.98  forced_gc_time:                         0
% 3.39/0.98  parsing_time:                           0.007
% 3.39/0.98  unif_index_cands_time:                  0.
% 3.39/0.98  unif_index_add_time:                    0.
% 3.39/0.98  orderings_time:                         0.
% 3.39/0.98  out_proof_time:                         0.007
% 3.39/0.98  total_time:                             0.274
% 3.39/0.98  num_of_symbols:                         48
% 3.39/0.98  num_of_terms:                           8493
% 3.39/0.98  
% 3.39/0.98  ------ Preprocessing
% 3.39/0.98  
% 3.39/0.98  num_of_splits:                          0
% 3.39/0.98  num_of_split_atoms:                     0
% 3.39/0.98  num_of_reused_defs:                     0
% 3.39/0.98  num_eq_ax_congr_red:                    8
% 3.39/0.98  num_of_sem_filtered_clauses:            1
% 3.39/0.98  num_of_subtypes:                        3
% 3.39/0.98  monotx_restored_types:                  0
% 3.39/0.98  sat_num_of_epr_types:                   0
% 3.39/0.98  sat_num_of_non_cyclic_types:            0
% 3.39/0.98  sat_guarded_non_collapsed_types:        1
% 3.39/0.98  num_pure_diseq_elim:                    0
% 3.39/0.98  simp_replaced_by:                       0
% 3.39/0.98  res_preprocessed:                       102
% 3.39/0.98  prep_upred:                             0
% 3.39/0.98  prep_unflattend:                        37
% 3.39/0.98  smt_new_axioms:                         0
% 3.39/0.98  pred_elim_cands:                        4
% 3.39/0.98  pred_elim:                              2
% 3.39/0.98  pred_elim_cl:                           3
% 3.39/0.98  pred_elim_cycles:                       4
% 3.39/0.98  merged_defs:                            0
% 3.39/0.98  merged_defs_ncl:                        0
% 3.39/0.98  bin_hyper_res:                          0
% 3.39/0.98  prep_cycles:                            4
% 3.39/0.98  pred_elim_time:                         0.015
% 3.39/0.98  splitting_time:                         0.
% 3.39/0.98  sem_filter_time:                        0.
% 3.39/0.98  monotx_time:                            0.
% 3.39/0.98  subtype_inf_time:                       0.
% 3.39/0.98  
% 3.39/0.98  ------ Problem properties
% 3.39/0.98  
% 3.39/0.98  clauses:                                18
% 3.39/0.98  conjectures:                            5
% 3.39/0.98  epr:                                    5
% 3.39/0.98  horn:                                   10
% 3.39/0.98  ground:                                 6
% 3.39/0.98  unary:                                  6
% 3.39/0.98  binary:                                 9
% 3.39/0.98  lits:                                   41
% 3.39/0.98  lits_eq:                                9
% 3.39/0.98  fd_pure:                                0
% 3.39/0.98  fd_pseudo:                              0
% 3.39/0.98  fd_cond:                                0
% 3.39/0.98  fd_pseudo_cond:                         1
% 3.39/0.98  ac_symbols:                             0
% 3.39/0.98  
% 3.39/0.98  ------ Propositional Solver
% 3.39/0.98  
% 3.39/0.98  prop_solver_calls:                      32
% 3.39/0.98  prop_fast_solver_calls:                 941
% 3.39/0.98  smt_solver_calls:                       0
% 3.39/0.98  smt_fast_solver_calls:                  0
% 3.39/0.98  prop_num_of_clauses:                    2456
% 3.39/0.98  prop_preprocess_simplified:             6313
% 3.39/0.98  prop_fo_subsumed:                       5
% 3.39/0.98  prop_solver_time:                       0.
% 3.39/0.98  smt_solver_time:                        0.
% 3.39/0.98  smt_fast_solver_time:                   0.
% 3.39/0.98  prop_fast_solver_time:                  0.
% 3.39/0.98  prop_unsat_core_time:                   0.
% 3.39/0.98  
% 3.39/0.98  ------ QBF
% 3.39/0.98  
% 3.39/0.98  qbf_q_res:                              0
% 3.39/0.98  qbf_num_tautologies:                    0
% 3.39/0.98  qbf_prep_cycles:                        0
% 3.39/0.98  
% 3.39/0.98  ------ BMC1
% 3.39/0.98  
% 3.39/0.98  bmc1_current_bound:                     -1
% 3.39/0.98  bmc1_last_solved_bound:                 -1
% 3.39/0.98  bmc1_unsat_core_size:                   -1
% 3.39/0.98  bmc1_unsat_core_parents_size:           -1
% 3.39/0.98  bmc1_merge_next_fun:                    0
% 3.39/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.39/0.98  
% 3.39/0.98  ------ Instantiation
% 3.39/0.98  
% 3.39/0.98  inst_num_of_clauses:                    934
% 3.39/0.98  inst_num_in_passive:                    99
% 3.39/0.98  inst_num_in_active:                     444
% 3.39/0.98  inst_num_in_unprocessed:                391
% 3.39/0.98  inst_num_of_loops:                      480
% 3.39/0.98  inst_num_of_learning_restarts:          0
% 3.39/0.98  inst_num_moves_active_passive:          28
% 3.39/0.98  inst_lit_activity:                      0
% 3.39/0.98  inst_lit_activity_moves:                0
% 3.39/0.98  inst_num_tautologies:                   0
% 3.39/0.98  inst_num_prop_implied:                  0
% 3.39/0.98  inst_num_existing_simplified:           0
% 3.39/0.98  inst_num_eq_res_simplified:             0
% 3.39/0.98  inst_num_child_elim:                    0
% 3.39/0.98  inst_num_of_dismatching_blockings:      921
% 3.39/0.98  inst_num_of_non_proper_insts:           1536
% 3.39/0.98  inst_num_of_duplicates:                 0
% 3.39/0.98  inst_inst_num_from_inst_to_res:         0
% 3.39/0.98  inst_dismatching_checking_time:         0.
% 3.39/0.98  
% 3.39/0.98  ------ Resolution
% 3.39/0.98  
% 3.39/0.98  res_num_of_clauses:                     0
% 3.39/0.98  res_num_in_passive:                     0
% 3.39/0.98  res_num_in_active:                      0
% 3.39/0.98  res_num_of_loops:                       106
% 3.39/0.98  res_forward_subset_subsumed:            162
% 3.39/0.98  res_backward_subset_subsumed:           2
% 3.39/0.98  res_forward_subsumed:                   0
% 3.39/0.98  res_backward_subsumed:                  0
% 3.39/0.98  res_forward_subsumption_resolution:     0
% 3.39/0.98  res_backward_subsumption_resolution:    0
% 3.39/0.98  res_clause_to_clause_subsumption:       336
% 3.39/0.98  res_orphan_elimination:                 0
% 3.39/0.98  res_tautology_del:                      209
% 3.39/0.98  res_num_eq_res_simplified:              0
% 3.39/0.98  res_num_sel_changes:                    0
% 3.39/0.98  res_moves_from_active_to_pass:          0
% 3.39/0.98  
% 3.39/0.98  ------ Superposition
% 3.39/0.98  
% 3.39/0.98  sup_time_total:                         0.
% 3.39/0.98  sup_time_generating:                    0.
% 3.39/0.98  sup_time_sim_full:                      0.
% 3.39/0.98  sup_time_sim_immed:                     0.
% 3.39/0.98  
% 3.39/0.98  sup_num_of_clauses:                     152
% 3.39/0.98  sup_num_in_active:                      92
% 3.39/0.98  sup_num_in_passive:                     60
% 3.39/0.98  sup_num_of_loops:                       94
% 3.39/0.98  sup_fw_superposition:                   97
% 3.39/0.98  sup_bw_superposition:                   71
% 3.39/0.98  sup_immediate_simplified:               19
% 3.39/0.98  sup_given_eliminated:                   0
% 3.39/0.98  comparisons_done:                       0
% 3.39/0.98  comparisons_avoided:                    0
% 3.39/0.98  
% 3.39/0.98  ------ Simplifications
% 3.39/0.98  
% 3.39/0.98  
% 3.39/0.98  sim_fw_subset_subsumed:                 6
% 3.39/0.98  sim_bw_subset_subsumed:                 0
% 3.39/0.98  sim_fw_subsumed:                        0
% 3.39/0.98  sim_bw_subsumed:                        0
% 3.39/0.98  sim_fw_subsumption_res:                 0
% 3.39/0.98  sim_bw_subsumption_res:                 0
% 3.39/0.98  sim_tautology_del:                      0
% 3.39/0.98  sim_eq_tautology_del:                   4
% 3.39/0.98  sim_eq_res_simp:                        0
% 3.39/0.98  sim_fw_demodulated:                     0
% 3.39/0.98  sim_bw_demodulated:                     2
% 3.39/0.98  sim_light_normalised:                   14
% 3.39/0.98  sim_joinable_taut:                      0
% 3.39/0.98  sim_joinable_simp:                      0
% 3.39/0.98  sim_ac_normalised:                      0
% 3.39/0.98  sim_smt_subsumption:                    0
% 3.39/0.98  
%------------------------------------------------------------------------------
