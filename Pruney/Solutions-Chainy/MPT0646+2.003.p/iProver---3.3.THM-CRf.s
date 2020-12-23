%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:19 EST 2020

% Result     : Theorem 6.94s
% Output     : CNFRefutation 6.94s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 457 expanded)
%              Number of clauses        :   84 ( 132 expanded)
%              Number of leaves         :   14 ( 132 expanded)
%              Depth                    :   13
%              Number of atoms          :  484 (3004 expanded)
%              Number of equality atoms :  158 ( 771 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ? [X1] :
              ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & v1_funct_1(X1)
              & v1_relat_1(X1) )
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

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

fof(f45,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    v1_relat_1(sK5) ),
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

fof(f37,plain,(
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

fof(f8,plain,(
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
    inference(cnf_transformation,[],[f8])).

fof(f49,plain,(
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

fof(f33,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ sP0(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

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
    inference(ennf_transformation,[],[f5])).

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

fof(f44,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( sP0(X0)
      | k5_relat_1(sK2(X0),X0) = k5_relat_1(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0] :
      ( sP0(X0)
      | v1_relat_1(sK2(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0] :
      ( sP0(X0)
      | sK2(X0) != sK3(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0] :
      ( sP0(X0)
      | k1_relat_1(sK2(X0)) = k1_relat_1(sK3(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0] :
      ( sP0(X0)
      | r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0] :
      ( sP0(X0)
      | r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0] :
      ( sP0(X0)
      | v1_funct_1(sK3(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0] :
      ( sP0(X0)
      | v1_funct_1(sK2(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_25,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1831,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1833,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_15,plain,
    ( sP0(X0)
    | v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1838,plain,
    ( sP0(X0) = iProver_top
    | v1_relat_1(sK3(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1847,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3186,plain,
    ( k5_relat_1(sK3(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(sK3(X0),X1),X2)
    | sP0(X0) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_1847])).

cnf(c_19682,plain,
    ( k5_relat_1(k5_relat_1(sK3(X0),X1),sK5) = k5_relat_1(sK3(X0),k5_relat_1(X1,sK5))
    | sP0(X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1833,c_3186])).

cnf(c_20430,plain,
    ( k5_relat_1(k5_relat_1(sK3(X0),sK4),sK5) = k5_relat_1(sK3(X0),k5_relat_1(sK4,sK5))
    | sP0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1831,c_19682])).

cnf(c_21,negated_conjecture,
    ( k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20433,plain,
    ( k5_relat_1(k5_relat_1(sK3(X0),sK4),sK5) = k5_relat_1(sK3(X0),k6_relat_1(k1_relat_1(sK4)))
    | sP0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20430,c_21])).

cnf(c_7,plain,
    ( ~ sP1(X0)
    | ~ sP0(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_20,negated_conjecture,
    ( ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_278,plain,
    ( ~ sP1(X0)
    | ~ sP0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_279,plain,
    ( ~ sP1(sK4)
    | ~ sP0(sK4) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,plain,
    ( sP1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_32,plain,
    ( sP1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_66,plain,
    ( ~ sP1(sK4)
    | ~ sP0(sK4)
    | v2_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_281,plain,
    ( ~ sP0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_279,c_25,c_24,c_20,c_32,c_66])).

cnf(c_1830,plain,
    ( sP0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_20474,plain,
    ( k5_relat_1(k5_relat_1(sK3(sK4),sK4),sK5) = k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4))) ),
    inference(superposition,[status(thm)],[c_20433,c_1830])).

cnf(c_10,plain,
    ( sP0(X0)
    | k5_relat_1(sK3(X0),X0) = k5_relat_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1843,plain,
    ( k5_relat_1(sK3(X0),X0) = k5_relat_1(sK2(X0),X0)
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4285,plain,
    ( k5_relat_1(sK2(sK4),sK4) = k5_relat_1(sK3(sK4),sK4) ),
    inference(superposition,[status(thm)],[c_1843,c_1830])).

cnf(c_17,plain,
    ( sP0(X0)
    | v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1836,plain,
    ( sP0(X0) = iProver_top
    | v1_relat_1(sK2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2532,plain,
    ( k5_relat_1(sK2(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(sK2(X0),X1),X2)
    | sP0(X0) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1836,c_1847])).

cnf(c_6727,plain,
    ( k5_relat_1(k5_relat_1(sK2(X0),X1),sK5) = k5_relat_1(sK2(X0),k5_relat_1(X1,sK5))
    | sP0(X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1833,c_2532])).

cnf(c_8996,plain,
    ( k5_relat_1(k5_relat_1(sK2(X0),sK4),sK5) = k5_relat_1(sK2(X0),k5_relat_1(sK4,sK5))
    | sP0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1831,c_6727])).

cnf(c_8999,plain,
    ( k5_relat_1(k5_relat_1(sK2(X0),sK4),sK5) = k5_relat_1(sK2(X0),k6_relat_1(k1_relat_1(sK4)))
    | sP0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8996,c_21])).

cnf(c_9040,plain,
    ( k5_relat_1(sK2(sK4),k6_relat_1(k1_relat_1(sK4))) = k5_relat_1(k5_relat_1(sK2(sK4),sK4),sK5) ),
    inference(superposition,[status(thm)],[c_8999,c_1830])).

cnf(c_20475,plain,
    ( k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4))) = k5_relat_1(sK2(sK4),k6_relat_1(k1_relat_1(sK4))) ),
    inference(light_normalisation,[status(thm)],[c_20474,c_4285,c_9040])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f34])).

cnf(c_2006,plain,
    ( ~ r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X1))
    | ~ sP0(X1)
    | ~ v1_funct_1(sK3(X0))
    | ~ v1_funct_1(sK2(X0))
    | ~ v1_relat_1(sK3(X0))
    | ~ v1_relat_1(sK2(X0))
    | k5_relat_1(sK3(X0),X1) != k5_relat_1(sK2(X0),X1)
    | sK3(X0) = sK2(X0)
    | k1_relat_1(sK3(X0)) != k1_relat_1(sK2(X0)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2169,plain,
    ( ~ r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(k6_relat_1(X1)))
    | ~ r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(k6_relat_1(X1)))
    | ~ sP0(k6_relat_1(X1))
    | ~ v1_funct_1(sK3(X0))
    | ~ v1_funct_1(sK2(X0))
    | ~ v1_relat_1(sK3(X0))
    | ~ v1_relat_1(sK2(X0))
    | k5_relat_1(sK3(X0),k6_relat_1(X1)) != k5_relat_1(sK2(X0),k6_relat_1(X1))
    | sK3(X0) = sK2(X0)
    | k1_relat_1(sK3(X0)) != k1_relat_1(sK2(X0)) ),
    inference(instantiation,[status(thm)],[c_2006])).

cnf(c_8330,plain,
    ( ~ r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(k6_relat_1(k1_relat_1(X0))))
    | ~ r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(k6_relat_1(k1_relat_1(X0))))
    | ~ sP0(k6_relat_1(k1_relat_1(X0)))
    | ~ v1_funct_1(sK3(X0))
    | ~ v1_funct_1(sK2(X0))
    | ~ v1_relat_1(sK3(X0))
    | ~ v1_relat_1(sK2(X0))
    | k5_relat_1(sK3(X0),k6_relat_1(k1_relat_1(X0))) != k5_relat_1(sK2(X0),k6_relat_1(k1_relat_1(X0)))
    | sK3(X0) = sK2(X0)
    | k1_relat_1(sK3(X0)) != k1_relat_1(sK2(X0)) ),
    inference(instantiation,[status(thm)],[c_2169])).

cnf(c_8332,plain,
    ( ~ r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(k6_relat_1(k1_relat_1(sK4))))
    | ~ r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(k6_relat_1(k1_relat_1(sK4))))
    | ~ sP0(k6_relat_1(k1_relat_1(sK4)))
    | ~ v1_funct_1(sK3(sK4))
    | ~ v1_funct_1(sK2(sK4))
    | ~ v1_relat_1(sK3(sK4))
    | ~ v1_relat_1(sK2(sK4))
    | k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4))) != k5_relat_1(sK2(sK4),k6_relat_1(k1_relat_1(sK4)))
    | sK3(sK4) = sK2(sK4)
    | k1_relat_1(sK3(sK4)) != k1_relat_1(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_8330])).

cnf(c_1482,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2001,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_relat_1(sK2(X2)),k1_relat_1(X2))
    | X1 != k1_relat_1(X2)
    | X0 != k2_relat_1(sK2(X2)) ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_2099,plain,
    ( r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(sK2(X2)),k1_relat_1(X2))
    | X0 != k2_relat_1(sK2(X2))
    | k1_relat_1(X1) != k1_relat_1(X2) ),
    inference(instantiation,[status(thm)],[c_2001])).

cnf(c_2347,plain,
    ( ~ r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))
    | r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | k2_relat_1(sK2(X0)) != k2_relat_1(sK2(X0)) ),
    inference(instantiation,[status(thm)],[c_2099])).

cnf(c_3264,plain,
    ( ~ r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))
    | r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(k6_relat_1(X1)))
    | k1_relat_1(k6_relat_1(X1)) != k1_relat_1(X0)
    | k2_relat_1(sK2(X0)) != k2_relat_1(sK2(X0)) ),
    inference(instantiation,[status(thm)],[c_2347])).

cnf(c_4081,plain,
    ( ~ r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))
    | r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(k6_relat_1(k1_relat_1(X0))))
    | k1_relat_1(k6_relat_1(k1_relat_1(X0))) != k1_relat_1(X0)
    | k2_relat_1(sK2(X0)) != k2_relat_1(sK2(X0)) ),
    inference(instantiation,[status(thm)],[c_3264])).

cnf(c_4083,plain,
    ( r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(k6_relat_1(k1_relat_1(sK4))))
    | ~ r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(sK4))
    | k1_relat_1(k6_relat_1(k1_relat_1(sK4))) != k1_relat_1(sK4)
    | k2_relat_1(sK2(sK4)) != k2_relat_1(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_4081])).

cnf(c_1996,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_relat_1(sK3(X2)),k1_relat_1(X2))
    | X1 != k1_relat_1(X2)
    | X0 != k2_relat_1(sK3(X2)) ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_2066,plain,
    ( r1_tarski(X0,k1_relat_1(k6_relat_1(k1_relat_1(X1))))
    | ~ r1_tarski(k2_relat_1(sK3(X1)),k1_relat_1(X1))
    | X0 != k2_relat_1(sK3(X1))
    | k1_relat_1(k6_relat_1(k1_relat_1(X1))) != k1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_1996])).

cnf(c_2621,plain,
    ( ~ r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))
    | r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(k6_relat_1(k1_relat_1(X0))))
    | k1_relat_1(k6_relat_1(k1_relat_1(X0))) != k1_relat_1(X0)
    | k2_relat_1(sK3(X0)) != k2_relat_1(sK3(X0)) ),
    inference(instantiation,[status(thm)],[c_2066])).

cnf(c_2624,plain,
    ( r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(k6_relat_1(k1_relat_1(sK4))))
    | ~ r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(sK4))
    | k1_relat_1(k6_relat_1(k1_relat_1(sK4))) != k1_relat_1(sK4)
    | k2_relat_1(sK3(sK4)) != k2_relat_1(sK3(sK4)) ),
    inference(instantiation,[status(thm)],[c_2621])).

cnf(c_1473,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2348,plain,
    ( k2_relat_1(sK2(X0)) = k2_relat_1(sK2(X0)) ),
    inference(instantiation,[status(thm)],[c_1473])).

cnf(c_2351,plain,
    ( k2_relat_1(sK2(sK4)) = k2_relat_1(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_2348])).

cnf(c_2252,plain,
    ( k2_relat_1(sK3(X0)) = k2_relat_1(sK3(X0)) ),
    inference(instantiation,[status(thm)],[c_1473])).

cnf(c_2257,plain,
    ( k2_relat_1(sK3(sK4)) = k2_relat_1(sK3(sK4)) ),
    inference(instantiation,[status(thm)],[c_2252])).

cnf(c_5,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_8,plain,
    ( ~ sP1(X0)
    | sP0(X0)
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_261,plain,
    ( ~ sP1(X0)
    | sP0(X0)
    | k6_relat_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_8])).

cnf(c_262,plain,
    ( ~ sP1(k6_relat_1(X0))
    | sP0(k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_295,plain,
    ( sP0(k6_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k6_relat_1(X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_262])).

cnf(c_296,plain,
    ( sP0(k6_relat_1(X0))
    | ~ v1_funct_1(k6_relat_1(X0))
    | ~ v1_relat_1(k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_6,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_300,plain,
    ( sP0(k6_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_6,c_3])).

cnf(c_2124,plain,
    ( sP0(k6_relat_1(k1_relat_1(sK4))) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_2,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_2067,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(X0))) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2072,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(sK4))) = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2067])).

cnf(c_9,plain,
    ( sP0(X0)
    | sK3(X0) != sK2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_62,plain,
    ( sP0(sK4)
    | sK3(sK4) != sK2(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( sP0(X0)
    | k1_relat_1(sK3(X0)) = k1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_56,plain,
    ( sP0(sK4)
    | k1_relat_1(sK3(sK4)) = k1_relat_1(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_53,plain,
    ( r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(sK4))
    | sP0(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_50,plain,
    ( r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(sK4))
    | sP0(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( sP0(X0)
    | v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_47,plain,
    ( sP0(sK4)
    | v1_funct_1(sK3(sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_44,plain,
    ( sP0(sK4)
    | v1_relat_1(sK3(sK4)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_16,plain,
    ( sP0(X0)
    | v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_41,plain,
    ( sP0(sK4)
    | v1_funct_1(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_38,plain,
    ( sP0(sK4)
    | v1_relat_1(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20475,c_8332,c_4083,c_2624,c_2351,c_2257,c_2124,c_2072,c_66,c_62,c_56,c_53,c_50,c_47,c_44,c_41,c_38,c_32,c_20,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:25:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 6.94/1.54  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.94/1.54  
% 6.94/1.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.94/1.54  
% 6.94/1.54  ------  iProver source info
% 6.94/1.54  
% 6.94/1.54  git: date: 2020-06-30 10:37:57 +0100
% 6.94/1.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.94/1.54  git: non_committed_changes: false
% 6.94/1.54  git: last_make_outside_of_git: false
% 6.94/1.54  
% 6.94/1.54  ------ 
% 6.94/1.54  
% 6.94/1.54  ------ Input Options
% 6.94/1.54  
% 6.94/1.54  --out_options                           all
% 6.94/1.54  --tptp_safe_out                         true
% 6.94/1.54  --problem_path                          ""
% 6.94/1.54  --include_path                          ""
% 6.94/1.54  --clausifier                            res/vclausify_rel
% 6.94/1.54  --clausifier_options                    --mode clausify
% 6.94/1.54  --stdin                                 false
% 6.94/1.54  --stats_out                             all
% 6.94/1.54  
% 6.94/1.54  ------ General Options
% 6.94/1.54  
% 6.94/1.54  --fof                                   false
% 6.94/1.54  --time_out_real                         305.
% 6.94/1.54  --time_out_virtual                      -1.
% 6.94/1.54  --symbol_type_check                     false
% 6.94/1.54  --clausify_out                          false
% 6.94/1.54  --sig_cnt_out                           false
% 6.94/1.54  --trig_cnt_out                          false
% 6.94/1.54  --trig_cnt_out_tolerance                1.
% 6.94/1.54  --trig_cnt_out_sk_spl                   false
% 6.94/1.54  --abstr_cl_out                          false
% 6.94/1.54  
% 6.94/1.54  ------ Global Options
% 6.94/1.54  
% 6.94/1.54  --schedule                              default
% 6.94/1.54  --add_important_lit                     false
% 6.94/1.54  --prop_solver_per_cl                    1000
% 6.94/1.54  --min_unsat_core                        false
% 6.94/1.54  --soft_assumptions                      false
% 6.94/1.54  --soft_lemma_size                       3
% 6.94/1.54  --prop_impl_unit_size                   0
% 6.94/1.54  --prop_impl_unit                        []
% 6.94/1.54  --share_sel_clauses                     true
% 6.94/1.54  --reset_solvers                         false
% 6.94/1.54  --bc_imp_inh                            [conj_cone]
% 6.94/1.54  --conj_cone_tolerance                   3.
% 6.94/1.54  --extra_neg_conj                        none
% 6.94/1.54  --large_theory_mode                     true
% 6.94/1.54  --prolific_symb_bound                   200
% 6.94/1.54  --lt_threshold                          2000
% 6.94/1.54  --clause_weak_htbl                      true
% 6.94/1.54  --gc_record_bc_elim                     false
% 6.94/1.54  
% 6.94/1.54  ------ Preprocessing Options
% 6.94/1.54  
% 6.94/1.54  --preprocessing_flag                    true
% 6.94/1.54  --time_out_prep_mult                    0.1
% 6.94/1.54  --splitting_mode                        input
% 6.94/1.54  --splitting_grd                         true
% 6.94/1.54  --splitting_cvd                         false
% 6.94/1.54  --splitting_cvd_svl                     false
% 6.94/1.54  --splitting_nvd                         32
% 6.94/1.54  --sub_typing                            true
% 6.94/1.54  --prep_gs_sim                           true
% 6.94/1.54  --prep_unflatten                        true
% 6.94/1.54  --prep_res_sim                          true
% 6.94/1.54  --prep_upred                            true
% 6.94/1.54  --prep_sem_filter                       exhaustive
% 6.94/1.54  --prep_sem_filter_out                   false
% 6.94/1.54  --pred_elim                             true
% 6.94/1.54  --res_sim_input                         true
% 6.94/1.54  --eq_ax_congr_red                       true
% 6.94/1.54  --pure_diseq_elim                       true
% 6.94/1.54  --brand_transform                       false
% 6.94/1.54  --non_eq_to_eq                          false
% 6.94/1.54  --prep_def_merge                        true
% 6.94/1.54  --prep_def_merge_prop_impl              false
% 6.94/1.54  --prep_def_merge_mbd                    true
% 6.94/1.54  --prep_def_merge_tr_red                 false
% 6.94/1.54  --prep_def_merge_tr_cl                  false
% 6.94/1.54  --smt_preprocessing                     true
% 6.94/1.54  --smt_ac_axioms                         fast
% 6.94/1.54  --preprocessed_out                      false
% 6.94/1.54  --preprocessed_stats                    false
% 6.94/1.54  
% 6.94/1.54  ------ Abstraction refinement Options
% 6.94/1.54  
% 6.94/1.54  --abstr_ref                             []
% 6.94/1.54  --abstr_ref_prep                        false
% 6.94/1.54  --abstr_ref_until_sat                   false
% 6.94/1.54  --abstr_ref_sig_restrict                funpre
% 6.94/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 6.94/1.54  --abstr_ref_under                       []
% 6.94/1.54  
% 6.94/1.54  ------ SAT Options
% 6.94/1.54  
% 6.94/1.54  --sat_mode                              false
% 6.94/1.54  --sat_fm_restart_options                ""
% 6.94/1.54  --sat_gr_def                            false
% 6.94/1.54  --sat_epr_types                         true
% 6.94/1.54  --sat_non_cyclic_types                  false
% 6.94/1.54  --sat_finite_models                     false
% 6.94/1.54  --sat_fm_lemmas                         false
% 6.94/1.54  --sat_fm_prep                           false
% 6.94/1.54  --sat_fm_uc_incr                        true
% 6.94/1.54  --sat_out_model                         small
% 6.94/1.54  --sat_out_clauses                       false
% 6.94/1.54  
% 6.94/1.54  ------ QBF Options
% 6.94/1.54  
% 6.94/1.54  --qbf_mode                              false
% 6.94/1.54  --qbf_elim_univ                         false
% 6.94/1.54  --qbf_dom_inst                          none
% 6.94/1.54  --qbf_dom_pre_inst                      false
% 6.94/1.54  --qbf_sk_in                             false
% 6.94/1.54  --qbf_pred_elim                         true
% 6.94/1.54  --qbf_split                             512
% 6.94/1.54  
% 6.94/1.54  ------ BMC1 Options
% 6.94/1.54  
% 6.94/1.54  --bmc1_incremental                      false
% 6.94/1.54  --bmc1_axioms                           reachable_all
% 6.94/1.54  --bmc1_min_bound                        0
% 6.94/1.54  --bmc1_max_bound                        -1
% 6.94/1.54  --bmc1_max_bound_default                -1
% 6.94/1.54  --bmc1_symbol_reachability              true
% 6.94/1.54  --bmc1_property_lemmas                  false
% 6.94/1.54  --bmc1_k_induction                      false
% 6.94/1.54  --bmc1_non_equiv_states                 false
% 6.94/1.54  --bmc1_deadlock                         false
% 6.94/1.54  --bmc1_ucm                              false
% 6.94/1.54  --bmc1_add_unsat_core                   none
% 6.94/1.54  --bmc1_unsat_core_children              false
% 6.94/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 6.94/1.54  --bmc1_out_stat                         full
% 6.94/1.54  --bmc1_ground_init                      false
% 6.94/1.54  --bmc1_pre_inst_next_state              false
% 6.94/1.54  --bmc1_pre_inst_state                   false
% 6.94/1.54  --bmc1_pre_inst_reach_state             false
% 6.94/1.54  --bmc1_out_unsat_core                   false
% 6.94/1.54  --bmc1_aig_witness_out                  false
% 6.94/1.54  --bmc1_verbose                          false
% 6.94/1.54  --bmc1_dump_clauses_tptp                false
% 6.94/1.54  --bmc1_dump_unsat_core_tptp             false
% 6.94/1.54  --bmc1_dump_file                        -
% 6.94/1.54  --bmc1_ucm_expand_uc_limit              128
% 6.94/1.54  --bmc1_ucm_n_expand_iterations          6
% 6.94/1.54  --bmc1_ucm_extend_mode                  1
% 6.94/1.54  --bmc1_ucm_init_mode                    2
% 6.94/1.54  --bmc1_ucm_cone_mode                    none
% 6.94/1.54  --bmc1_ucm_reduced_relation_type        0
% 6.94/1.54  --bmc1_ucm_relax_model                  4
% 6.94/1.54  --bmc1_ucm_full_tr_after_sat            true
% 6.94/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 6.94/1.54  --bmc1_ucm_layered_model                none
% 6.94/1.54  --bmc1_ucm_max_lemma_size               10
% 6.94/1.54  
% 6.94/1.54  ------ AIG Options
% 6.94/1.54  
% 6.94/1.54  --aig_mode                              false
% 6.94/1.54  
% 6.94/1.54  ------ Instantiation Options
% 6.94/1.54  
% 6.94/1.54  --instantiation_flag                    true
% 6.94/1.54  --inst_sos_flag                         false
% 6.94/1.54  --inst_sos_phase                        true
% 6.94/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.94/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.94/1.54  --inst_lit_sel_side                     num_symb
% 6.94/1.54  --inst_solver_per_active                1400
% 6.94/1.54  --inst_solver_calls_frac                1.
% 6.94/1.54  --inst_passive_queue_type               priority_queues
% 6.94/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.94/1.54  --inst_passive_queues_freq              [25;2]
% 6.94/1.54  --inst_dismatching                      true
% 6.94/1.54  --inst_eager_unprocessed_to_passive     true
% 6.94/1.54  --inst_prop_sim_given                   true
% 6.94/1.54  --inst_prop_sim_new                     false
% 6.94/1.54  --inst_subs_new                         false
% 6.94/1.54  --inst_eq_res_simp                      false
% 6.94/1.54  --inst_subs_given                       false
% 6.94/1.54  --inst_orphan_elimination               true
% 6.94/1.54  --inst_learning_loop_flag               true
% 6.94/1.54  --inst_learning_start                   3000
% 6.94/1.54  --inst_learning_factor                  2
% 6.94/1.54  --inst_start_prop_sim_after_learn       3
% 6.94/1.54  --inst_sel_renew                        solver
% 6.94/1.54  --inst_lit_activity_flag                true
% 6.94/1.54  --inst_restr_to_given                   false
% 6.94/1.54  --inst_activity_threshold               500
% 6.94/1.54  --inst_out_proof                        true
% 6.94/1.54  
% 6.94/1.54  ------ Resolution Options
% 6.94/1.54  
% 6.94/1.54  --resolution_flag                       true
% 6.94/1.54  --res_lit_sel                           adaptive
% 6.94/1.54  --res_lit_sel_side                      none
% 6.94/1.54  --res_ordering                          kbo
% 6.94/1.54  --res_to_prop_solver                    active
% 6.94/1.54  --res_prop_simpl_new                    false
% 6.94/1.54  --res_prop_simpl_given                  true
% 6.94/1.54  --res_passive_queue_type                priority_queues
% 6.94/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.94/1.54  --res_passive_queues_freq               [15;5]
% 6.94/1.54  --res_forward_subs                      full
% 6.94/1.54  --res_backward_subs                     full
% 6.94/1.54  --res_forward_subs_resolution           true
% 6.94/1.54  --res_backward_subs_resolution          true
% 6.94/1.54  --res_orphan_elimination                true
% 6.94/1.54  --res_time_limit                        2.
% 6.94/1.54  --res_out_proof                         true
% 6.94/1.54  
% 6.94/1.54  ------ Superposition Options
% 6.94/1.54  
% 6.94/1.54  --superposition_flag                    true
% 6.94/1.54  --sup_passive_queue_type                priority_queues
% 6.94/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.94/1.54  --sup_passive_queues_freq               [8;1;4]
% 6.94/1.54  --demod_completeness_check              fast
% 6.94/1.54  --demod_use_ground                      true
% 6.94/1.54  --sup_to_prop_solver                    passive
% 6.94/1.54  --sup_prop_simpl_new                    true
% 6.94/1.54  --sup_prop_simpl_given                  true
% 6.94/1.54  --sup_fun_splitting                     false
% 6.94/1.54  --sup_smt_interval                      50000
% 6.94/1.54  
% 6.94/1.54  ------ Superposition Simplification Setup
% 6.94/1.54  
% 6.94/1.54  --sup_indices_passive                   []
% 6.94/1.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.94/1.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.94/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.94/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 6.94/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.94/1.54  --sup_full_bw                           [BwDemod]
% 6.94/1.54  --sup_immed_triv                        [TrivRules]
% 6.94/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.94/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.94/1.54  --sup_immed_bw_main                     []
% 6.94/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.94/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 6.94/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.94/1.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.94/1.54  
% 6.94/1.54  ------ Combination Options
% 6.94/1.54  
% 6.94/1.54  --comb_res_mult                         3
% 6.94/1.54  --comb_sup_mult                         2
% 6.94/1.54  --comb_inst_mult                        10
% 6.94/1.54  
% 6.94/1.54  ------ Debug Options
% 6.94/1.54  
% 6.94/1.54  --dbg_backtrace                         false
% 6.94/1.54  --dbg_dump_prop_clauses                 false
% 6.94/1.54  --dbg_dump_prop_clauses_file            -
% 6.94/1.54  --dbg_out_stat                          false
% 6.94/1.54  ------ Parsing...
% 6.94/1.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.94/1.54  
% 6.94/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 6.94/1.54  
% 6.94/1.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.94/1.54  
% 6.94/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.94/1.54  ------ Proving...
% 6.94/1.54  ------ Problem Properties 
% 6.94/1.54  
% 6.94/1.54  
% 6.94/1.54  clauses                                 23
% 6.94/1.54  conjectures                             5
% 6.94/1.54  EPR                                     5
% 6.94/1.54  Horn                                    15
% 6.94/1.54  unary                                   12
% 6.94/1.54  binary                                  9
% 6.94/1.54  lits                                    44
% 6.94/1.54  lits eq                                 11
% 6.94/1.54  fd_pure                                 0
% 6.94/1.54  fd_pseudo                               0
% 6.94/1.54  fd_cond                                 0
% 6.94/1.54  fd_pseudo_cond                          1
% 6.94/1.54  AC symbols                              0
% 6.94/1.54  
% 6.94/1.54  ------ Schedule dynamic 5 is on 
% 6.94/1.54  
% 6.94/1.54  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.94/1.54  
% 6.94/1.54  
% 6.94/1.54  ------ 
% 6.94/1.54  Current options:
% 6.94/1.54  ------ 
% 6.94/1.54  
% 6.94/1.54  ------ Input Options
% 6.94/1.54  
% 6.94/1.54  --out_options                           all
% 6.94/1.54  --tptp_safe_out                         true
% 6.94/1.54  --problem_path                          ""
% 6.94/1.54  --include_path                          ""
% 6.94/1.54  --clausifier                            res/vclausify_rel
% 6.94/1.54  --clausifier_options                    --mode clausify
% 6.94/1.54  --stdin                                 false
% 6.94/1.54  --stats_out                             all
% 6.94/1.54  
% 6.94/1.54  ------ General Options
% 6.94/1.54  
% 6.94/1.54  --fof                                   false
% 6.94/1.54  --time_out_real                         305.
% 6.94/1.54  --time_out_virtual                      -1.
% 6.94/1.54  --symbol_type_check                     false
% 6.94/1.54  --clausify_out                          false
% 6.94/1.54  --sig_cnt_out                           false
% 6.94/1.54  --trig_cnt_out                          false
% 6.94/1.54  --trig_cnt_out_tolerance                1.
% 6.94/1.54  --trig_cnt_out_sk_spl                   false
% 6.94/1.54  --abstr_cl_out                          false
% 6.94/1.54  
% 6.94/1.54  ------ Global Options
% 6.94/1.54  
% 6.94/1.54  --schedule                              default
% 6.94/1.54  --add_important_lit                     false
% 6.94/1.54  --prop_solver_per_cl                    1000
% 6.94/1.54  --min_unsat_core                        false
% 6.94/1.54  --soft_assumptions                      false
% 6.94/1.54  --soft_lemma_size                       3
% 6.94/1.54  --prop_impl_unit_size                   0
% 6.94/1.54  --prop_impl_unit                        []
% 6.94/1.54  --share_sel_clauses                     true
% 6.94/1.54  --reset_solvers                         false
% 6.94/1.54  --bc_imp_inh                            [conj_cone]
% 6.94/1.54  --conj_cone_tolerance                   3.
% 6.94/1.54  --extra_neg_conj                        none
% 6.94/1.54  --large_theory_mode                     true
% 6.94/1.54  --prolific_symb_bound                   200
% 6.94/1.54  --lt_threshold                          2000
% 6.94/1.54  --clause_weak_htbl                      true
% 6.94/1.54  --gc_record_bc_elim                     false
% 6.94/1.54  
% 6.94/1.54  ------ Preprocessing Options
% 6.94/1.54  
% 6.94/1.54  --preprocessing_flag                    true
% 6.94/1.54  --time_out_prep_mult                    0.1
% 6.94/1.54  --splitting_mode                        input
% 6.94/1.54  --splitting_grd                         true
% 6.94/1.54  --splitting_cvd                         false
% 6.94/1.54  --splitting_cvd_svl                     false
% 6.94/1.54  --splitting_nvd                         32
% 6.94/1.54  --sub_typing                            true
% 6.94/1.54  --prep_gs_sim                           true
% 6.94/1.54  --prep_unflatten                        true
% 6.94/1.54  --prep_res_sim                          true
% 6.94/1.54  --prep_upred                            true
% 6.94/1.54  --prep_sem_filter                       exhaustive
% 6.94/1.54  --prep_sem_filter_out                   false
% 6.94/1.54  --pred_elim                             true
% 6.94/1.54  --res_sim_input                         true
% 6.94/1.54  --eq_ax_congr_red                       true
% 6.94/1.54  --pure_diseq_elim                       true
% 6.94/1.54  --brand_transform                       false
% 6.94/1.54  --non_eq_to_eq                          false
% 6.94/1.54  --prep_def_merge                        true
% 6.94/1.54  --prep_def_merge_prop_impl              false
% 6.94/1.54  --prep_def_merge_mbd                    true
% 6.94/1.54  --prep_def_merge_tr_red                 false
% 6.94/1.54  --prep_def_merge_tr_cl                  false
% 6.94/1.54  --smt_preprocessing                     true
% 6.94/1.54  --smt_ac_axioms                         fast
% 6.94/1.54  --preprocessed_out                      false
% 6.94/1.54  --preprocessed_stats                    false
% 6.94/1.54  
% 6.94/1.54  ------ Abstraction refinement Options
% 6.94/1.54  
% 6.94/1.54  --abstr_ref                             []
% 6.94/1.54  --abstr_ref_prep                        false
% 6.94/1.54  --abstr_ref_until_sat                   false
% 6.94/1.54  --abstr_ref_sig_restrict                funpre
% 6.94/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 6.94/1.54  --abstr_ref_under                       []
% 6.94/1.54  
% 6.94/1.54  ------ SAT Options
% 6.94/1.54  
% 6.94/1.54  --sat_mode                              false
% 6.94/1.54  --sat_fm_restart_options                ""
% 6.94/1.54  --sat_gr_def                            false
% 6.94/1.54  --sat_epr_types                         true
% 6.94/1.54  --sat_non_cyclic_types                  false
% 6.94/1.54  --sat_finite_models                     false
% 6.94/1.54  --sat_fm_lemmas                         false
% 6.94/1.54  --sat_fm_prep                           false
% 6.94/1.54  --sat_fm_uc_incr                        true
% 6.94/1.54  --sat_out_model                         small
% 6.94/1.54  --sat_out_clauses                       false
% 6.94/1.54  
% 6.94/1.54  ------ QBF Options
% 6.94/1.54  
% 6.94/1.54  --qbf_mode                              false
% 6.94/1.54  --qbf_elim_univ                         false
% 6.94/1.54  --qbf_dom_inst                          none
% 6.94/1.54  --qbf_dom_pre_inst                      false
% 6.94/1.54  --qbf_sk_in                             false
% 6.94/1.54  --qbf_pred_elim                         true
% 6.94/1.54  --qbf_split                             512
% 6.94/1.54  
% 6.94/1.54  ------ BMC1 Options
% 6.94/1.54  
% 6.94/1.54  --bmc1_incremental                      false
% 6.94/1.54  --bmc1_axioms                           reachable_all
% 6.94/1.54  --bmc1_min_bound                        0
% 6.94/1.54  --bmc1_max_bound                        -1
% 6.94/1.54  --bmc1_max_bound_default                -1
% 6.94/1.54  --bmc1_symbol_reachability              true
% 6.94/1.54  --bmc1_property_lemmas                  false
% 6.94/1.54  --bmc1_k_induction                      false
% 6.94/1.54  --bmc1_non_equiv_states                 false
% 6.94/1.54  --bmc1_deadlock                         false
% 6.94/1.54  --bmc1_ucm                              false
% 6.94/1.54  --bmc1_add_unsat_core                   none
% 6.94/1.54  --bmc1_unsat_core_children              false
% 6.94/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 6.94/1.54  --bmc1_out_stat                         full
% 6.94/1.54  --bmc1_ground_init                      false
% 6.94/1.54  --bmc1_pre_inst_next_state              false
% 6.94/1.54  --bmc1_pre_inst_state                   false
% 6.94/1.54  --bmc1_pre_inst_reach_state             false
% 6.94/1.54  --bmc1_out_unsat_core                   false
% 6.94/1.54  --bmc1_aig_witness_out                  false
% 6.94/1.54  --bmc1_verbose                          false
% 6.94/1.54  --bmc1_dump_clauses_tptp                false
% 6.94/1.54  --bmc1_dump_unsat_core_tptp             false
% 6.94/1.54  --bmc1_dump_file                        -
% 6.94/1.54  --bmc1_ucm_expand_uc_limit              128
% 6.94/1.54  --bmc1_ucm_n_expand_iterations          6
% 6.94/1.54  --bmc1_ucm_extend_mode                  1
% 6.94/1.54  --bmc1_ucm_init_mode                    2
% 6.94/1.54  --bmc1_ucm_cone_mode                    none
% 6.94/1.54  --bmc1_ucm_reduced_relation_type        0
% 6.94/1.54  --bmc1_ucm_relax_model                  4
% 6.94/1.54  --bmc1_ucm_full_tr_after_sat            true
% 6.94/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 6.94/1.54  --bmc1_ucm_layered_model                none
% 6.94/1.54  --bmc1_ucm_max_lemma_size               10
% 6.94/1.54  
% 6.94/1.54  ------ AIG Options
% 6.94/1.54  
% 6.94/1.54  --aig_mode                              false
% 6.94/1.54  
% 6.94/1.54  ------ Instantiation Options
% 6.94/1.54  
% 6.94/1.54  --instantiation_flag                    true
% 6.94/1.54  --inst_sos_flag                         false
% 6.94/1.54  --inst_sos_phase                        true
% 6.94/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.94/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.94/1.54  --inst_lit_sel_side                     none
% 6.94/1.54  --inst_solver_per_active                1400
% 6.94/1.54  --inst_solver_calls_frac                1.
% 6.94/1.54  --inst_passive_queue_type               priority_queues
% 6.94/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.94/1.54  --inst_passive_queues_freq              [25;2]
% 6.94/1.54  --inst_dismatching                      true
% 6.94/1.54  --inst_eager_unprocessed_to_passive     true
% 6.94/1.54  --inst_prop_sim_given                   true
% 6.94/1.54  --inst_prop_sim_new                     false
% 6.94/1.54  --inst_subs_new                         false
% 6.94/1.54  --inst_eq_res_simp                      false
% 6.94/1.54  --inst_subs_given                       false
% 6.94/1.54  --inst_orphan_elimination               true
% 6.94/1.54  --inst_learning_loop_flag               true
% 6.94/1.54  --inst_learning_start                   3000
% 6.94/1.54  --inst_learning_factor                  2
% 6.94/1.54  --inst_start_prop_sim_after_learn       3
% 6.94/1.54  --inst_sel_renew                        solver
% 6.94/1.54  --inst_lit_activity_flag                true
% 6.94/1.54  --inst_restr_to_given                   false
% 6.94/1.54  --inst_activity_threshold               500
% 6.94/1.54  --inst_out_proof                        true
% 6.94/1.54  
% 6.94/1.54  ------ Resolution Options
% 6.94/1.54  
% 6.94/1.54  --resolution_flag                       false
% 6.94/1.54  --res_lit_sel                           adaptive
% 6.94/1.54  --res_lit_sel_side                      none
% 6.94/1.54  --res_ordering                          kbo
% 6.94/1.54  --res_to_prop_solver                    active
% 6.94/1.54  --res_prop_simpl_new                    false
% 6.94/1.54  --res_prop_simpl_given                  true
% 6.94/1.54  --res_passive_queue_type                priority_queues
% 6.94/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.94/1.54  --res_passive_queues_freq               [15;5]
% 6.94/1.54  --res_forward_subs                      full
% 6.94/1.54  --res_backward_subs                     full
% 6.94/1.54  --res_forward_subs_resolution           true
% 6.94/1.54  --res_backward_subs_resolution          true
% 6.94/1.54  --res_orphan_elimination                true
% 6.94/1.54  --res_time_limit                        2.
% 6.94/1.54  --res_out_proof                         true
% 6.94/1.54  
% 6.94/1.54  ------ Superposition Options
% 6.94/1.54  
% 6.94/1.54  --superposition_flag                    true
% 6.94/1.54  --sup_passive_queue_type                priority_queues
% 6.94/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.94/1.54  --sup_passive_queues_freq               [8;1;4]
% 6.94/1.54  --demod_completeness_check              fast
% 6.94/1.54  --demod_use_ground                      true
% 6.94/1.54  --sup_to_prop_solver                    passive
% 6.94/1.54  --sup_prop_simpl_new                    true
% 6.94/1.54  --sup_prop_simpl_given                  true
% 6.94/1.54  --sup_fun_splitting                     false
% 6.94/1.54  --sup_smt_interval                      50000
% 6.94/1.54  
% 6.94/1.54  ------ Superposition Simplification Setup
% 6.94/1.54  
% 6.94/1.54  --sup_indices_passive                   []
% 6.94/1.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.94/1.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.94/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.94/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 6.94/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.94/1.54  --sup_full_bw                           [BwDemod]
% 6.94/1.54  --sup_immed_triv                        [TrivRules]
% 6.94/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.94/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.94/1.54  --sup_immed_bw_main                     []
% 6.94/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.94/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 6.94/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.94/1.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.94/1.54  
% 6.94/1.54  ------ Combination Options
% 6.94/1.54  
% 6.94/1.54  --comb_res_mult                         3
% 6.94/1.54  --comb_sup_mult                         2
% 6.94/1.54  --comb_inst_mult                        10
% 6.94/1.54  
% 6.94/1.54  ------ Debug Options
% 6.94/1.54  
% 6.94/1.54  --dbg_backtrace                         false
% 6.94/1.54  --dbg_dump_prop_clauses                 false
% 6.94/1.54  --dbg_dump_prop_clauses_file            -
% 6.94/1.54  --dbg_out_stat                          false
% 6.94/1.54  
% 6.94/1.54  
% 6.94/1.54  
% 6.94/1.54  
% 6.94/1.54  ------ Proving...
% 6.94/1.54  
% 6.94/1.54  
% 6.94/1.54  % SZS status Theorem for theBenchmark.p
% 6.94/1.54  
% 6.94/1.54  % SZS output start CNFRefutation for theBenchmark.p
% 6.94/1.54  
% 6.94/1.54  fof(f6,conjecture,(
% 6.94/1.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 6.94/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.54  
% 6.94/1.54  fof(f7,negated_conjecture,(
% 6.94/1.54    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 6.94/1.54    inference(negated_conjecture,[],[f6])).
% 6.94/1.54  
% 6.94/1.54  fof(f11,plain,(
% 6.94/1.54    ? [X0] : ((~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 6.94/1.54    inference(ennf_transformation,[],[f7])).
% 6.94/1.54  
% 6.94/1.54  fof(f12,plain,(
% 6.94/1.54    ? [X0] : (~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 6.94/1.54    inference(flattening,[],[f11])).
% 6.94/1.54  
% 6.94/1.54  fof(f23,plain,(
% 6.94/1.54    ( ! [X0] : (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k5_relat_1(X0,sK5) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(sK5) & v1_relat_1(sK5))) )),
% 6.94/1.54    introduced(choice_axiom,[])).
% 6.94/1.54  
% 6.94/1.54  fof(f22,plain,(
% 6.94/1.54    ? [X0] : (~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v2_funct_1(sK4) & ? [X1] : (k5_relat_1(sK4,X1) = k6_relat_1(k1_relat_1(sK4)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 6.94/1.54    introduced(choice_axiom,[])).
% 6.94/1.54  
% 6.94/1.54  fof(f24,plain,(
% 6.94/1.54    ~v2_funct_1(sK4) & (k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4)) & v1_funct_1(sK5) & v1_relat_1(sK5)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 6.94/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f12,f23,f22])).
% 6.94/1.54  
% 6.94/1.54  fof(f45,plain,(
% 6.94/1.54    v1_relat_1(sK4)),
% 6.94/1.54    inference(cnf_transformation,[],[f24])).
% 6.94/1.54  
% 6.94/1.54  fof(f47,plain,(
% 6.94/1.54    v1_relat_1(sK5)),
% 6.94/1.54    inference(cnf_transformation,[],[f24])).
% 6.94/1.54  
% 6.94/1.54  fof(f13,plain,(
% 6.94/1.54    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.94/1.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 6.94/1.54  
% 6.94/1.54  fof(f17,plain,(
% 6.94/1.54    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))) & (! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~sP0(X0)))),
% 6.94/1.54    inference(nnf_transformation,[],[f13])).
% 6.94/1.54  
% 6.94/1.54  fof(f18,plain,(
% 6.94/1.54    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))) & (! [X3] : (! [X4] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~sP0(X0)))),
% 6.94/1.54    inference(rectify,[],[f17])).
% 6.94/1.54  
% 6.94/1.54  fof(f20,plain,(
% 6.94/1.54    ( ! [X1] : (! [X0] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) => (sK3(X0) != X1 & k5_relat_1(X1,X0) = k5_relat_1(sK3(X0),X0) & k1_relat_1(X1) = k1_relat_1(sK3(X0)) & r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))) )),
% 6.94/1.54    introduced(choice_axiom,[])).
% 6.94/1.54  
% 6.94/1.54  fof(f19,plain,(
% 6.94/1.54    ! [X0] : (? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (sK2(X0) != X2 & k5_relat_1(X2,X0) = k5_relat_1(sK2(X0),X0) & k1_relat_1(X2) = k1_relat_1(sK2(X0)) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0))))),
% 6.94/1.54    introduced(choice_axiom,[])).
% 6.94/1.54  
% 6.94/1.54  fof(f21,plain,(
% 6.94/1.54    ! [X0] : ((sP0(X0) | ((sK2(X0) != sK3(X0) & k5_relat_1(sK2(X0),X0) = k5_relat_1(sK3(X0),X0) & k1_relat_1(sK2(X0)) = k1_relat_1(sK3(X0)) & r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0)) & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))) & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0)))) & (! [X3] : (! [X4] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~sP0(X0)))),
% 6.94/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f20,f19])).
% 6.94/1.54  
% 6.94/1.54  fof(f37,plain,(
% 6.94/1.54    ( ! [X0] : (sP0(X0) | v1_relat_1(sK3(X0))) )),
% 6.94/1.54    inference(cnf_transformation,[],[f21])).
% 6.94/1.54  
% 6.94/1.54  fof(f1,axiom,(
% 6.94/1.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 6.94/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.54  
% 6.94/1.54  fof(f8,plain,(
% 6.94/1.54    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.94/1.54    inference(ennf_transformation,[],[f1])).
% 6.94/1.54  
% 6.94/1.54  fof(f25,plain,(
% 6.94/1.54    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 6.94/1.54    inference(cnf_transformation,[],[f8])).
% 6.94/1.54  
% 6.94/1.54  fof(f49,plain,(
% 6.94/1.54    k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4))),
% 6.94/1.54    inference(cnf_transformation,[],[f24])).
% 6.94/1.54  
% 6.94/1.54  fof(f14,plain,(
% 6.94/1.54    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 6.94/1.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 6.94/1.54  
% 6.94/1.54  fof(f16,plain,(
% 6.94/1.54    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 6.94/1.54    inference(nnf_transformation,[],[f14])).
% 6.94/1.54  
% 6.94/1.54  fof(f33,plain,(
% 6.94/1.54    ( ! [X0] : (v2_funct_1(X0) | ~sP0(X0) | ~sP1(X0)) )),
% 6.94/1.54    inference(cnf_transformation,[],[f16])).
% 6.94/1.54  
% 6.94/1.54  fof(f50,plain,(
% 6.94/1.54    ~v2_funct_1(sK4)),
% 6.94/1.54    inference(cnf_transformation,[],[f24])).
% 6.94/1.54  
% 6.94/1.54  fof(f46,plain,(
% 6.94/1.54    v1_funct_1(sK4)),
% 6.94/1.54    inference(cnf_transformation,[],[f24])).
% 6.94/1.54  
% 6.94/1.54  fof(f5,axiom,(
% 6.94/1.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) => X1 = X2)))))),
% 6.94/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.54  
% 6.94/1.54  fof(f9,plain,(
% 6.94/1.54    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : ((X1 = X2 | (k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.94/1.54    inference(ennf_transformation,[],[f5])).
% 6.94/1.54  
% 6.94/1.54  fof(f10,plain,(
% 6.94/1.54    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.94/1.54    inference(flattening,[],[f9])).
% 6.94/1.54  
% 6.94/1.54  fof(f15,plain,(
% 6.94/1.54    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.94/1.54    inference(definition_folding,[],[f10,f14,f13])).
% 6.94/1.54  
% 6.94/1.54  fof(f44,plain,(
% 6.94/1.54    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.94/1.54    inference(cnf_transformation,[],[f15])).
% 6.94/1.54  
% 6.94/1.54  fof(f42,plain,(
% 6.94/1.54    ( ! [X0] : (sP0(X0) | k5_relat_1(sK2(X0),X0) = k5_relat_1(sK3(X0),X0)) )),
% 6.94/1.54    inference(cnf_transformation,[],[f21])).
% 6.94/1.54  
% 6.94/1.54  fof(f35,plain,(
% 6.94/1.54    ( ! [X0] : (sP0(X0) | v1_relat_1(sK2(X0))) )),
% 6.94/1.54    inference(cnf_transformation,[],[f21])).
% 6.94/1.54  
% 6.94/1.54  fof(f34,plain,(
% 6.94/1.54    ( ! [X4,X0,X3] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~sP0(X0)) )),
% 6.94/1.54    inference(cnf_transformation,[],[f21])).
% 6.94/1.54  
% 6.94/1.54  fof(f4,axiom,(
% 6.94/1.54    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 6.94/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.54  
% 6.94/1.54  fof(f31,plain,(
% 6.94/1.54    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 6.94/1.54    inference(cnf_transformation,[],[f4])).
% 6.94/1.54  
% 6.94/1.54  fof(f32,plain,(
% 6.94/1.54    ( ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~sP1(X0)) )),
% 6.94/1.54    inference(cnf_transformation,[],[f16])).
% 6.94/1.54  
% 6.94/1.54  fof(f30,plain,(
% 6.94/1.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 6.94/1.54    inference(cnf_transformation,[],[f4])).
% 6.94/1.54  
% 6.94/1.54  fof(f3,axiom,(
% 6.94/1.54    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 6.94/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.54  
% 6.94/1.54  fof(f29,plain,(
% 6.94/1.54    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 6.94/1.54    inference(cnf_transformation,[],[f3])).
% 6.94/1.54  
% 6.94/1.54  fof(f2,axiom,(
% 6.94/1.54    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 6.94/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.94/1.54  
% 6.94/1.54  fof(f26,plain,(
% 6.94/1.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 6.94/1.54    inference(cnf_transformation,[],[f2])).
% 6.94/1.54  
% 6.94/1.54  fof(f43,plain,(
% 6.94/1.54    ( ! [X0] : (sP0(X0) | sK2(X0) != sK3(X0)) )),
% 6.94/1.54    inference(cnf_transformation,[],[f21])).
% 6.94/1.54  
% 6.94/1.54  fof(f41,plain,(
% 6.94/1.54    ( ! [X0] : (sP0(X0) | k1_relat_1(sK2(X0)) = k1_relat_1(sK3(X0))) )),
% 6.94/1.54    inference(cnf_transformation,[],[f21])).
% 6.94/1.54  
% 6.94/1.54  fof(f40,plain,(
% 6.94/1.54    ( ! [X0] : (sP0(X0) | r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))) )),
% 6.94/1.54    inference(cnf_transformation,[],[f21])).
% 6.94/1.54  
% 6.94/1.54  fof(f39,plain,(
% 6.94/1.54    ( ! [X0] : (sP0(X0) | r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))) )),
% 6.94/1.54    inference(cnf_transformation,[],[f21])).
% 6.94/1.54  
% 6.94/1.54  fof(f38,plain,(
% 6.94/1.54    ( ! [X0] : (sP0(X0) | v1_funct_1(sK3(X0))) )),
% 6.94/1.54    inference(cnf_transformation,[],[f21])).
% 6.94/1.54  
% 6.94/1.54  fof(f36,plain,(
% 6.94/1.54    ( ! [X0] : (sP0(X0) | v1_funct_1(sK2(X0))) )),
% 6.94/1.54    inference(cnf_transformation,[],[f21])).
% 6.94/1.54  
% 6.94/1.54  cnf(c_25,negated_conjecture,
% 6.94/1.54      ( v1_relat_1(sK4) ),
% 6.94/1.54      inference(cnf_transformation,[],[f45]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_1831,plain,
% 6.94/1.54      ( v1_relat_1(sK4) = iProver_top ),
% 6.94/1.54      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_23,negated_conjecture,
% 6.94/1.54      ( v1_relat_1(sK5) ),
% 6.94/1.54      inference(cnf_transformation,[],[f47]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_1833,plain,
% 6.94/1.54      ( v1_relat_1(sK5) = iProver_top ),
% 6.94/1.54      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_15,plain,
% 6.94/1.54      ( sP0(X0) | v1_relat_1(sK3(X0)) ),
% 6.94/1.54      inference(cnf_transformation,[],[f37]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_1838,plain,
% 6.94/1.54      ( sP0(X0) = iProver_top | v1_relat_1(sK3(X0)) = iProver_top ),
% 6.94/1.54      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_0,plain,
% 6.94/1.54      ( ~ v1_relat_1(X0)
% 6.94/1.54      | ~ v1_relat_1(X1)
% 6.94/1.54      | ~ v1_relat_1(X2)
% 6.94/1.54      | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
% 6.94/1.54      inference(cnf_transformation,[],[f25]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_1847,plain,
% 6.94/1.54      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 6.94/1.54      | v1_relat_1(X2) != iProver_top
% 6.94/1.54      | v1_relat_1(X0) != iProver_top
% 6.94/1.54      | v1_relat_1(X1) != iProver_top ),
% 6.94/1.54      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_3186,plain,
% 6.94/1.54      ( k5_relat_1(sK3(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(sK3(X0),X1),X2)
% 6.94/1.54      | sP0(X0) = iProver_top
% 6.94/1.54      | v1_relat_1(X2) != iProver_top
% 6.94/1.54      | v1_relat_1(X1) != iProver_top ),
% 6.94/1.54      inference(superposition,[status(thm)],[c_1838,c_1847]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_19682,plain,
% 6.94/1.54      ( k5_relat_1(k5_relat_1(sK3(X0),X1),sK5) = k5_relat_1(sK3(X0),k5_relat_1(X1,sK5))
% 6.94/1.54      | sP0(X0) = iProver_top
% 6.94/1.54      | v1_relat_1(X1) != iProver_top ),
% 6.94/1.54      inference(superposition,[status(thm)],[c_1833,c_3186]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_20430,plain,
% 6.94/1.54      ( k5_relat_1(k5_relat_1(sK3(X0),sK4),sK5) = k5_relat_1(sK3(X0),k5_relat_1(sK4,sK5))
% 6.94/1.54      | sP0(X0) = iProver_top ),
% 6.94/1.54      inference(superposition,[status(thm)],[c_1831,c_19682]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_21,negated_conjecture,
% 6.94/1.54      ( k5_relat_1(sK4,sK5) = k6_relat_1(k1_relat_1(sK4)) ),
% 6.94/1.54      inference(cnf_transformation,[],[f49]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_20433,plain,
% 6.94/1.54      ( k5_relat_1(k5_relat_1(sK3(X0),sK4),sK5) = k5_relat_1(sK3(X0),k6_relat_1(k1_relat_1(sK4)))
% 6.94/1.54      | sP0(X0) = iProver_top ),
% 6.94/1.54      inference(light_normalisation,[status(thm)],[c_20430,c_21]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_7,plain,
% 6.94/1.54      ( ~ sP1(X0) | ~ sP0(X0) | v2_funct_1(X0) ),
% 6.94/1.54      inference(cnf_transformation,[],[f33]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_20,negated_conjecture,
% 6.94/1.54      ( ~ v2_funct_1(sK4) ),
% 6.94/1.54      inference(cnf_transformation,[],[f50]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_278,plain,
% 6.94/1.54      ( ~ sP1(X0) | ~ sP0(X0) | sK4 != X0 ),
% 6.94/1.54      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_279,plain,
% 6.94/1.54      ( ~ sP1(sK4) | ~ sP0(sK4) ),
% 6.94/1.54      inference(unflattening,[status(thm)],[c_278]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_24,negated_conjecture,
% 6.94/1.54      ( v1_funct_1(sK4) ),
% 6.94/1.54      inference(cnf_transformation,[],[f46]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_19,plain,
% 6.94/1.54      ( sP1(X0) | ~ v1_funct_1(X0) | ~ v1_relat_1(X0) ),
% 6.94/1.54      inference(cnf_transformation,[],[f44]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_32,plain,
% 6.94/1.54      ( sP1(sK4) | ~ v1_funct_1(sK4) | ~ v1_relat_1(sK4) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_19]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_66,plain,
% 6.94/1.54      ( ~ sP1(sK4) | ~ sP0(sK4) | v2_funct_1(sK4) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_7]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_281,plain,
% 6.94/1.54      ( ~ sP0(sK4) ),
% 6.94/1.54      inference(global_propositional_subsumption,
% 6.94/1.54                [status(thm)],
% 6.94/1.54                [c_279,c_25,c_24,c_20,c_32,c_66]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_1830,plain,
% 6.94/1.54      ( sP0(sK4) != iProver_top ),
% 6.94/1.54      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_20474,plain,
% 6.94/1.54      ( k5_relat_1(k5_relat_1(sK3(sK4),sK4),sK5) = k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4))) ),
% 6.94/1.54      inference(superposition,[status(thm)],[c_20433,c_1830]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_10,plain,
% 6.94/1.54      ( sP0(X0) | k5_relat_1(sK3(X0),X0) = k5_relat_1(sK2(X0),X0) ),
% 6.94/1.54      inference(cnf_transformation,[],[f42]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_1843,plain,
% 6.94/1.54      ( k5_relat_1(sK3(X0),X0) = k5_relat_1(sK2(X0),X0)
% 6.94/1.54      | sP0(X0) = iProver_top ),
% 6.94/1.54      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_4285,plain,
% 6.94/1.54      ( k5_relat_1(sK2(sK4),sK4) = k5_relat_1(sK3(sK4),sK4) ),
% 6.94/1.54      inference(superposition,[status(thm)],[c_1843,c_1830]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_17,plain,
% 6.94/1.54      ( sP0(X0) | v1_relat_1(sK2(X0)) ),
% 6.94/1.54      inference(cnf_transformation,[],[f35]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_1836,plain,
% 6.94/1.54      ( sP0(X0) = iProver_top | v1_relat_1(sK2(X0)) = iProver_top ),
% 6.94/1.54      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2532,plain,
% 6.94/1.54      ( k5_relat_1(sK2(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(sK2(X0),X1),X2)
% 6.94/1.54      | sP0(X0) = iProver_top
% 6.94/1.54      | v1_relat_1(X2) != iProver_top
% 6.94/1.54      | v1_relat_1(X1) != iProver_top ),
% 6.94/1.54      inference(superposition,[status(thm)],[c_1836,c_1847]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_6727,plain,
% 6.94/1.54      ( k5_relat_1(k5_relat_1(sK2(X0),X1),sK5) = k5_relat_1(sK2(X0),k5_relat_1(X1,sK5))
% 6.94/1.54      | sP0(X0) = iProver_top
% 6.94/1.54      | v1_relat_1(X1) != iProver_top ),
% 6.94/1.54      inference(superposition,[status(thm)],[c_1833,c_2532]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_8996,plain,
% 6.94/1.54      ( k5_relat_1(k5_relat_1(sK2(X0),sK4),sK5) = k5_relat_1(sK2(X0),k5_relat_1(sK4,sK5))
% 6.94/1.54      | sP0(X0) = iProver_top ),
% 6.94/1.54      inference(superposition,[status(thm)],[c_1831,c_6727]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_8999,plain,
% 6.94/1.54      ( k5_relat_1(k5_relat_1(sK2(X0),sK4),sK5) = k5_relat_1(sK2(X0),k6_relat_1(k1_relat_1(sK4)))
% 6.94/1.54      | sP0(X0) = iProver_top ),
% 6.94/1.54      inference(light_normalisation,[status(thm)],[c_8996,c_21]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_9040,plain,
% 6.94/1.54      ( k5_relat_1(sK2(sK4),k6_relat_1(k1_relat_1(sK4))) = k5_relat_1(k5_relat_1(sK2(sK4),sK4),sK5) ),
% 6.94/1.54      inference(superposition,[status(thm)],[c_8999,c_1830]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_20475,plain,
% 6.94/1.54      ( k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4))) = k5_relat_1(sK2(sK4),k6_relat_1(k1_relat_1(sK4))) ),
% 6.94/1.54      inference(light_normalisation,
% 6.94/1.54                [status(thm)],
% 6.94/1.54                [c_20474,c_4285,c_9040]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_18,plain,
% 6.94/1.54      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 6.94/1.54      | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
% 6.94/1.54      | ~ sP0(X1)
% 6.94/1.54      | ~ v1_funct_1(X0)
% 6.94/1.54      | ~ v1_funct_1(X2)
% 6.94/1.54      | ~ v1_relat_1(X0)
% 6.94/1.54      | ~ v1_relat_1(X2)
% 6.94/1.54      | X0 = X2
% 6.94/1.54      | k5_relat_1(X0,X1) != k5_relat_1(X2,X1)
% 6.94/1.54      | k1_relat_1(X0) != k1_relat_1(X2) ),
% 6.94/1.54      inference(cnf_transformation,[],[f34]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2006,plain,
% 6.94/1.54      ( ~ r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X1))
% 6.94/1.54      | ~ r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X1))
% 6.94/1.54      | ~ sP0(X1)
% 6.94/1.54      | ~ v1_funct_1(sK3(X0))
% 6.94/1.54      | ~ v1_funct_1(sK2(X0))
% 6.94/1.54      | ~ v1_relat_1(sK3(X0))
% 6.94/1.54      | ~ v1_relat_1(sK2(X0))
% 6.94/1.54      | k5_relat_1(sK3(X0),X1) != k5_relat_1(sK2(X0),X1)
% 6.94/1.54      | sK3(X0) = sK2(X0)
% 6.94/1.54      | k1_relat_1(sK3(X0)) != k1_relat_1(sK2(X0)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_18]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2169,plain,
% 6.94/1.54      ( ~ r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(k6_relat_1(X1)))
% 6.94/1.54      | ~ r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(k6_relat_1(X1)))
% 6.94/1.54      | ~ sP0(k6_relat_1(X1))
% 6.94/1.54      | ~ v1_funct_1(sK3(X0))
% 6.94/1.54      | ~ v1_funct_1(sK2(X0))
% 6.94/1.54      | ~ v1_relat_1(sK3(X0))
% 6.94/1.54      | ~ v1_relat_1(sK2(X0))
% 6.94/1.54      | k5_relat_1(sK3(X0),k6_relat_1(X1)) != k5_relat_1(sK2(X0),k6_relat_1(X1))
% 6.94/1.54      | sK3(X0) = sK2(X0)
% 6.94/1.54      | k1_relat_1(sK3(X0)) != k1_relat_1(sK2(X0)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_2006]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_8330,plain,
% 6.94/1.54      ( ~ r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(k6_relat_1(k1_relat_1(X0))))
% 6.94/1.54      | ~ r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(k6_relat_1(k1_relat_1(X0))))
% 6.94/1.54      | ~ sP0(k6_relat_1(k1_relat_1(X0)))
% 6.94/1.54      | ~ v1_funct_1(sK3(X0))
% 6.94/1.54      | ~ v1_funct_1(sK2(X0))
% 6.94/1.54      | ~ v1_relat_1(sK3(X0))
% 6.94/1.54      | ~ v1_relat_1(sK2(X0))
% 6.94/1.54      | k5_relat_1(sK3(X0),k6_relat_1(k1_relat_1(X0))) != k5_relat_1(sK2(X0),k6_relat_1(k1_relat_1(X0)))
% 6.94/1.54      | sK3(X0) = sK2(X0)
% 6.94/1.54      | k1_relat_1(sK3(X0)) != k1_relat_1(sK2(X0)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_2169]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_8332,plain,
% 6.94/1.54      ( ~ r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(k6_relat_1(k1_relat_1(sK4))))
% 6.94/1.54      | ~ r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(k6_relat_1(k1_relat_1(sK4))))
% 6.94/1.54      | ~ sP0(k6_relat_1(k1_relat_1(sK4)))
% 6.94/1.54      | ~ v1_funct_1(sK3(sK4))
% 6.94/1.54      | ~ v1_funct_1(sK2(sK4))
% 6.94/1.54      | ~ v1_relat_1(sK3(sK4))
% 6.94/1.54      | ~ v1_relat_1(sK2(sK4))
% 6.94/1.54      | k5_relat_1(sK3(sK4),k6_relat_1(k1_relat_1(sK4))) != k5_relat_1(sK2(sK4),k6_relat_1(k1_relat_1(sK4)))
% 6.94/1.54      | sK3(sK4) = sK2(sK4)
% 6.94/1.54      | k1_relat_1(sK3(sK4)) != k1_relat_1(sK2(sK4)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_8330]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_1482,plain,
% 6.94/1.54      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.94/1.54      theory(equality) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2001,plain,
% 6.94/1.54      ( r1_tarski(X0,X1)
% 6.94/1.54      | ~ r1_tarski(k2_relat_1(sK2(X2)),k1_relat_1(X2))
% 6.94/1.54      | X1 != k1_relat_1(X2)
% 6.94/1.54      | X0 != k2_relat_1(sK2(X2)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_1482]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2099,plain,
% 6.94/1.54      ( r1_tarski(X0,k1_relat_1(X1))
% 6.94/1.54      | ~ r1_tarski(k2_relat_1(sK2(X2)),k1_relat_1(X2))
% 6.94/1.54      | X0 != k2_relat_1(sK2(X2))
% 6.94/1.54      | k1_relat_1(X1) != k1_relat_1(X2) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_2001]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2347,plain,
% 6.94/1.54      ( ~ r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))
% 6.94/1.54      | r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X1))
% 6.94/1.54      | k1_relat_1(X1) != k1_relat_1(X0)
% 6.94/1.54      | k2_relat_1(sK2(X0)) != k2_relat_1(sK2(X0)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_2099]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_3264,plain,
% 6.94/1.54      ( ~ r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))
% 6.94/1.54      | r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(k6_relat_1(X1)))
% 6.94/1.54      | k1_relat_1(k6_relat_1(X1)) != k1_relat_1(X0)
% 6.94/1.54      | k2_relat_1(sK2(X0)) != k2_relat_1(sK2(X0)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_2347]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_4081,plain,
% 6.94/1.54      ( ~ r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0))
% 6.94/1.54      | r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(k6_relat_1(k1_relat_1(X0))))
% 6.94/1.54      | k1_relat_1(k6_relat_1(k1_relat_1(X0))) != k1_relat_1(X0)
% 6.94/1.54      | k2_relat_1(sK2(X0)) != k2_relat_1(sK2(X0)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_3264]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_4083,plain,
% 6.94/1.54      ( r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(k6_relat_1(k1_relat_1(sK4))))
% 6.94/1.54      | ~ r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(sK4))
% 6.94/1.54      | k1_relat_1(k6_relat_1(k1_relat_1(sK4))) != k1_relat_1(sK4)
% 6.94/1.54      | k2_relat_1(sK2(sK4)) != k2_relat_1(sK2(sK4)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_4081]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_1996,plain,
% 6.94/1.54      ( r1_tarski(X0,X1)
% 6.94/1.54      | ~ r1_tarski(k2_relat_1(sK3(X2)),k1_relat_1(X2))
% 6.94/1.54      | X1 != k1_relat_1(X2)
% 6.94/1.54      | X0 != k2_relat_1(sK3(X2)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_1482]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2066,plain,
% 6.94/1.54      ( r1_tarski(X0,k1_relat_1(k6_relat_1(k1_relat_1(X1))))
% 6.94/1.54      | ~ r1_tarski(k2_relat_1(sK3(X1)),k1_relat_1(X1))
% 6.94/1.54      | X0 != k2_relat_1(sK3(X1))
% 6.94/1.54      | k1_relat_1(k6_relat_1(k1_relat_1(X1))) != k1_relat_1(X1) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_1996]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2621,plain,
% 6.94/1.54      ( ~ r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0))
% 6.94/1.54      | r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(k6_relat_1(k1_relat_1(X0))))
% 6.94/1.54      | k1_relat_1(k6_relat_1(k1_relat_1(X0))) != k1_relat_1(X0)
% 6.94/1.54      | k2_relat_1(sK3(X0)) != k2_relat_1(sK3(X0)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_2066]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2624,plain,
% 6.94/1.54      ( r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(k6_relat_1(k1_relat_1(sK4))))
% 6.94/1.54      | ~ r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(sK4))
% 6.94/1.54      | k1_relat_1(k6_relat_1(k1_relat_1(sK4))) != k1_relat_1(sK4)
% 6.94/1.54      | k2_relat_1(sK3(sK4)) != k2_relat_1(sK3(sK4)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_2621]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_1473,plain,( X0 = X0 ),theory(equality) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2348,plain,
% 6.94/1.54      ( k2_relat_1(sK2(X0)) = k2_relat_1(sK2(X0)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_1473]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2351,plain,
% 6.94/1.54      ( k2_relat_1(sK2(sK4)) = k2_relat_1(sK2(sK4)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_2348]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2252,plain,
% 6.94/1.54      ( k2_relat_1(sK3(X0)) = k2_relat_1(sK3(X0)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_1473]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2257,plain,
% 6.94/1.54      ( k2_relat_1(sK3(sK4)) = k2_relat_1(sK3(sK4)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_2252]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_5,plain,
% 6.94/1.54      ( v2_funct_1(k6_relat_1(X0)) ),
% 6.94/1.54      inference(cnf_transformation,[],[f31]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_8,plain,
% 6.94/1.54      ( ~ sP1(X0) | sP0(X0) | ~ v2_funct_1(X0) ),
% 6.94/1.54      inference(cnf_transformation,[],[f32]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_261,plain,
% 6.94/1.54      ( ~ sP1(X0) | sP0(X0) | k6_relat_1(X1) != X0 ),
% 6.94/1.54      inference(resolution_lifted,[status(thm)],[c_5,c_8]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_262,plain,
% 6.94/1.54      ( ~ sP1(k6_relat_1(X0)) | sP0(k6_relat_1(X0)) ),
% 6.94/1.54      inference(unflattening,[status(thm)],[c_261]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_295,plain,
% 6.94/1.54      ( sP0(k6_relat_1(X0))
% 6.94/1.54      | ~ v1_funct_1(X1)
% 6.94/1.54      | ~ v1_relat_1(X1)
% 6.94/1.54      | k6_relat_1(X0) != X1 ),
% 6.94/1.54      inference(resolution_lifted,[status(thm)],[c_19,c_262]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_296,plain,
% 6.94/1.54      ( sP0(k6_relat_1(X0))
% 6.94/1.54      | ~ v1_funct_1(k6_relat_1(X0))
% 6.94/1.54      | ~ v1_relat_1(k6_relat_1(X0)) ),
% 6.94/1.54      inference(unflattening,[status(thm)],[c_295]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_6,plain,
% 6.94/1.54      ( v1_relat_1(k6_relat_1(X0)) ),
% 6.94/1.54      inference(cnf_transformation,[],[f30]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_3,plain,
% 6.94/1.54      ( v1_funct_1(k6_relat_1(X0)) ),
% 6.94/1.54      inference(cnf_transformation,[],[f29]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_300,plain,
% 6.94/1.54      ( sP0(k6_relat_1(X0)) ),
% 6.94/1.54      inference(global_propositional_subsumption,
% 6.94/1.54                [status(thm)],
% 6.94/1.54                [c_296,c_6,c_3]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2124,plain,
% 6.94/1.54      ( sP0(k6_relat_1(k1_relat_1(sK4))) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_300]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2,plain,
% 6.94/1.54      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 6.94/1.54      inference(cnf_transformation,[],[f26]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2067,plain,
% 6.94/1.54      ( k1_relat_1(k6_relat_1(k1_relat_1(X0))) = k1_relat_1(X0) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_2]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_2072,plain,
% 6.94/1.54      ( k1_relat_1(k6_relat_1(k1_relat_1(sK4))) = k1_relat_1(sK4) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_2067]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_9,plain,
% 6.94/1.54      ( sP0(X0) | sK3(X0) != sK2(X0) ),
% 6.94/1.54      inference(cnf_transformation,[],[f43]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_62,plain,
% 6.94/1.54      ( sP0(sK4) | sK3(sK4) != sK2(sK4) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_9]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_11,plain,
% 6.94/1.54      ( sP0(X0) | k1_relat_1(sK3(X0)) = k1_relat_1(sK2(X0)) ),
% 6.94/1.54      inference(cnf_transformation,[],[f41]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_56,plain,
% 6.94/1.54      ( sP0(sK4) | k1_relat_1(sK3(sK4)) = k1_relat_1(sK2(sK4)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_11]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_12,plain,
% 6.94/1.54      ( r1_tarski(k2_relat_1(sK3(X0)),k1_relat_1(X0)) | sP0(X0) ),
% 6.94/1.54      inference(cnf_transformation,[],[f40]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_53,plain,
% 6.94/1.54      ( r1_tarski(k2_relat_1(sK3(sK4)),k1_relat_1(sK4)) | sP0(sK4) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_12]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_13,plain,
% 6.94/1.54      ( r1_tarski(k2_relat_1(sK2(X0)),k1_relat_1(X0)) | sP0(X0) ),
% 6.94/1.54      inference(cnf_transformation,[],[f39]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_50,plain,
% 6.94/1.54      ( r1_tarski(k2_relat_1(sK2(sK4)),k1_relat_1(sK4)) | sP0(sK4) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_13]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_14,plain,
% 6.94/1.54      ( sP0(X0) | v1_funct_1(sK3(X0)) ),
% 6.94/1.54      inference(cnf_transformation,[],[f38]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_47,plain,
% 6.94/1.54      ( sP0(sK4) | v1_funct_1(sK3(sK4)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_14]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_44,plain,
% 6.94/1.54      ( sP0(sK4) | v1_relat_1(sK3(sK4)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_15]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_16,plain,
% 6.94/1.54      ( sP0(X0) | v1_funct_1(sK2(X0)) ),
% 6.94/1.54      inference(cnf_transformation,[],[f36]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_41,plain,
% 6.94/1.54      ( sP0(sK4) | v1_funct_1(sK2(sK4)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_16]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(c_38,plain,
% 6.94/1.54      ( sP0(sK4) | v1_relat_1(sK2(sK4)) ),
% 6.94/1.54      inference(instantiation,[status(thm)],[c_17]) ).
% 6.94/1.54  
% 6.94/1.54  cnf(contradiction,plain,
% 6.94/1.54      ( $false ),
% 6.94/1.54      inference(minisat,
% 6.94/1.54                [status(thm)],
% 6.94/1.54                [c_20475,c_8332,c_4083,c_2624,c_2351,c_2257,c_2124,
% 6.94/1.54                 c_2072,c_66,c_62,c_56,c_53,c_50,c_47,c_44,c_41,c_38,
% 6.94/1.54                 c_32,c_20,c_24,c_25]) ).
% 6.94/1.54  
% 6.94/1.54  
% 6.94/1.54  % SZS output end CNFRefutation for theBenchmark.p
% 6.94/1.54  
% 6.94/1.54  ------                               Statistics
% 6.94/1.54  
% 6.94/1.54  ------ General
% 6.94/1.54  
% 6.94/1.54  abstr_ref_over_cycles:                  0
% 6.94/1.54  abstr_ref_under_cycles:                 0
% 6.94/1.54  gc_basic_clause_elim:                   0
% 6.94/1.54  forced_gc_time:                         0
% 6.94/1.54  parsing_time:                           0.013
% 6.94/1.54  unif_index_cands_time:                  0.
% 6.94/1.54  unif_index_add_time:                    0.
% 6.94/1.54  orderings_time:                         0.
% 6.94/1.54  out_proof_time:                         0.014
% 6.94/1.54  total_time:                             0.978
% 6.94/1.54  num_of_symbols:                         45
% 6.94/1.54  num_of_terms:                           24549
% 6.94/1.54  
% 6.94/1.54  ------ Preprocessing
% 6.94/1.54  
% 6.94/1.54  num_of_splits:                          0
% 6.94/1.54  num_of_split_atoms:                     0
% 6.94/1.54  num_of_reused_defs:                     0
% 6.94/1.54  num_eq_ax_congr_red:                    8
% 6.94/1.54  num_of_sem_filtered_clauses:            1
% 6.94/1.54  num_of_subtypes:                        0
% 6.94/1.54  monotx_restored_types:                  0
% 6.94/1.54  sat_num_of_epr_types:                   0
% 6.94/1.54  sat_num_of_non_cyclic_types:            0
% 6.94/1.54  sat_guarded_non_collapsed_types:        0
% 6.94/1.54  num_pure_diseq_elim:                    0
% 6.94/1.54  simp_replaced_by:                       0
% 6.94/1.54  res_preprocessed:                       115
% 6.94/1.54  prep_upred:                             0
% 6.94/1.54  prep_unflattend:                        41
% 6.94/1.54  smt_new_axioms:                         0
% 6.94/1.54  pred_elim_cands:                        4
% 6.94/1.54  pred_elim:                              2
% 6.94/1.54  pred_elim_cl:                           2
% 6.94/1.54  pred_elim_cycles:                       4
% 6.94/1.54  merged_defs:                            0
% 6.94/1.54  merged_defs_ncl:                        0
% 6.94/1.54  bin_hyper_res:                          0
% 6.94/1.54  prep_cycles:                            4
% 6.94/1.54  pred_elim_time:                         0.021
% 6.94/1.54  splitting_time:                         0.
% 6.94/1.54  sem_filter_time:                        0.
% 6.94/1.54  monotx_time:                            0.
% 6.94/1.54  subtype_inf_time:                       0.
% 6.94/1.54  
% 6.94/1.54  ------ Problem properties
% 6.94/1.54  
% 6.94/1.54  clauses:                                23
% 6.94/1.54  conjectures:                            5
% 6.94/1.54  epr:                                    5
% 6.94/1.54  horn:                                   15
% 6.94/1.54  ground:                                 6
% 6.94/1.54  unary:                                  12
% 6.94/1.54  binary:                                 9
% 6.94/1.54  lits:                                   44
% 6.94/1.54  lits_eq:                                11
% 6.94/1.54  fd_pure:                                0
% 6.94/1.54  fd_pseudo:                              0
% 6.94/1.54  fd_cond:                                0
% 6.94/1.54  fd_pseudo_cond:                         1
% 6.94/1.54  ac_symbols:                             0
% 6.94/1.54  
% 6.94/1.54  ------ Propositional Solver
% 6.94/1.54  
% 6.94/1.54  prop_solver_calls:                      29
% 6.94/1.54  prop_fast_solver_calls:                 1418
% 6.94/1.54  smt_solver_calls:                       0
% 6.94/1.54  smt_fast_solver_calls:                  0
% 6.94/1.54  prop_num_of_clauses:                    6283
% 6.94/1.54  prop_preprocess_simplified:             12778
% 6.94/1.54  prop_fo_subsumed:                       25
% 6.94/1.54  prop_solver_time:                       0.
% 6.94/1.54  smt_solver_time:                        0.
% 6.94/1.54  smt_fast_solver_time:                   0.
% 6.94/1.54  prop_fast_solver_time:                  0.
% 6.94/1.54  prop_unsat_core_time:                   0.001
% 6.94/1.54  
% 6.94/1.54  ------ QBF
% 6.94/1.54  
% 6.94/1.54  qbf_q_res:                              0
% 6.94/1.54  qbf_num_tautologies:                    0
% 6.94/1.54  qbf_prep_cycles:                        0
% 6.94/1.54  
% 6.94/1.54  ------ BMC1
% 6.94/1.54  
% 6.94/1.54  bmc1_current_bound:                     -1
% 6.94/1.54  bmc1_last_solved_bound:                 -1
% 6.94/1.54  bmc1_unsat_core_size:                   -1
% 6.94/1.54  bmc1_unsat_core_parents_size:           -1
% 6.94/1.54  bmc1_merge_next_fun:                    0
% 6.94/1.54  bmc1_unsat_core_clauses_time:           0.
% 6.94/1.54  
% 6.94/1.54  ------ Instantiation
% 6.94/1.54  
% 6.94/1.54  inst_num_of_clauses:                    2043
% 6.94/1.54  inst_num_in_passive:                    381
% 6.94/1.54  inst_num_in_active:                     744
% 6.94/1.54  inst_num_in_unprocessed:                921
% 6.94/1.54  inst_num_of_loops:                      770
% 6.94/1.54  inst_num_of_learning_restarts:          0
% 6.94/1.54  inst_num_moves_active_passive:          22
% 6.94/1.54  inst_lit_activity:                      0
% 6.94/1.54  inst_lit_activity_moves:                0
% 6.94/1.54  inst_num_tautologies:                   0
% 6.94/1.54  inst_num_prop_implied:                  0
% 6.94/1.54  inst_num_existing_simplified:           0
% 6.94/1.54  inst_num_eq_res_simplified:             0
% 6.94/1.54  inst_num_child_elim:                    0
% 6.94/1.54  inst_num_of_dismatching_blockings:      2573
% 6.94/1.54  inst_num_of_non_proper_insts:           3047
% 6.94/1.54  inst_num_of_duplicates:                 0
% 6.94/1.54  inst_inst_num_from_inst_to_res:         0
% 6.94/1.54  inst_dismatching_checking_time:         0.
% 6.94/1.54  
% 6.94/1.54  ------ Resolution
% 6.94/1.54  
% 6.94/1.54  res_num_of_clauses:                     0
% 6.94/1.54  res_num_in_passive:                     0
% 6.94/1.54  res_num_in_active:                      0
% 6.94/1.54  res_num_of_loops:                       119
% 6.94/1.54  res_forward_subset_subsumed:            263
% 6.94/1.54  res_backward_subset_subsumed:           14
% 6.94/1.54  res_forward_subsumed:                   0
% 6.94/1.54  res_backward_subsumed:                  0
% 6.94/1.54  res_forward_subsumption_resolution:     0
% 6.94/1.54  res_backward_subsumption_resolution:    0
% 6.94/1.54  res_clause_to_clause_subsumption:       1167
% 6.94/1.54  res_orphan_elimination:                 0
% 6.94/1.54  res_tautology_del:                      241
% 6.94/1.54  res_num_eq_res_simplified:              0
% 6.94/1.54  res_num_sel_changes:                    0
% 6.94/1.55  res_moves_from_active_to_pass:          0
% 6.94/1.55  
% 6.94/1.55  ------ Superposition
% 6.94/1.55  
% 6.94/1.55  sup_time_total:                         0.
% 6.94/1.55  sup_time_generating:                    0.
% 6.94/1.55  sup_time_sim_full:                      0.
% 6.94/1.55  sup_time_sim_immed:                     0.
% 6.94/1.55  
% 6.94/1.55  sup_num_of_clauses:                     294
% 6.94/1.55  sup_num_in_active:                      154
% 6.94/1.55  sup_num_in_passive:                     140
% 6.94/1.55  sup_num_of_loops:                       153
% 6.94/1.55  sup_fw_superposition:                   168
% 6.94/1.55  sup_bw_superposition:                   199
% 6.94/1.55  sup_immediate_simplified:               57
% 6.94/1.55  sup_given_eliminated:                   0
% 6.94/1.55  comparisons_done:                       0
% 6.94/1.55  comparisons_avoided:                    0
% 6.94/1.55  
% 6.94/1.55  ------ Simplifications
% 6.94/1.55  
% 6.94/1.55  
% 6.94/1.55  sim_fw_subset_subsumed:                 18
% 6.94/1.55  sim_bw_subset_subsumed:                 0
% 6.94/1.55  sim_fw_subsumed:                        2
% 6.94/1.55  sim_bw_subsumed:                        0
% 6.94/1.55  sim_fw_subsumption_res:                 2
% 6.94/1.55  sim_bw_subsumption_res:                 0
% 6.94/1.55  sim_tautology_del:                      0
% 6.94/1.55  sim_eq_tautology_del:                   13
% 6.94/1.55  sim_eq_res_simp:                        1
% 6.94/1.55  sim_fw_demodulated:                     24
% 6.94/1.55  sim_bw_demodulated:                     0
% 6.94/1.55  sim_light_normalised:                   24
% 6.94/1.55  sim_joinable_taut:                      0
% 6.94/1.55  sim_joinable_simp:                      0
% 6.94/1.55  sim_ac_normalised:                      0
% 6.94/1.55  sim_smt_subsumption:                    0
% 6.94/1.55  
%------------------------------------------------------------------------------
