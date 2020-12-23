%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:54 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 677 expanded)
%              Number of clauses        :   78 ( 210 expanded)
%              Number of leaves         :   15 ( 176 expanded)
%              Depth                    :   25
%              Number of atoms          :  409 (4407 expanded)
%              Number of equality atoms :  106 ( 250 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
            | ~ r1_tarski(X2,k1_relat_1(X0))
            | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
          & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
            | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
     => ( ( ~ r1_tarski(k9_relat_1(X0,sK3),k1_relat_1(X1))
          | ~ r1_tarski(sK3,k1_relat_1(X0))
          | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(X0,X1))) )
        & ( ( r1_tarski(k9_relat_1(X0,sK3),k1_relat_1(X1))
            & r1_tarski(sK3,k1_relat_1(X0)) )
          | r1_tarski(sK3,k1_relat_1(k5_relat_1(X0,X1))) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK2))
              | ~ r1_tarski(X2,k1_relat_1(X0))
              | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK2))) )
            & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK2))
                & r1_tarski(X2,k1_relat_1(X0)) )
              | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK2))) ) )
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  | ~ r1_tarski(X2,k1_relat_1(X0))
                  | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
                & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                    & r1_tarski(X2,k1_relat_1(X0)) )
                  | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(sK1,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(sK1))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK1,X1))) )
              & ( ( r1_tarski(k9_relat_1(sK1,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(sK1)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(sK1,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ~ r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
      | ~ r1_tarski(sK3,k1_relat_1(sK1))
      | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) )
    & ( ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
        & r1_tarski(sK3,k1_relat_1(sK1)) )
      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f28,f27,f26])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,
    ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,
    ( r1_tarski(sK3,k1_relat_1(sK1))
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
    | ~ r1_tarski(sK3,k1_relat_1(sK1))
    | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_147,plain,
    ( r2_hidden(sK0(X0_41,X1_41),X0_41)
    | r1_tarski(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_404,plain,
    ( r2_hidden(sK0(X0_41,X1_41),X0_41) = iProver_top
    | r1_tarski(X0_41,X1_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_147])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_145,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(k9_relat_1(X0_40,X0_41),k9_relat_1(X0_40,X1_41))
    | ~ v1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_406,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(k9_relat_1(X0_40,X0_41),k9_relat_1(X0_40,X1_41)) = iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_145])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_146,plain,
    ( ~ r2_hidden(X0_42,X0_41)
    | r2_hidden(X0_42,X1_41)
    | ~ r1_tarski(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_405,plain,
    ( r2_hidden(X0_42,X0_41) != iProver_top
    | r2_hidden(X0_42,X1_41) = iProver_top
    | r1_tarski(X0_41,X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_146])).

cnf(c_1750,plain,
    ( r2_hidden(X0_42,k9_relat_1(X0_40,X0_41)) != iProver_top
    | r2_hidden(X0_42,k9_relat_1(X0_40,X1_41)) = iProver_top
    | r1_tarski(X0_41,X1_41) != iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_406,c_405])).

cnf(c_3691,plain,
    ( r2_hidden(sK0(k9_relat_1(X0_40,X0_41),X1_41),k9_relat_1(X0_40,X2_41)) = iProver_top
    | r1_tarski(X0_41,X2_41) != iProver_top
    | r1_tarski(k9_relat_1(X0_40,X0_41),X1_41) = iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_404,c_1750])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_134,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_417,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_134])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_136,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_415,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_136])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_144,plain,
    ( ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(X1_40)
    | k10_relat_1(X1_40,k1_relat_1(X0_40)) = k1_relat_1(k5_relat_1(X1_40,X0_40)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_407,plain,
    ( k10_relat_1(X0_40,k1_relat_1(X1_40)) = k1_relat_1(k5_relat_1(X0_40,X1_40))
    | v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(X1_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_144])).

cnf(c_995,plain,
    ( k10_relat_1(X0_40,k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(X0_40,sK2))
    | v1_relat_1(X0_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_415,c_407])).

cnf(c_1123,plain,
    ( k10_relat_1(sK1,k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_417,c_995])).

cnf(c_6,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_142,plain,
    ( r1_tarski(k9_relat_1(X0_40,k10_relat_1(X0_40,X0_41)),X0_41)
    | ~ v1_funct_1(X0_40)
    | ~ v1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_409,plain,
    ( r1_tarski(k9_relat_1(X0_40,k10_relat_1(X0_40,X0_41)),X0_41) = iProver_top
    | v1_funct_1(X0_40) != iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_142])).

cnf(c_1757,plain,
    ( r1_tarski(k9_relat_1(sK1,k1_relat_1(k5_relat_1(sK1,sK2))),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1123,c_409])).

cnf(c_15,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2215,plain,
    ( r1_tarski(k9_relat_1(sK1,k1_relat_1(k5_relat_1(sK1,sK2))),k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1757,c_15,c_16])).

cnf(c_2221,plain,
    ( r2_hidden(X0_42,k9_relat_1(sK1,k1_relat_1(k5_relat_1(sK1,sK2)))) != iProver_top
    | r2_hidden(X0_42,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2215,c_405])).

cnf(c_4234,plain,
    ( r2_hidden(sK0(k9_relat_1(sK1,X0_41),X1_41),k1_relat_1(sK2)) = iProver_top
    | r1_tarski(X0_41,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top
    | r1_tarski(k9_relat_1(sK1,X0_41),X1_41) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3691,c_2221])).

cnf(c_4484,plain,
    ( r1_tarski(k9_relat_1(sK1,X0_41),X1_41) = iProver_top
    | r1_tarski(X0_41,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top
    | r2_hidden(sK0(k9_relat_1(sK1,X0_41),X1_41),k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4234,c_15])).

cnf(c_4485,plain,
    ( r2_hidden(sK0(k9_relat_1(sK1,X0_41),X1_41),k1_relat_1(sK2)) = iProver_top
    | r1_tarski(X0_41,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top
    | r1_tarski(k9_relat_1(sK1,X0_41),X1_41) = iProver_top ),
    inference(renaming,[status(thm)],[c_4484])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_148,plain,
    ( ~ r2_hidden(sK0(X0_41,X1_41),X1_41)
    | r1_tarski(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_403,plain,
    ( r2_hidden(sK0(X0_41,X1_41),X1_41) != iProver_top
    | r1_tarski(X0_41,X1_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_148])).

cnf(c_4493,plain,
    ( r1_tarski(X0_41,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top
    | r1_tarski(k9_relat_1(sK1,X0_41),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4485,c_403])).

cnf(c_4495,plain,
    ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) = iProver_top
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4493])).

cnf(c_5,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_143,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0_40,X1_40)),k1_relat_1(X0_40))
    | ~ v1_relat_1(X1_40)
    | ~ v1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1149,plain,
    ( r2_hidden(X0_42,k1_relat_1(X0_40))
    | ~ r2_hidden(X0_42,k1_relat_1(k5_relat_1(X0_40,X1_40)))
    | ~ v1_relat_1(X1_40)
    | ~ v1_relat_1(X0_40) ),
    inference(resolution,[status(thm)],[c_143,c_146])).

cnf(c_152,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_150,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_1830,plain,
    ( X0_41 != X1_41
    | X1_41 = X0_41 ),
    inference(resolution,[status(thm)],[c_152,c_150])).

cnf(c_155,plain,
    ( X0_41 != X1_41
    | k9_relat_1(X0_40,X0_41) = k9_relat_1(X0_40,X1_41) ),
    theory(equality)).

cnf(c_2080,plain,
    ( X0_41 != X1_41
    | k9_relat_1(X0_40,X1_41) = k9_relat_1(X0_40,X0_41) ),
    inference(resolution,[status(thm)],[c_1830,c_155])).

cnf(c_153,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(X2_41,X3_41)
    | X2_41 != X0_41
    | X3_41 != X1_41 ),
    theory(equality)).

cnf(c_1274,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(X2_41,X1_41)
    | X2_41 != X0_41 ),
    inference(resolution,[status(thm)],[c_153,c_150])).

cnf(c_2263,plain,
    ( ~ r1_tarski(k9_relat_1(X0_40,X0_41),X1_41)
    | r1_tarski(k9_relat_1(X0_40,X2_41),X1_41)
    | X0_41 != X2_41 ),
    inference(resolution,[status(thm)],[c_2080,c_1274])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_139,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2425,plain,
    ( r1_tarski(k9_relat_1(sK1,X0_41),k1_relat_1(sK2))
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
    | sK3 != X0_41 ),
    inference(resolution,[status(thm)],[c_2263,c_139])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
    | r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_412,plain,
    ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) = iProver_top
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_139])).

cnf(c_7,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_141,plain,
    ( r1_tarski(X0_41,k10_relat_1(X0_40,X1_41))
    | ~ r1_tarski(X0_41,k1_relat_1(X0_40))
    | ~ r1_tarski(k9_relat_1(X0_40,X0_41),X1_41)
    | ~ v1_funct_1(X0_40)
    | ~ v1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_410,plain,
    ( r1_tarski(X0_41,k10_relat_1(X0_40,X1_41)) = iProver_top
    | r1_tarski(X0_41,k1_relat_1(X0_40)) != iProver_top
    | r1_tarski(k9_relat_1(X0_40,X0_41),X1_41) != iProver_top
    | v1_funct_1(X0_40) != iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_141])).

cnf(c_2018,plain,
    ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2))) = iProver_top
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top
    | r1_tarski(sK3,k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_412,c_410])).

cnf(c_2044,plain,
    ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top
    | r1_tarski(sK3,k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2018,c_1123])).

cnf(c_2055,plain,
    ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ r1_tarski(sK3,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2044])).

cnf(c_2440,plain,
    ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2425,c_14,c_13,c_10,c_2055])).

cnf(c_2507,plain,
    ( r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ r2_hidden(X0_42,sK3) ),
    inference(resolution,[status(thm)],[c_2440,c_146])).

cnf(c_2736,plain,
    ( r2_hidden(X0_42,k1_relat_1(sK1))
    | ~ r2_hidden(X0_42,sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_1149,c_2507])).

cnf(c_2442,plain,
    ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2440])).

cnf(c_2478,plain,
    ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2044,c_2442])).

cnf(c_2484,plain,
    ( r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top
    | r2_hidden(X0_42,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_405])).

cnf(c_408,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0_40,X1_40)),k1_relat_1(X0_40)) = iProver_top
    | v1_relat_1(X1_40) != iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_143])).

cnf(c_1013,plain,
    ( r2_hidden(X0_42,k1_relat_1(X0_40)) = iProver_top
    | r2_hidden(X0_42,k1_relat_1(k5_relat_1(X0_40,X1_40))) != iProver_top
    | v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(X1_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_408,c_405])).

cnf(c_2682,plain,
    ( r2_hidden(X0_42,k1_relat_1(sK1)) = iProver_top
    | r2_hidden(X0_42,sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2484,c_1013])).

cnf(c_2702,plain,
    ( r2_hidden(X0_42,k1_relat_1(sK1))
    | ~ r2_hidden(X0_42,sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2682])).

cnf(c_2739,plain,
    ( r2_hidden(X0_42,k1_relat_1(sK1))
    | ~ r2_hidden(X0_42,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2736,c_14,c_12,c_2702])).

cnf(c_3106,plain,
    ( ~ r2_hidden(sK0(X0_41,k1_relat_1(sK1)),sK3)
    | r1_tarski(X0_41,k1_relat_1(sK1)) ),
    inference(resolution,[status(thm)],[c_2739,c_148])).

cnf(c_3207,plain,
    ( r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[status(thm)],[c_3106,c_147])).

cnf(c_3208,plain,
    ( r1_tarski(sK3,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3207])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
    | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,plain,
    ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top
    | r1_tarski(sK3,k1_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4495,c_3208,c_2442,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.28/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/0.98  
% 3.28/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.28/0.98  
% 3.28/0.98  ------  iProver source info
% 3.28/0.98  
% 3.28/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.28/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.28/0.98  git: non_committed_changes: false
% 3.28/0.98  git: last_make_outside_of_git: false
% 3.28/0.98  
% 3.28/0.98  ------ 
% 3.28/0.98  ------ Parsing...
% 3.28/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.28/0.98  
% 3.28/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.28/0.98  
% 3.28/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.28/0.98  
% 3.28/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.28/0.98  ------ Proving...
% 3.28/0.98  ------ Problem Properties 
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  clauses                                 15
% 3.28/0.98  conjectures                             7
% 3.28/0.98  EPR                                     5
% 3.28/0.98  Horn                                    12
% 3.28/0.98  unary                                   4
% 3.28/0.98  binary                                  4
% 3.28/0.98  lits                                    35
% 3.28/0.98  lits eq                                 1
% 3.28/0.98  fd_pure                                 0
% 3.28/0.98  fd_pseudo                               0
% 3.28/0.98  fd_cond                                 0
% 3.28/0.98  fd_pseudo_cond                          0
% 3.28/0.98  AC symbols                              0
% 3.28/0.98  
% 3.28/0.98  ------ Input Options Time Limit: Unbounded
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  ------ 
% 3.28/0.98  Current options:
% 3.28/0.98  ------ 
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  ------ Proving...
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  % SZS status Theorem for theBenchmark.p
% 3.28/0.98  
% 3.28/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.28/0.98  
% 3.28/0.98  fof(f1,axiom,(
% 3.28/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f9,plain,(
% 3.28/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.28/0.98    inference(ennf_transformation,[],[f1])).
% 3.28/0.98  
% 3.28/0.98  fof(f20,plain,(
% 3.28/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.28/0.98    inference(nnf_transformation,[],[f9])).
% 3.28/0.98  
% 3.28/0.98  fof(f21,plain,(
% 3.28/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.28/0.98    inference(rectify,[],[f20])).
% 3.28/0.98  
% 3.28/0.98  fof(f22,plain,(
% 3.28/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.28/0.98    introduced(choice_axiom,[])).
% 3.28/0.98  
% 3.28/0.98  fof(f23,plain,(
% 3.28/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.28/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 3.28/0.98  
% 3.28/0.98  fof(f31,plain,(
% 3.28/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f23])).
% 3.28/0.98  
% 3.28/0.98  fof(f2,axiom,(
% 3.28/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f10,plain,(
% 3.28/0.98    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.28/0.98    inference(ennf_transformation,[],[f2])).
% 3.28/0.98  
% 3.28/0.98  fof(f11,plain,(
% 3.28/0.98    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.28/0.98    inference(flattening,[],[f10])).
% 3.28/0.98  
% 3.28/0.98  fof(f33,plain,(
% 3.28/0.98    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f11])).
% 3.28/0.98  
% 3.28/0.98  fof(f30,plain,(
% 3.28/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f23])).
% 3.28/0.98  
% 3.28/0.98  fof(f7,conjecture,(
% 3.28/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 3.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f8,negated_conjecture,(
% 3.28/0.98    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 3.28/0.98    inference(negated_conjecture,[],[f7])).
% 3.28/0.98  
% 3.28/0.98  fof(f18,plain,(
% 3.28/0.98    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.28/0.98    inference(ennf_transformation,[],[f8])).
% 3.28/0.98  
% 3.28/0.98  fof(f19,plain,(
% 3.28/0.98    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.28/0.98    inference(flattening,[],[f18])).
% 3.28/0.98  
% 3.28/0.98  fof(f24,plain,(
% 3.28/0.98    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.28/0.98    inference(nnf_transformation,[],[f19])).
% 3.28/0.98  
% 3.28/0.98  fof(f25,plain,(
% 3.28/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.28/0.98    inference(flattening,[],[f24])).
% 3.28/0.98  
% 3.28/0.98  fof(f28,plain,(
% 3.28/0.98    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) => ((~r1_tarski(k9_relat_1(X0,sK3),k1_relat_1(X1)) | ~r1_tarski(sK3,k1_relat_1(X0)) | ~r1_tarski(sK3,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,sK3),k1_relat_1(X1)) & r1_tarski(sK3,k1_relat_1(X0))) | r1_tarski(sK3,k1_relat_1(k5_relat_1(X0,X1)))))) )),
% 3.28/0.98    introduced(choice_axiom,[])).
% 3.28/0.98  
% 3.28/0.98  fof(f27,plain,(
% 3.28/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK2)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK2)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK2)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK2))))) & v1_funct_1(sK2) & v1_relat_1(sK2))) )),
% 3.28/0.98    introduced(choice_axiom,[])).
% 3.28/0.98  
% 3.28/0.98  fof(f26,plain,(
% 3.28/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK1,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK1,X1)))) & ((r1_tarski(k9_relat_1(sK1,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK1))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK1,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 3.28/0.98    introduced(choice_axiom,[])).
% 3.28/0.98  
% 3.28/0.98  fof(f29,plain,(
% 3.28/0.98    (((~r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) | ~r1_tarski(sK3,k1_relat_1(sK1)) | ~r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))) & ((r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) & r1_tarski(sK3,k1_relat_1(sK1))) | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))))) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 3.28/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f28,f27,f26])).
% 3.28/0.98  
% 3.28/0.98  fof(f38,plain,(
% 3.28/0.98    v1_relat_1(sK1)),
% 3.28/0.98    inference(cnf_transformation,[],[f29])).
% 3.28/0.98  
% 3.28/0.98  fof(f40,plain,(
% 3.28/0.98    v1_relat_1(sK2)),
% 3.28/0.98    inference(cnf_transformation,[],[f29])).
% 3.28/0.98  
% 3.28/0.98  fof(f3,axiom,(
% 3.28/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f12,plain,(
% 3.28/0.98    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.28/0.98    inference(ennf_transformation,[],[f3])).
% 3.28/0.98  
% 3.28/0.98  fof(f34,plain,(
% 3.28/0.98    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f12])).
% 3.28/0.98  
% 3.28/0.98  fof(f5,axiom,(
% 3.28/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f14,plain,(
% 3.28/0.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.28/0.98    inference(ennf_transformation,[],[f5])).
% 3.28/0.98  
% 3.28/0.98  fof(f15,plain,(
% 3.28/0.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.28/0.98    inference(flattening,[],[f14])).
% 3.28/0.98  
% 3.28/0.98  fof(f36,plain,(
% 3.28/0.98    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f15])).
% 3.28/0.98  
% 3.28/0.98  fof(f39,plain,(
% 3.28/0.98    v1_funct_1(sK1)),
% 3.28/0.98    inference(cnf_transformation,[],[f29])).
% 3.28/0.98  
% 3.28/0.98  fof(f32,plain,(
% 3.28/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f23])).
% 3.28/0.98  
% 3.28/0.98  fof(f4,axiom,(
% 3.28/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 3.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f13,plain,(
% 3.28/0.98    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.28/0.98    inference(ennf_transformation,[],[f4])).
% 3.28/0.98  
% 3.28/0.98  fof(f35,plain,(
% 3.28/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f13])).
% 3.28/0.98  
% 3.28/0.98  fof(f43,plain,(
% 3.28/0.98    r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))),
% 3.28/0.98    inference(cnf_transformation,[],[f29])).
% 3.28/0.98  
% 3.28/0.98  fof(f42,plain,(
% 3.28/0.98    r1_tarski(sK3,k1_relat_1(sK1)) | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))),
% 3.28/0.98    inference(cnf_transformation,[],[f29])).
% 3.28/0.98  
% 3.28/0.98  fof(f6,axiom,(
% 3.28/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 3.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.28/0.98  
% 3.28/0.98  fof(f16,plain,(
% 3.28/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.28/0.98    inference(ennf_transformation,[],[f6])).
% 3.28/0.98  
% 3.28/0.98  fof(f17,plain,(
% 3.28/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.28/0.98    inference(flattening,[],[f16])).
% 3.28/0.98  
% 3.28/0.98  fof(f37,plain,(
% 3.28/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.28/0.98    inference(cnf_transformation,[],[f17])).
% 3.28/0.98  
% 3.28/0.98  fof(f44,plain,(
% 3.28/0.98    ~r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) | ~r1_tarski(sK3,k1_relat_1(sK1)) | ~r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))),
% 3.28/0.98    inference(cnf_transformation,[],[f29])).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1,plain,
% 3.28/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.28/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_147,plain,
% 3.28/0.98      ( r2_hidden(sK0(X0_41,X1_41),X0_41) | r1_tarski(X0_41,X1_41) ),
% 3.28/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_404,plain,
% 3.28/0.98      ( r2_hidden(sK0(X0_41,X1_41),X0_41) = iProver_top
% 3.28/0.98      | r1_tarski(X0_41,X1_41) = iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_147]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3,plain,
% 3.28/0.98      ( ~ r1_tarski(X0,X1)
% 3.28/0.98      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.28/0.98      | ~ v1_relat_1(X2) ),
% 3.28/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_145,plain,
% 3.28/0.98      ( ~ r1_tarski(X0_41,X1_41)
% 3.28/0.98      | r1_tarski(k9_relat_1(X0_40,X0_41),k9_relat_1(X0_40,X1_41))
% 3.28/0.98      | ~ v1_relat_1(X0_40) ),
% 3.28/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_406,plain,
% 3.28/0.98      ( r1_tarski(X0_41,X1_41) != iProver_top
% 3.28/0.98      | r1_tarski(k9_relat_1(X0_40,X0_41),k9_relat_1(X0_40,X1_41)) = iProver_top
% 3.28/0.98      | v1_relat_1(X0_40) != iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_145]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2,plain,
% 3.28/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.28/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_146,plain,
% 3.28/0.98      ( ~ r2_hidden(X0_42,X0_41)
% 3.28/0.98      | r2_hidden(X0_42,X1_41)
% 3.28/0.98      | ~ r1_tarski(X0_41,X1_41) ),
% 3.28/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_405,plain,
% 3.28/0.98      ( r2_hidden(X0_42,X0_41) != iProver_top
% 3.28/0.98      | r2_hidden(X0_42,X1_41) = iProver_top
% 3.28/0.98      | r1_tarski(X0_41,X1_41) != iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_146]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1750,plain,
% 3.28/0.98      ( r2_hidden(X0_42,k9_relat_1(X0_40,X0_41)) != iProver_top
% 3.28/0.98      | r2_hidden(X0_42,k9_relat_1(X0_40,X1_41)) = iProver_top
% 3.28/0.98      | r1_tarski(X0_41,X1_41) != iProver_top
% 3.28/0.98      | v1_relat_1(X0_40) != iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_406,c_405]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3691,plain,
% 3.28/0.98      ( r2_hidden(sK0(k9_relat_1(X0_40,X0_41),X1_41),k9_relat_1(X0_40,X2_41)) = iProver_top
% 3.28/0.98      | r1_tarski(X0_41,X2_41) != iProver_top
% 3.28/0.98      | r1_tarski(k9_relat_1(X0_40,X0_41),X1_41) = iProver_top
% 3.28/0.98      | v1_relat_1(X0_40) != iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_404,c_1750]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_14,negated_conjecture,
% 3.28/0.98      ( v1_relat_1(sK1) ),
% 3.28/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_134,negated_conjecture,
% 3.28/0.98      ( v1_relat_1(sK1) ),
% 3.28/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_417,plain,
% 3.28/0.98      ( v1_relat_1(sK1) = iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_134]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_12,negated_conjecture,
% 3.28/0.98      ( v1_relat_1(sK2) ),
% 3.28/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_136,negated_conjecture,
% 3.28/0.98      ( v1_relat_1(sK2) ),
% 3.28/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_415,plain,
% 3.28/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_136]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_4,plain,
% 3.28/0.98      ( ~ v1_relat_1(X0)
% 3.28/0.98      | ~ v1_relat_1(X1)
% 3.28/0.98      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 3.28/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_144,plain,
% 3.28/0.98      ( ~ v1_relat_1(X0_40)
% 3.28/0.98      | ~ v1_relat_1(X1_40)
% 3.28/0.98      | k10_relat_1(X1_40,k1_relat_1(X0_40)) = k1_relat_1(k5_relat_1(X1_40,X0_40)) ),
% 3.28/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_407,plain,
% 3.28/0.98      ( k10_relat_1(X0_40,k1_relat_1(X1_40)) = k1_relat_1(k5_relat_1(X0_40,X1_40))
% 3.28/0.98      | v1_relat_1(X0_40) != iProver_top
% 3.28/0.98      | v1_relat_1(X1_40) != iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_144]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_995,plain,
% 3.28/0.98      ( k10_relat_1(X0_40,k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(X0_40,sK2))
% 3.28/0.98      | v1_relat_1(X0_40) != iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_415,c_407]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1123,plain,
% 3.28/0.98      ( k10_relat_1(sK1,k1_relat_1(sK2)) = k1_relat_1(k5_relat_1(sK1,sK2)) ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_417,c_995]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_6,plain,
% 3.28/0.98      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.28/0.98      | ~ v1_funct_1(X0)
% 3.28/0.98      | ~ v1_relat_1(X0) ),
% 3.28/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_142,plain,
% 3.28/0.98      ( r1_tarski(k9_relat_1(X0_40,k10_relat_1(X0_40,X0_41)),X0_41)
% 3.28/0.98      | ~ v1_funct_1(X0_40)
% 3.28/0.98      | ~ v1_relat_1(X0_40) ),
% 3.28/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_409,plain,
% 3.28/0.98      ( r1_tarski(k9_relat_1(X0_40,k10_relat_1(X0_40,X0_41)),X0_41) = iProver_top
% 3.28/0.98      | v1_funct_1(X0_40) != iProver_top
% 3.28/0.98      | v1_relat_1(X0_40) != iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_142]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1757,plain,
% 3.28/0.98      ( r1_tarski(k9_relat_1(sK1,k1_relat_1(k5_relat_1(sK1,sK2))),k1_relat_1(sK2)) = iProver_top
% 3.28/0.98      | v1_funct_1(sK1) != iProver_top
% 3.28/0.98      | v1_relat_1(sK1) != iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_1123,c_409]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_15,plain,
% 3.28/0.98      ( v1_relat_1(sK1) = iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_13,negated_conjecture,
% 3.28/0.98      ( v1_funct_1(sK1) ),
% 3.28/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_16,plain,
% 3.28/0.98      ( v1_funct_1(sK1) = iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2215,plain,
% 3.28/0.98      ( r1_tarski(k9_relat_1(sK1,k1_relat_1(k5_relat_1(sK1,sK2))),k1_relat_1(sK2)) = iProver_top ),
% 3.28/0.98      inference(global_propositional_subsumption,
% 3.28/0.98                [status(thm)],
% 3.28/0.98                [c_1757,c_15,c_16]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2221,plain,
% 3.28/0.98      ( r2_hidden(X0_42,k9_relat_1(sK1,k1_relat_1(k5_relat_1(sK1,sK2)))) != iProver_top
% 3.28/0.98      | r2_hidden(X0_42,k1_relat_1(sK2)) = iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_2215,c_405]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_4234,plain,
% 3.28/0.98      ( r2_hidden(sK0(k9_relat_1(sK1,X0_41),X1_41),k1_relat_1(sK2)) = iProver_top
% 3.28/0.98      | r1_tarski(X0_41,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top
% 3.28/0.98      | r1_tarski(k9_relat_1(sK1,X0_41),X1_41) = iProver_top
% 3.28/0.98      | v1_relat_1(sK1) != iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_3691,c_2221]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_4484,plain,
% 3.28/0.98      ( r1_tarski(k9_relat_1(sK1,X0_41),X1_41) = iProver_top
% 3.28/0.98      | r1_tarski(X0_41,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top
% 3.28/0.98      | r2_hidden(sK0(k9_relat_1(sK1,X0_41),X1_41),k1_relat_1(sK2)) = iProver_top ),
% 3.28/0.98      inference(global_propositional_subsumption,
% 3.28/0.98                [status(thm)],
% 3.28/0.98                [c_4234,c_15]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_4485,plain,
% 3.28/0.98      ( r2_hidden(sK0(k9_relat_1(sK1,X0_41),X1_41),k1_relat_1(sK2)) = iProver_top
% 3.28/0.98      | r1_tarski(X0_41,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top
% 3.28/0.98      | r1_tarski(k9_relat_1(sK1,X0_41),X1_41) = iProver_top ),
% 3.28/0.98      inference(renaming,[status(thm)],[c_4484]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_0,plain,
% 3.28/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.28/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_148,plain,
% 3.28/0.98      ( ~ r2_hidden(sK0(X0_41,X1_41),X1_41) | r1_tarski(X0_41,X1_41) ),
% 3.28/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_403,plain,
% 3.28/0.98      ( r2_hidden(sK0(X0_41,X1_41),X1_41) != iProver_top
% 3.28/0.98      | r1_tarski(X0_41,X1_41) = iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_148]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_4493,plain,
% 3.28/0.98      ( r1_tarski(X0_41,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top
% 3.28/0.98      | r1_tarski(k9_relat_1(sK1,X0_41),k1_relat_1(sK2)) = iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_4485,c_403]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_4495,plain,
% 3.28/0.98      ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) = iProver_top
% 3.28/0.98      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top ),
% 3.28/0.98      inference(instantiation,[status(thm)],[c_4493]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_5,plain,
% 3.28/0.98      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 3.28/0.98      | ~ v1_relat_1(X1)
% 3.28/0.98      | ~ v1_relat_1(X0) ),
% 3.28/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_143,plain,
% 3.28/0.98      ( r1_tarski(k1_relat_1(k5_relat_1(X0_40,X1_40)),k1_relat_1(X0_40))
% 3.28/0.98      | ~ v1_relat_1(X1_40)
% 3.28/0.98      | ~ v1_relat_1(X0_40) ),
% 3.28/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1149,plain,
% 3.28/0.98      ( r2_hidden(X0_42,k1_relat_1(X0_40))
% 3.28/0.98      | ~ r2_hidden(X0_42,k1_relat_1(k5_relat_1(X0_40,X1_40)))
% 3.28/0.98      | ~ v1_relat_1(X1_40)
% 3.28/0.98      | ~ v1_relat_1(X0_40) ),
% 3.28/0.98      inference(resolution,[status(thm)],[c_143,c_146]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_152,plain,
% 3.28/0.98      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 3.28/0.98      theory(equality) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_150,plain,( X0_41 = X0_41 ),theory(equality) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1830,plain,
% 3.28/0.98      ( X0_41 != X1_41 | X1_41 = X0_41 ),
% 3.28/0.98      inference(resolution,[status(thm)],[c_152,c_150]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_155,plain,
% 3.28/0.98      ( X0_41 != X1_41
% 3.28/0.98      | k9_relat_1(X0_40,X0_41) = k9_relat_1(X0_40,X1_41) ),
% 3.28/0.98      theory(equality) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2080,plain,
% 3.28/0.98      ( X0_41 != X1_41
% 3.28/0.98      | k9_relat_1(X0_40,X1_41) = k9_relat_1(X0_40,X0_41) ),
% 3.28/0.98      inference(resolution,[status(thm)],[c_1830,c_155]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_153,plain,
% 3.28/0.98      ( ~ r1_tarski(X0_41,X1_41)
% 3.28/0.98      | r1_tarski(X2_41,X3_41)
% 3.28/0.98      | X2_41 != X0_41
% 3.28/0.98      | X3_41 != X1_41 ),
% 3.28/0.98      theory(equality) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1274,plain,
% 3.28/0.98      ( ~ r1_tarski(X0_41,X1_41)
% 3.28/0.98      | r1_tarski(X2_41,X1_41)
% 3.28/0.98      | X2_41 != X0_41 ),
% 3.28/0.98      inference(resolution,[status(thm)],[c_153,c_150]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2263,plain,
% 3.28/0.98      ( ~ r1_tarski(k9_relat_1(X0_40,X0_41),X1_41)
% 3.28/0.98      | r1_tarski(k9_relat_1(X0_40,X2_41),X1_41)
% 3.28/0.98      | X0_41 != X2_41 ),
% 3.28/0.98      inference(resolution,[status(thm)],[c_2080,c_1274]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_9,negated_conjecture,
% 3.28/0.98      ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
% 3.28/0.98      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
% 3.28/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_139,negated_conjecture,
% 3.28/0.98      ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
% 3.28/0.98      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
% 3.28/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2425,plain,
% 3.28/0.98      ( r1_tarski(k9_relat_1(sK1,X0_41),k1_relat_1(sK2))
% 3.28/0.98      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
% 3.28/0.98      | sK3 != X0_41 ),
% 3.28/0.98      inference(resolution,[status(thm)],[c_2263,c_139]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_10,negated_conjecture,
% 3.28/0.98      ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
% 3.28/0.98      | r1_tarski(sK3,k1_relat_1(sK1)) ),
% 3.28/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_412,plain,
% 3.28/0.98      ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) = iProver_top
% 3.28/0.98      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_139]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_7,plain,
% 3.28/0.98      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 3.28/0.98      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.28/0.98      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 3.28/0.98      | ~ v1_funct_1(X1)
% 3.28/0.98      | ~ v1_relat_1(X1) ),
% 3.28/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_141,plain,
% 3.28/0.98      ( r1_tarski(X0_41,k10_relat_1(X0_40,X1_41))
% 3.28/0.98      | ~ r1_tarski(X0_41,k1_relat_1(X0_40))
% 3.28/0.98      | ~ r1_tarski(k9_relat_1(X0_40,X0_41),X1_41)
% 3.28/0.98      | ~ v1_funct_1(X0_40)
% 3.28/0.98      | ~ v1_relat_1(X0_40) ),
% 3.28/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_410,plain,
% 3.28/0.98      ( r1_tarski(X0_41,k10_relat_1(X0_40,X1_41)) = iProver_top
% 3.28/0.98      | r1_tarski(X0_41,k1_relat_1(X0_40)) != iProver_top
% 3.28/0.98      | r1_tarski(k9_relat_1(X0_40,X0_41),X1_41) != iProver_top
% 3.28/0.98      | v1_funct_1(X0_40) != iProver_top
% 3.28/0.98      | v1_relat_1(X0_40) != iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_141]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2018,plain,
% 3.28/0.98      ( r1_tarski(sK3,k10_relat_1(sK1,k1_relat_1(sK2))) = iProver_top
% 3.28/0.98      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top
% 3.28/0.98      | r1_tarski(sK3,k1_relat_1(sK1)) != iProver_top
% 3.28/0.98      | v1_funct_1(sK1) != iProver_top
% 3.28/0.98      | v1_relat_1(sK1) != iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_412,c_410]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2044,plain,
% 3.28/0.98      ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top
% 3.28/0.98      | r1_tarski(sK3,k1_relat_1(sK1)) != iProver_top
% 3.28/0.98      | v1_funct_1(sK1) != iProver_top
% 3.28/0.98      | v1_relat_1(sK1) != iProver_top ),
% 3.28/0.98      inference(light_normalisation,[status(thm)],[c_2018,c_1123]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2055,plain,
% 3.28/0.98      ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
% 3.28/0.98      | ~ r1_tarski(sK3,k1_relat_1(sK1))
% 3.28/0.98      | ~ v1_funct_1(sK1)
% 3.28/0.98      | ~ v1_relat_1(sK1) ),
% 3.28/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2044]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2440,plain,
% 3.28/0.98      ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) ),
% 3.28/0.98      inference(global_propositional_subsumption,
% 3.28/0.98                [status(thm)],
% 3.28/0.98                [c_2425,c_14,c_13,c_10,c_2055]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2507,plain,
% 3.28/0.98      ( r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK1,sK2)))
% 3.28/0.98      | ~ r2_hidden(X0_42,sK3) ),
% 3.28/0.98      inference(resolution,[status(thm)],[c_2440,c_146]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2736,plain,
% 3.28/0.98      ( r2_hidden(X0_42,k1_relat_1(sK1))
% 3.28/0.98      | ~ r2_hidden(X0_42,sK3)
% 3.28/0.98      | ~ v1_relat_1(sK2)
% 3.28/0.98      | ~ v1_relat_1(sK1) ),
% 3.28/0.98      inference(resolution,[status(thm)],[c_1149,c_2507]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2442,plain,
% 3.28/0.98      ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_2440]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2478,plain,
% 3.28/0.98      ( r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top ),
% 3.28/0.98      inference(global_propositional_subsumption,
% 3.28/0.98                [status(thm)],
% 3.28/0.98                [c_2044,c_2442]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2484,plain,
% 3.28/0.98      ( r2_hidden(X0_42,k1_relat_1(k5_relat_1(sK1,sK2))) = iProver_top
% 3.28/0.98      | r2_hidden(X0_42,sK3) != iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_2478,c_405]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_408,plain,
% 3.28/0.98      ( r1_tarski(k1_relat_1(k5_relat_1(X0_40,X1_40)),k1_relat_1(X0_40)) = iProver_top
% 3.28/0.98      | v1_relat_1(X1_40) != iProver_top
% 3.28/0.98      | v1_relat_1(X0_40) != iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_143]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_1013,plain,
% 3.28/0.98      ( r2_hidden(X0_42,k1_relat_1(X0_40)) = iProver_top
% 3.28/0.98      | r2_hidden(X0_42,k1_relat_1(k5_relat_1(X0_40,X1_40))) != iProver_top
% 3.28/0.98      | v1_relat_1(X0_40) != iProver_top
% 3.28/0.98      | v1_relat_1(X1_40) != iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_408,c_405]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2682,plain,
% 3.28/0.98      ( r2_hidden(X0_42,k1_relat_1(sK1)) = iProver_top
% 3.28/0.98      | r2_hidden(X0_42,sK3) != iProver_top
% 3.28/0.98      | v1_relat_1(sK2) != iProver_top
% 3.28/0.98      | v1_relat_1(sK1) != iProver_top ),
% 3.28/0.98      inference(superposition,[status(thm)],[c_2484,c_1013]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2702,plain,
% 3.28/0.98      ( r2_hidden(X0_42,k1_relat_1(sK1))
% 3.28/0.98      | ~ r2_hidden(X0_42,sK3)
% 3.28/0.98      | ~ v1_relat_1(sK2)
% 3.28/0.98      | ~ v1_relat_1(sK1) ),
% 3.28/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2682]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_2739,plain,
% 3.28/0.98      ( r2_hidden(X0_42,k1_relat_1(sK1)) | ~ r2_hidden(X0_42,sK3) ),
% 3.28/0.98      inference(global_propositional_subsumption,
% 3.28/0.98                [status(thm)],
% 3.28/0.98                [c_2736,c_14,c_12,c_2702]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3106,plain,
% 3.28/0.98      ( ~ r2_hidden(sK0(X0_41,k1_relat_1(sK1)),sK3)
% 3.28/0.98      | r1_tarski(X0_41,k1_relat_1(sK1)) ),
% 3.28/0.98      inference(resolution,[status(thm)],[c_2739,c_148]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3207,plain,
% 3.28/0.98      ( r1_tarski(sK3,k1_relat_1(sK1)) ),
% 3.28/0.98      inference(resolution,[status(thm)],[c_3106,c_147]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_3208,plain,
% 3.28/0.98      ( r1_tarski(sK3,k1_relat_1(sK1)) = iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_3207]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_8,negated_conjecture,
% 3.28/0.98      ( ~ r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2))
% 3.28/0.98      | ~ r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2)))
% 3.28/0.98      | ~ r1_tarski(sK3,k1_relat_1(sK1)) ),
% 3.28/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(c_21,plain,
% 3.28/0.98      ( r1_tarski(k9_relat_1(sK1,sK3),k1_relat_1(sK2)) != iProver_top
% 3.28/0.98      | r1_tarski(sK3,k1_relat_1(k5_relat_1(sK1,sK2))) != iProver_top
% 3.28/0.98      | r1_tarski(sK3,k1_relat_1(sK1)) != iProver_top ),
% 3.28/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.28/0.98  
% 3.28/0.98  cnf(contradiction,plain,
% 3.28/0.98      ( $false ),
% 3.28/0.98      inference(minisat,[status(thm)],[c_4495,c_3208,c_2442,c_21]) ).
% 3.28/0.98  
% 3.28/0.98  
% 3.28/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.28/0.98  
% 3.28/0.98  ------                               Statistics
% 3.28/0.98  
% 3.28/0.98  ------ Selected
% 3.28/0.98  
% 3.28/0.98  total_time:                             0.163
% 3.28/0.98  
%------------------------------------------------------------------------------
