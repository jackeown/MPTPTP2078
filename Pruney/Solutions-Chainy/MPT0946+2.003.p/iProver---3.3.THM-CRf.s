%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:41 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  181 (3346 expanded)
%              Number of clauses        :  124 (1235 expanded)
%              Number of leaves         :   17 ( 719 expanded)
%              Depth                    :   35
%              Number of atoms          :  609 (12288 expanded)
%              Number of equality atoms :  328 (3911 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
     => ( sK3 != X0
        & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3))
        & v3_ordinal1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK2 != X1
          & r4_wellord1(k1_wellord2(sK2),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( sK2 != sK3
    & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f40,f39])).

fof(f59,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK0(X0,X1),sK1(X0,X1))
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( r1_tarski(sK0(X0,X1),sK1(X0,X1))
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK0(X0,X1),sK1(X0,X1))
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( r1_tarski(sK0(X0,X1),sK1(X0,X1))
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & r2_hidden(sK1(X0,X1),X0)
            & r2_hidden(sK0(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f61,plain,(
    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_8733,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_233,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_234,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_8725,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_234])).

cnf(c_8870,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8733,c_8725])).

cnf(c_20,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_8727,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_8728,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8868,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8733,c_8725])).

cnf(c_8945,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8868,c_8725])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_8730,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9003,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8945,c_8730])).

cnf(c_9092,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9003,c_8730])).

cnf(c_9330,plain,
    ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8728,c_9092])).

cnf(c_9362,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_8727,c_9330])).

cnf(c_17,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_829,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_856,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_830,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4637,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_4642,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4637])).

cnf(c_6450,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6451,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6453,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6449,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_234])).

cnf(c_6519,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6453,c_6449])).

cnf(c_6551,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6519,c_6449])).

cnf(c_6452,plain,
    ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6572,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6551,c_6452])).

cnf(c_6604,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6572,c_6452])).

cnf(c_6620,plain,
    ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6451,c_6604])).

cnf(c_6653,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_6450,c_6620])).

cnf(c_9376,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9362,c_17,c_856,c_4642,c_6653])).

cnf(c_9377,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(renaming,[status(thm)],[c_9376])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_118,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_2])).

cnf(c_8726,plain,
    ( k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_118])).

cnf(c_8903,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8733,c_8726])).

cnf(c_8943,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8868,c_8726])).

cnf(c_9069,plain,
    ( X0 = X1
    | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8943,c_8730])).

cnf(c_9111,plain,
    ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),X0) = X0
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8728,c_9069])).

cnf(c_9142,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_8727,c_9111])).

cnf(c_21,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9130,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | sK3 = sK2
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9111])).

cnf(c_9152,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9142,c_21,c_17,c_856,c_4642,c_9130])).

cnf(c_9153,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(renaming,[status(thm)],[c_9152])).

cnf(c_9112,plain,
    ( k2_wellord1(k1_wellord2(X0),sK2) = k1_wellord2(sK2)
    | k1_wellord1(k1_wellord2(sK2),X0) = X0
    | sK2 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8727,c_9069])).

cnf(c_9167,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_8728,c_9112])).

cnf(c_9178,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9167,c_17,c_856,c_4642])).

cnf(c_9179,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(renaming,[status(thm)],[c_9178])).

cnf(c_8902,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8733,c_8726])).

cnf(c_9035,plain,
    ( X0 = X1
    | k1_wellord1(k1_wellord2(X0),X1) = X1
    | k1_wellord1(k1_wellord2(X1),X0) = X0
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8902,c_8726])).

cnf(c_9188,plain,
    ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),X0) = X0
    | sK3 = X0
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8728,c_9035])).

cnf(c_9219,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_8727,c_9188])).

cnf(c_9207,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | sK3 = sK2
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9188])).

cnf(c_9231,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9219,c_21,c_17,c_856,c_4642,c_9207])).

cnf(c_9232,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(renaming,[status(thm)],[c_9231])).

cnf(c_5,negated_conjecture,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,plain,
    ( v2_wellord1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_252,plain,
    ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v3_ordinal1(X2)
    | k1_wellord2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_253,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v1_relat_1(k1_wellord2(X0))
    | ~ v3_ordinal1(X0) ),
    inference(unflattening,[status(thm)],[c_252])).

cnf(c_13,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_257,plain,
    ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ v3_ordinal1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_253,c_13])).

cnf(c_258,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
    | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_257])).

cnf(c_8724,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_258])).

cnf(c_12,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_124,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_13])).

cnf(c_8788,plain,
    ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8724,c_124])).

cnf(c_9235,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9232,c_8788])).

cnf(c_22,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1851,plain,
    ( r2_hidden(X0,sK3)
    | r2_hidden(sK3,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1852,plain,
    ( X0 = sK3
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(sK3,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1851])).

cnf(c_1854,plain,
    ( sK2 = sK3
    | r2_hidden(sK3,sK2) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1852])).

cnf(c_8835,plain,
    ( ~ r2_hidden(sK3,X0)
    | ~ v3_ordinal1(X0)
    | k1_wellord1(k1_wellord2(X0),sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_8840,plain,
    ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
    | r2_hidden(sK3,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8835])).

cnf(c_8842,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r2_hidden(sK3,sK2) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8840])).

cnf(c_9249,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9235,c_21,c_22,c_17,c_1854,c_8842])).

cnf(c_9255,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9179,c_9249])).

cnf(c_18,negated_conjecture,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_8729,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_8732,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8858,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8729,c_8732])).

cnf(c_23,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_36,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_38,plain,
    ( v1_relat_1(k1_wellord2(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_8811,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
    | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
    | ~ v1_relat_1(k1_wellord2(sK3))
    | ~ v1_relat_1(k1_wellord2(sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8812,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8811])).

cnf(c_8928,plain,
    ( v1_relat_1(k1_wellord2(sK3)) != iProver_top
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8858,c_23,c_38,c_8812])).

cnf(c_8929,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8928])).

cnf(c_8731,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8934,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8929,c_8731])).

cnf(c_9267,plain,
    ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9255,c_8934])).

cnf(c_9270,plain,
    ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9267,c_8788])).

cnf(c_9397,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9270,c_21])).

cnf(c_9398,plain,
    ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9397])).

cnf(c_9403,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9153,c_9398])).

cnf(c_9412,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9403,c_23])).

cnf(c_9421,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
    | sK3 = sK2
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8903,c_9412])).

cnf(c_9458,plain,
    ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9421,c_21,c_22,c_17,c_856,c_4642])).

cnf(c_9461,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9458,c_8788])).

cnf(c_9470,plain,
    ( r2_hidden(sK2,sK3) != iProver_top
    | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9461,c_22])).

cnf(c_9471,plain,
    ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_9470])).

cnf(c_9476,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9377,c_9471])).

cnf(c_6503,plain,
    ( ~ r2_hidden(sK3,X0)
    | r1_tarski(sK3,X0)
    | ~ v3_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_6504,plain,
    ( r2_hidden(sK3,X0) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6503])).

cnf(c_6506,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | r1_tarski(sK3,sK2) = iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6504])).

cnf(c_6553,plain,
    ( ~ r1_tarski(sK3,X0)
    | k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6554,plain,
    ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6553])).

cnf(c_6556,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
    | r1_tarski(sK3,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6554])).

cnf(c_9490,plain,
    ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9476,c_21,c_22,c_17,c_1854,c_6506,c_6556,c_8934])).

cnf(c_9493,plain,
    ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9490,c_9398])).

cnf(c_9496,plain,
    ( r2_hidden(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9493,c_23])).

cnf(c_9505,plain,
    ( sK3 = sK2
    | r1_tarski(sK2,sK3) = iProver_top
    | v3_ordinal1(sK3) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8870,c_9496])).

cnf(c_9532,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9505,c_21,c_22,c_17,c_856,c_4642])).

cnf(c_9537,plain,
    ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
    inference(superposition,[status(thm)],[c_9532,c_8730])).

cnf(c_9543,plain,
    ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9537,c_9471])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9543,c_9493,c_8934,c_1854,c_17,c_23,c_22,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.94/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/0.99  
% 3.94/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.94/0.99  
% 3.94/0.99  ------  iProver source info
% 3.94/0.99  
% 3.94/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.94/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.94/0.99  git: non_committed_changes: false
% 3.94/0.99  git: last_make_outside_of_git: false
% 3.94/0.99  
% 3.94/0.99  ------ 
% 3.94/0.99  ------ Parsing...
% 3.94/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  ------ Proving...
% 3.94/0.99  ------ Problem Properties 
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  clauses                                 19
% 3.94/0.99  conjectures                             4
% 3.94/0.99  EPR                                     7
% 3.94/0.99  Horn                                    15
% 3.94/0.99  unary                                   6
% 3.94/0.99  binary                                  1
% 3.94/0.99  lits                                    53
% 3.94/0.99  lits eq                                 9
% 3.94/0.99  fd_pure                                 0
% 3.94/0.99  fd_pseudo                               0
% 3.94/0.99  fd_cond                                 0
% 3.94/0.99  fd_pseudo_cond                          1
% 3.94/0.99  AC symbols                              0
% 3.94/0.99  
% 3.94/0.99  ------ Input Options Time Limit: Unbounded
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.94/0.99  Current options:
% 3.94/0.99  ------ 
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  % SZS status Theorem for theBenchmark.p
% 3.94/0.99  
% 3.94/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.94/0.99  
% 3.94/0.99  fof(f4,axiom,(
% 3.94/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f20,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f4])).
% 3.94/0.99  
% 3.94/0.99  fof(f21,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.94/0.99    inference(flattening,[],[f20])).
% 3.94/0.99  
% 3.94/0.99  fof(f45,plain,(
% 3.94/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f21])).
% 3.94/0.99  
% 3.94/0.99  fof(f1,axiom,(
% 3.94/0.99    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f15,plain,(
% 3.94/0.99    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 3.94/0.99    inference(pure_predicate_removal,[],[f1])).
% 3.94/0.99  
% 3.94/0.99  fof(f16,plain,(
% 3.94/0.99    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f15])).
% 3.94/0.99  
% 3.94/0.99  fof(f42,plain,(
% 3.94/0.99    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f16])).
% 3.94/0.99  
% 3.94/0.99  fof(f2,axiom,(
% 3.94/0.99    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f14,plain,(
% 3.94/0.99    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 3.94/0.99    inference(unused_predicate_definition_removal,[],[f2])).
% 3.94/0.99  
% 3.94/0.99  fof(f17,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f14])).
% 3.94/0.99  
% 3.94/0.99  fof(f43,plain,(
% 3.94/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f17])).
% 3.94/0.99  
% 3.94/0.99  fof(f12,conjecture,(
% 3.94/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f13,negated_conjecture,(
% 3.94/0.99    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 3.94/0.99    inference(negated_conjecture,[],[f12])).
% 3.94/0.99  
% 3.94/0.99  fof(f32,plain,(
% 3.94/0.99    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f13])).
% 3.94/0.99  
% 3.94/0.99  fof(f33,plain,(
% 3.94/0.99    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.94/0.99    inference(flattening,[],[f32])).
% 3.94/0.99  
% 3.94/0.99  fof(f40,plain,(
% 3.94/0.99    ( ! [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK3 != X0 & r4_wellord1(k1_wellord2(X0),k1_wellord2(sK3)) & v3_ordinal1(sK3))) )),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f39,plain,(
% 3.94/0.99    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK2 != X1 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK2))),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f41,plain,(
% 3.94/0.99    (sK2 != sK3 & r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)),
% 3.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f40,f39])).
% 3.94/0.99  
% 3.94/0.99  fof(f59,plain,(
% 3.94/0.99    v3_ordinal1(sK2)),
% 3.94/0.99    inference(cnf_transformation,[],[f41])).
% 3.94/0.99  
% 3.94/0.99  fof(f60,plain,(
% 3.94/0.99    v3_ordinal1(sK3)),
% 3.94/0.99    inference(cnf_transformation,[],[f41])).
% 3.94/0.99  
% 3.94/0.99  fof(f11,axiom,(
% 3.94/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f31,plain,(
% 3.94/0.99    ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1))),
% 3.94/0.99    inference(ennf_transformation,[],[f11])).
% 3.94/0.99  
% 3.94/0.99  fof(f58,plain,(
% 3.94/0.99    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) | ~r1_tarski(X0,X1)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f31])).
% 3.94/0.99  
% 3.94/0.99  fof(f62,plain,(
% 3.94/0.99    sK2 != sK3),
% 3.94/0.99    inference(cnf_transformation,[],[f41])).
% 3.94/0.99  
% 3.94/0.99  fof(f9,axiom,(
% 3.94/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f28,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f9])).
% 3.94/0.99  
% 3.94/0.99  fof(f29,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.94/0.99    inference(flattening,[],[f28])).
% 3.94/0.99  
% 3.94/0.99  fof(f56,plain,(
% 3.94/0.99    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f29])).
% 3.94/0.99  
% 3.94/0.99  fof(f3,axiom,(
% 3.94/0.99    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f18,plain,(
% 3.94/0.99    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 3.94/0.99    inference(ennf_transformation,[],[f3])).
% 3.94/0.99  
% 3.94/0.99  fof(f19,plain,(
% 3.94/0.99    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 3.94/0.99    inference(flattening,[],[f18])).
% 3.94/0.99  
% 3.94/0.99  fof(f44,plain,(
% 3.94/0.99    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f19])).
% 3.94/0.99  
% 3.94/0.99  fof(f6,axiom,(
% 3.94/0.99    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f24,plain,(
% 3.94/0.99    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f6])).
% 3.94/0.99  
% 3.94/0.99  fof(f25,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 3.94/0.99    inference(flattening,[],[f24])).
% 3.94/0.99  
% 3.94/0.99  fof(f47,plain,(
% 3.94/0.99    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f25])).
% 3.94/0.99  
% 3.94/0.99  fof(f10,axiom,(
% 3.94/0.99    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f30,plain,(
% 3.94/0.99    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f10])).
% 3.94/0.99  
% 3.94/0.99  fof(f57,plain,(
% 3.94/0.99    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f30])).
% 3.94/0.99  
% 3.94/0.99  fof(f8,axiom,(
% 3.94/0.99    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f55,plain,(
% 3.94/0.99    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 3.94/0.99    inference(cnf_transformation,[],[f8])).
% 3.94/0.99  
% 3.94/0.99  fof(f7,axiom,(
% 3.94/0.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f26,plain,(
% 3.94/0.99    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 3.94/0.99    inference(ennf_transformation,[],[f7])).
% 3.94/0.99  
% 3.94/0.99  fof(f27,plain,(
% 3.94/0.99    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 3.94/0.99    inference(flattening,[],[f26])).
% 3.94/0.99  
% 3.94/0.99  fof(f34,plain,(
% 3.94/0.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.94/0.99    inference(nnf_transformation,[],[f27])).
% 3.94/0.99  
% 3.94/0.99  fof(f35,plain,(
% 3.94/0.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.94/0.99    inference(flattening,[],[f34])).
% 3.94/0.99  
% 3.94/0.99  fof(f36,plain,(
% 3.94/0.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.94/0.99    inference(rectify,[],[f35])).
% 3.94/0.99  
% 3.94/0.99  fof(f37,plain,(
% 3.94/0.99    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)))),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f38,plain,(
% 3.94/0.99    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 3.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f37])).
% 3.94/0.99  
% 3.94/0.99  fof(f48,plain,(
% 3.94/0.99    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f38])).
% 3.94/0.99  
% 3.94/0.99  fof(f69,plain,(
% 3.94/0.99    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 3.94/0.99    inference(equality_resolution,[],[f48])).
% 3.94/0.99  
% 3.94/0.99  fof(f61,plain,(
% 3.94/0.99    r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))),
% 3.94/0.99    inference(cnf_transformation,[],[f41])).
% 3.94/0.99  
% 3.94/0.99  fof(f5,axiom,(
% 3.94/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f22,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f5])).
% 3.94/0.99  
% 3.94/0.99  fof(f23,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.94/0.99    inference(flattening,[],[f22])).
% 3.94/0.99  
% 3.94/0.99  fof(f46,plain,(
% 3.94/0.99    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f23])).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3,plain,
% 3.94/0.99      ( r2_hidden(X0,X1)
% 3.94/0.99      | r2_hidden(X1,X0)
% 3.94/0.99      | ~ v3_ordinal1(X1)
% 3.94/0.99      | ~ v3_ordinal1(X0)
% 3.94/0.99      | X0 = X1 ),
% 3.94/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8733,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.94/0.99      | r2_hidden(X1,X0) = iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_0,plain,
% 3.94/0.99      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1,plain,
% 3.94/0.99      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,X1) | ~ v1_ordinal1(X1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_233,plain,
% 3.94/0.99      ( ~ r2_hidden(X0,X1)
% 3.94/0.99      | r1_tarski(X0,X1)
% 3.94/0.99      | ~ v3_ordinal1(X2)
% 3.94/0.99      | X1 != X2 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_234,plain,
% 3.94/0.99      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,X1) | ~ v3_ordinal1(X1) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_233]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8725,plain,
% 3.94/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.94/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_234]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8870,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.94/0.99      | r1_tarski(X1,X0) = iProver_top
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8733,c_8725]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_20,negated_conjecture,
% 3.94/0.99      ( v3_ordinal1(sK2) ),
% 3.94/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8727,plain,
% 3.94/0.99      ( v3_ordinal1(sK2) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_19,negated_conjecture,
% 3.94/0.99      ( v3_ordinal1(sK3) ),
% 3.94/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8728,plain,
% 3.94/0.99      ( v3_ordinal1(sK3) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8868,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | r2_hidden(X1,X0) = iProver_top
% 3.94/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8733,c_8725]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8945,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | r1_tarski(X1,X0) = iProver_top
% 3.94/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8868,c_8725]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_16,plain,
% 3.94/0.99      ( ~ r1_tarski(X0,X1)
% 3.94/0.99      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8730,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.94/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9003,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.94/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8945,c_8730]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9092,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.94/0.99      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_9003,c_8730]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9330,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
% 3.94/0.99      | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
% 3.94/0.99      | sK3 = X0
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8728,c_9092]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9362,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.94/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.94/0.99      | sK3 = sK2 ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8727,c_9330]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_17,negated_conjecture,
% 3.94/0.99      ( sK2 != sK3 ),
% 3.94/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_829,plain,( X0 = X0 ),theory(equality) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_856,plain,
% 3.94/0.99      ( sK2 = sK2 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_829]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_830,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4637,plain,
% 3.94/0.99      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_830]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4642,plain,
% 3.94/0.99      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_4637]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6450,plain,
% 3.94/0.99      ( v3_ordinal1(sK2) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6451,plain,
% 3.94/0.99      ( v3_ordinal1(sK3) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6453,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.94/0.99      | r2_hidden(X1,X0) = iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6449,plain,
% 3.94/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.94/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_234]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6519,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | r2_hidden(X1,X0) = iProver_top
% 3.94/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_6453,c_6449]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6551,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | r1_tarski(X1,X0) = iProver_top
% 3.94/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_6519,c_6449]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6452,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.94/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6572,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.94/0.99      | r1_tarski(X0,X1) = iProver_top
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_6551,c_6452]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6604,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | k2_wellord1(k1_wellord2(X0),X1) = k1_wellord2(X1)
% 3.94/0.99      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_6572,c_6452]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6620,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
% 3.94/0.99      | k2_wellord1(k1_wellord2(sK3),X0) = k1_wellord2(X0)
% 3.94/0.99      | sK3 = X0
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_6451,c_6604]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6653,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.94/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.94/0.99      | sK3 = sK2 ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_6450,c_6620]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9376,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.94/0.99      | k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_9362,c_17,c_856,c_4642,c_6653]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9377,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.94/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_9376]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_14,plain,
% 3.94/0.99      ( ~ r2_hidden(X0,X1)
% 3.94/0.99      | ~ v3_ordinal1(X0)
% 3.94/0.99      | ~ v3_ordinal1(X1)
% 3.94/0.99      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 3.94/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2,plain,
% 3.94/0.99      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_118,plain,
% 3.94/0.99      ( ~ r2_hidden(X0,X1)
% 3.94/0.99      | ~ v3_ordinal1(X1)
% 3.94/0.99      | k1_wellord1(k1_wellord2(X1),X0) = X0 ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_14,c_2]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8726,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.94/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_118]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8903,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.94/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8733,c_8726]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8943,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 3.94/0.99      | r1_tarski(X1,X0) = iProver_top
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8868,c_8726]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9069,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | k2_wellord1(k1_wellord2(X1),X0) = k1_wellord2(X0)
% 3.94/0.99      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8943,c_8730]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9111,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
% 3.94/0.99      | k1_wellord1(k1_wellord2(sK3),X0) = X0
% 3.94/0.99      | sK3 = X0
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8728,c_9069]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9142,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.94/0.99      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.94/0.99      | sK3 = sK2 ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8727,c_9111]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_21,plain,
% 3.94/0.99      ( v3_ordinal1(sK2) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9130,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.94/0.99      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.94/0.99      | sK3 = sK2
% 3.94/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_9111]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9152,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.94/0.99      | k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_9142,c_21,c_17,c_856,c_4642,c_9130]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9153,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.94/0.99      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_9152]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9112,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(X0),sK2) = k1_wellord2(sK2)
% 3.94/0.99      | k1_wellord1(k1_wellord2(sK2),X0) = X0
% 3.94/0.99      | sK2 = X0
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8727,c_9069]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9167,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.94/0.99      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.94/0.99      | sK3 = sK2 ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8728,c_9112]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9178,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.94/0.99      | k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_9167,c_17,c_856,c_4642]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9179,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2)
% 3.94/0.99      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_9178]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8902,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 3.94/0.99      | r2_hidden(X1,X0) = iProver_top
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8733,c_8726]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9035,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | k1_wellord1(k1_wellord2(X0),X1) = X1
% 3.94/0.99      | k1_wellord1(k1_wellord2(X1),X0) = X0
% 3.94/0.99      | v3_ordinal1(X1) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8902,c_8726]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9188,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.94/0.99      | k1_wellord1(k1_wellord2(sK3),X0) = X0
% 3.94/0.99      | sK3 = X0
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8728,c_9035]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9219,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.94/0.99      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.94/0.99      | sK3 = sK2 ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8727,c_9188]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9207,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.94/0.99      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.94/0.99      | sK3 = sK2
% 3.94/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_9188]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9231,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.94/0.99      | k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_9219,c_21,c_17,c_856,c_4642,c_9207]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9232,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.94/0.99      | k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_9231]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_5,negated_conjecture,
% 3.94/0.99      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 3.94/0.99      | ~ r2_hidden(X1,k3_relat_1(X0))
% 3.94/0.99      | ~ v2_wellord1(X0)
% 3.94/0.99      | ~ v1_relat_1(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_15,plain,
% 3.94/0.99      ( v2_wellord1(k1_wellord2(X0)) | ~ v3_ordinal1(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_252,plain,
% 3.94/0.99      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
% 3.94/0.99      | ~ r2_hidden(X1,k3_relat_1(X0))
% 3.94/0.99      | ~ v1_relat_1(X0)
% 3.94/0.99      | ~ v3_ordinal1(X2)
% 3.94/0.99      | k1_wellord2(X2) != X0 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_15]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_253,plain,
% 3.94/0.99      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.94/0.99      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.94/0.99      | ~ v1_relat_1(k1_wellord2(X0))
% 3.94/0.99      | ~ v3_ordinal1(X0) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_252]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_13,plain,
% 3.94/0.99      ( v1_relat_1(k1_wellord2(X0)) ),
% 3.94/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_257,plain,
% 3.94/0.99      ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.94/0.99      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.94/0.99      | ~ v3_ordinal1(X0) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_253,c_13]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_258,plain,
% 3.94/0.99      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
% 3.94/0.99      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
% 3.94/0.99      | ~ v3_ordinal1(X0) ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_257]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8724,plain,
% 3.94/0.99      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 3.94/0.99      | r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_258]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_12,plain,
% 3.94/0.99      ( ~ v1_relat_1(k1_wellord2(X0))
% 3.94/0.99      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 3.94/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_124,plain,
% 3.94/0.99      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_12,c_13]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8788,plain,
% 3.94/0.99      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) != iProver_top
% 3.94/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(light_normalisation,[status(thm)],[c_8724,c_124]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9235,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.94/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 3.94/0.99      | r2_hidden(sK2,sK3) != iProver_top
% 3.94/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_9232,c_8788]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_22,plain,
% 3.94/0.99      ( v3_ordinal1(sK3) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1851,plain,
% 3.94/0.99      ( r2_hidden(X0,sK3)
% 3.94/0.99      | r2_hidden(sK3,X0)
% 3.94/0.99      | ~ v3_ordinal1(X0)
% 3.94/0.99      | ~ v3_ordinal1(sK3)
% 3.94/0.99      | X0 = sK3 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1852,plain,
% 3.94/0.99      ( X0 = sK3
% 3.94/0.99      | r2_hidden(X0,sK3) = iProver_top
% 3.94/0.99      | r2_hidden(sK3,X0) = iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top
% 3.94/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1851]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1854,plain,
% 3.94/0.99      ( sK2 = sK3
% 3.94/0.99      | r2_hidden(sK3,sK2) = iProver_top
% 3.94/0.99      | r2_hidden(sK2,sK3) = iProver_top
% 3.94/0.99      | v3_ordinal1(sK3) != iProver_top
% 3.94/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_1852]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8835,plain,
% 3.94/0.99      ( ~ r2_hidden(sK3,X0)
% 3.94/0.99      | ~ v3_ordinal1(X0)
% 3.94/0.99      | k1_wellord1(k1_wellord2(X0),sK3) = sK3 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_118]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8840,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(X0),sK3) = sK3
% 3.94/0.99      | r2_hidden(sK3,X0) != iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_8835]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8842,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.94/0.99      | r2_hidden(sK3,sK2) != iProver_top
% 3.94/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_8840]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9249,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.94/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_9235,c_21,c_22,c_17,c_1854,c_8842]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9255,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3
% 3.94/0.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_9179,c_9249]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_18,negated_conjecture,
% 3.94/0.99      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) ),
% 3.94/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8729,plain,
% 3.94/0.99      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4,plain,
% 3.94/0.99      ( ~ r4_wellord1(X0,X1)
% 3.94/0.99      | r4_wellord1(X1,X0)
% 3.94/0.99      | ~ v1_relat_1(X1)
% 3.94/0.99      | ~ v1_relat_1(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8732,plain,
% 3.94/0.99      ( r4_wellord1(X0,X1) != iProver_top
% 3.94/0.99      | r4_wellord1(X1,X0) = iProver_top
% 3.94/0.99      | v1_relat_1(X0) != iProver_top
% 3.94/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8858,plain,
% 3.94/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
% 3.94/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.94/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8729,c_8732]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_23,plain,
% 3.94/0.99      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_36,plain,
% 3.94/0.99      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_38,plain,
% 3.94/0.99      ( v1_relat_1(k1_wellord2(sK2)) = iProver_top ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_36]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8811,plain,
% 3.94/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2))
% 3.94/0.99      | ~ r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3))
% 3.94/0.99      | ~ v1_relat_1(k1_wellord2(sK3))
% 3.94/0.99      | ~ v1_relat_1(k1_wellord2(sK2)) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8812,plain,
% 3.94/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
% 3.94/0.99      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
% 3.94/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.94/0.99      | v1_relat_1(k1_wellord2(sK2)) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_8811]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8928,plain,
% 3.94/0.99      ( v1_relat_1(k1_wellord2(sK3)) != iProver_top
% 3.94/0.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_8858,c_23,c_38,c_8812]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8929,plain,
% 3.94/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top
% 3.94/0.99      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_8928]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8731,plain,
% 3.94/0.99      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8934,plain,
% 3.94/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) = iProver_top ),
% 3.94/0.99      inference(forward_subsumption_resolution,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_8929,c_8731]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9267,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(sK2),sK3) = sK3 ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_9255,c_8934]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9270,plain,
% 3.94/0.99      ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 3.94/0.99      | r2_hidden(sK3,sK2) != iProver_top
% 3.94/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_9267,c_8788]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9397,plain,
% 3.94/0.99      ( r2_hidden(sK3,sK2) != iProver_top
% 3.94/0.99      | r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_9270,c_21]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9398,plain,
% 3.94/0.99      ( r4_wellord1(k1_wellord2(sK2),k2_wellord1(k1_wellord2(sK2),sK3)) != iProver_top
% 3.94/0.99      | r2_hidden(sK3,sK2) != iProver_top ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_9397]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9403,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.94/0.99      | r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
% 3.94/0.99      | r2_hidden(sK3,sK2) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_9153,c_9398]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9412,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.94/0.99      | r2_hidden(sK3,sK2) != iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_9403,c_23]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9421,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2
% 3.94/0.99      | sK3 = sK2
% 3.94/0.99      | v3_ordinal1(sK3) != iProver_top
% 3.94/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8903,c_9412]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9458,plain,
% 3.94/0.99      ( k1_wellord1(k1_wellord2(sK3),sK2) = sK2 ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_9421,c_21,c_22,c_17,c_856,c_4642]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9461,plain,
% 3.94/0.99      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 3.94/0.99      | r2_hidden(sK2,sK3) != iProver_top
% 3.94/0.99      | v3_ordinal1(sK3) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_9458,c_8788]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9470,plain,
% 3.94/0.99      ( r2_hidden(sK2,sK3) != iProver_top
% 3.94/0.99      | r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_9461,c_22]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9471,plain,
% 3.94/0.99      ( r4_wellord1(k1_wellord2(sK3),k2_wellord1(k1_wellord2(sK3),sK2)) != iProver_top
% 3.94/0.99      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_9470]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9476,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.94/0.99      | r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top
% 3.94/0.99      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_9377,c_9471]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6503,plain,
% 3.94/0.99      ( ~ r2_hidden(sK3,X0) | r1_tarski(sK3,X0) | ~ v3_ordinal1(X0) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_234]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6504,plain,
% 3.94/0.99      ( r2_hidden(sK3,X0) != iProver_top
% 3.94/0.99      | r1_tarski(sK3,X0) = iProver_top
% 3.94/0.99      | v3_ordinal1(X0) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_6503]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6506,plain,
% 3.94/0.99      ( r2_hidden(sK3,sK2) != iProver_top
% 3.94/0.99      | r1_tarski(sK3,sK2) = iProver_top
% 3.94/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_6504]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6553,plain,
% 3.94/0.99      ( ~ r1_tarski(sK3,X0)
% 3.94/0.99      | k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6554,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(X0),sK3) = k1_wellord2(sK3)
% 3.94/0.99      | r1_tarski(sK3,X0) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_6553]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6556,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3)
% 3.94/0.99      | r1_tarski(sK3,sK2) != iProver_top ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_6554]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9490,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(sK2),sK3) = k1_wellord2(sK3) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_9476,c_21,c_22,c_17,c_1854,c_6506,c_6556,c_8934]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9493,plain,
% 3.94/0.99      ( r4_wellord1(k1_wellord2(sK2),k1_wellord2(sK3)) != iProver_top
% 3.94/0.99      | r2_hidden(sK3,sK2) != iProver_top ),
% 3.94/0.99      inference(demodulation,[status(thm)],[c_9490,c_9398]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9496,plain,
% 3.94/0.99      ( r2_hidden(sK3,sK2) != iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_9493,c_23]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9505,plain,
% 3.94/0.99      ( sK3 = sK2
% 3.94/0.99      | r1_tarski(sK2,sK3) = iProver_top
% 3.94/0.99      | v3_ordinal1(sK3) != iProver_top
% 3.94/0.99      | v3_ordinal1(sK2) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_8870,c_9496]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9532,plain,
% 3.94/0.99      ( r1_tarski(sK2,sK3) = iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_9505,c_21,c_22,c_17,c_856,c_4642]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9537,plain,
% 3.94/0.99      ( k2_wellord1(k1_wellord2(sK3),sK2) = k1_wellord2(sK2) ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_9532,c_8730]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_9543,plain,
% 3.94/0.99      ( r4_wellord1(k1_wellord2(sK3),k1_wellord2(sK2)) != iProver_top
% 3.94/0.99      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.94/0.99      inference(demodulation,[status(thm)],[c_9537,c_9471]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(contradiction,plain,
% 3.94/0.99      ( $false ),
% 3.94/0.99      inference(minisat,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_9543,c_9493,c_8934,c_1854,c_17,c_23,c_22,c_21]) ).
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.94/0.99  
% 3.94/0.99  ------                               Statistics
% 3.94/0.99  
% 3.94/0.99  ------ Selected
% 3.94/0.99  
% 3.94/0.99  total_time:                             0.192
% 3.94/0.99  
%------------------------------------------------------------------------------
