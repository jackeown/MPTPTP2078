%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:35 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 174 expanded)
%              Number of clauses        :   53 (  58 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   20
%              Number of atoms          :  380 ( 868 expanded)
%              Number of equality atoms :   84 ( 121 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ~ ( ! [X2] :
              ( v3_ordinal1(X2)
             => ~ ( ! [X3] :
                      ( v3_ordinal1(X3)
                     => ( r2_hidden(X3,X0)
                       => r1_ordinal1(X2,X3) ) )
                  & r2_hidden(X2,X0) ) )
          & k1_xboole_0 != X0
          & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ~ ( ! [X2] :
                ( v3_ordinal1(X2)
               => ~ ( ! [X3] :
                        ( v3_ordinal1(X3)
                       => ( r2_hidden(X3,X0)
                         => r1_ordinal1(X2,X3) ) )
                    & r2_hidden(X2,X0) ) )
            & k1_xboole_0 != X0
            & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
    ! [X0,X2] :
      ( ? [X3] :
          ( ~ r1_ordinal1(X2,X3)
          & r2_hidden(X3,X0)
          & v3_ordinal1(X3) )
     => ( ~ r1_ordinal1(X2,sK6(X2))
        & r2_hidden(sK6(X2),X0)
        & v3_ordinal1(sK6(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( ~ r1_ordinal1(X2,X3)
                & r2_hidden(X3,X0)
                & v3_ordinal1(X3) )
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1)
        & v3_ordinal1(X1) )
   => ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,sK4)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,sK4)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != sK4
      & r1_tarski(sK4,sK5)
      & v3_ordinal1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ! [X2] :
        ( ( ~ r1_ordinal1(X2,sK6(X2))
          & r2_hidden(sK6(X2),sK4)
          & v3_ordinal1(sK6(X2)) )
        | ~ r2_hidden(X2,sK4)
        | ~ v3_ordinal1(X2) )
    & k1_xboole_0 != sK4
    & r1_tarski(sK4,sK5)
    & v3_ordinal1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f37,f36])).

fof(f56,plain,(
    ! [X2] :
      ( r2_hidden(sK6(X2),sK4)
      | ~ r2_hidden(X2,sK4)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2] :
      ( ~ r1_ordinal1(X2,sK6(X2))
      | ~ r2_hidden(X2,sK4)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    ! [X2] :
      ( v3_ordinal1(sK6(X2))
      | ~ r2_hidden(X2,sK4)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f32])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK2(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f53,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(k1_zfmisc_1(X2),X1) )
      & ! [X2,X3] :
          ( ( r1_tarski(X3,X2)
            & r2_hidden(X2,X1) )
         => r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(k1_zfmisc_1(X3),X1) )
      & ! [X4,X5] :
          ( ( r1_tarski(X5,X4)
            & r2_hidden(X4,X1) )
         => r2_hidden(X5,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f2])).

fof(f11,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(k1_zfmisc_1(X3),X1) )
      & ! [X4,X5] :
          ( ( r1_tarski(X5,X4)
            & r2_hidden(X4,X1) )
         => r2_hidden(X5,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f13,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X3] :
          ( r2_hidden(k1_zfmisc_1(X3),X1)
          | ~ r2_hidden(X3,X1) )
      & ! [X4,X5] :
          ( r2_hidden(X5,X1)
          | ~ r1_tarski(X5,X4)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f14,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X3] :
          ( r2_hidden(k1_zfmisc_1(X3),X1)
          | ~ r2_hidden(X3,X1) )
      & ! [X4,X5] :
          ( r2_hidden(X5,X1)
          | ~ r1_tarski(X5,X4)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(k1_zfmisc_1(X2),X1)
          | ~ r2_hidden(X2,X1) )
      & ! [X3,X4] :
          ( r2_hidden(X4,X1)
          | ~ r1_tarski(X4,X3)
          | ~ r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_zfmisc_1(X2),X1)
              | ~ r2_hidden(X2,X1) )
          & ! [X3,X4] :
              ( r2_hidden(X4,X1)
              | ~ r1_tarski(X4,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X0,X1) )
     => ( ! [X2] :
            ( r2_hidden(k1_zfmisc_1(X2),sK1(X0))
            | ~ r2_hidden(X2,sK1(X0)) )
        & ! [X4,X3] :
            ( r2_hidden(X4,sK1(X0))
            | ~ r1_tarski(X4,X3)
            | ~ r2_hidden(X3,sK1(X0)) )
        & r2_hidden(X0,sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X2] :
          ( r2_hidden(k1_zfmisc_1(X2),sK1(X0))
          | ~ r2_hidden(X2,sK1(X0)) )
      & ! [X3,X4] :
          ( r2_hidden(X4,sK1(X0))
          | ~ r1_tarski(X4,X3)
          | ~ r2_hidden(X3,sK1(X0)) )
      & r2_hidden(X0,sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f42,plain,(
    ! [X0] : r2_hidden(X0,sK1(X0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X2,X0)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_9,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | r1_tarski(X1,k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_632,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK3(X0,X1),X0) = iProver_top
    | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(sK6(X0),sK4)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_629,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK6(X0),sK4) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_13,negated_conjecture,
    ( ~ r1_ordinal1(X0,sK6(X0))
    | ~ r2_hidden(X0,sK4)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_196,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,sK4)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | X2 != X1
    | sK6(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_197,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(sK6(X0),X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK6(X0)) ),
    inference(unflattening,[status(thm)],[c_196])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ v3_ordinal1(X0)
    | v3_ordinal1(sK6(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_199,plain,
    ( ~ v3_ordinal1(X0)
    | r2_hidden(sK6(X0),X0)
    | ~ r2_hidden(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_197,c_15])).

cnf(c_200,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(sK6(X0),X0)
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_199])).

cnf(c_625,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK6(X0),X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_200])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,sK2(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_635,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,sK2(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3267,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK6(sK2(X1)),X1) != iProver_top
    | r2_hidden(sK2(X1),sK4) != iProver_top
    | v3_ordinal1(sK2(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_625,c_635])).

cnf(c_4050,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK2(sK4),sK4) != iProver_top
    | v3_ordinal1(sK2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_3267])).

cnf(c_18,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_19,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1416,plain,
    ( ~ r2_hidden(sK2(X0),X0)
    | r2_hidden(sK2(X0),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2812,plain,
    ( ~ r2_hidden(sK2(X0),X0)
    | r2_hidden(sK2(X0),sK5)
    | ~ r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_1416])).

cnf(c_2814,plain,
    ( r2_hidden(sK2(X0),X0) != iProver_top
    | r2_hidden(sK2(X0),sK5) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2812])).

cnf(c_2816,plain,
    ( r2_hidden(sK2(sK4),sK5) = iProver_top
    | r2_hidden(sK2(sK4),sK4) != iProver_top
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2814])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_785,plain,
    ( ~ r2_hidden(X0,sK5)
    | v3_ordinal1(X0)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2813,plain,
    ( ~ r2_hidden(sK2(X0),sK5)
    | v3_ordinal1(sK2(X0))
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_2818,plain,
    ( r2_hidden(sK2(X0),sK5) != iProver_top
    | v3_ordinal1(sK2(X0)) = iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2813])).

cnf(c_2820,plain,
    ( r2_hidden(sK2(sK4),sK5) != iProver_top
    | v3_ordinal1(sK2(sK4)) = iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2818])).

cnf(c_4099,plain,
    ( r2_hidden(sK2(sK4),sK4) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4050,c_19,c_20,c_2816,c_2820])).

cnf(c_4100,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK2(sK4),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4099])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(X1),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_634,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK2(X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4105,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4100,c_634])).

cnf(c_4108,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(X0,k1_setfam_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_632,c_4105])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_331,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_861,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_911,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_330,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_912,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_4344,plain,
    ( r1_tarski(X0,k1_setfam_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4108,c_16,c_911,c_912])).

cnf(c_5,plain,
    ( r2_hidden(X0,sK1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_636,plain,
    ( r2_hidden(X0,sK1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_639,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2200,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(sK1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_636,c_639])).

cnf(c_4665,plain,
    ( r2_hidden(X0,k1_setfam_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4344,c_2200])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_630,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1119,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK1(X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_636,c_630])).

cnf(c_4190,plain,
    ( r2_hidden(sK1(sK1(X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_636,c_1119])).

cnf(c_7486,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4665,c_4190])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n015.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 17:16:08 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 2.56/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/0.97  
% 2.56/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.56/0.97  
% 2.56/0.97  ------  iProver source info
% 2.56/0.97  
% 2.56/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.56/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.56/0.97  git: non_committed_changes: false
% 2.56/0.97  git: last_make_outside_of_git: false
% 2.56/0.97  
% 2.56/0.97  ------ 
% 2.56/0.97  
% 2.56/0.97  ------ Input Options
% 2.56/0.97  
% 2.56/0.97  --out_options                           all
% 2.56/0.97  --tptp_safe_out                         true
% 2.56/0.97  --problem_path                          ""
% 2.56/0.97  --include_path                          ""
% 2.56/0.97  --clausifier                            res/vclausify_rel
% 2.56/0.97  --clausifier_options                    --mode clausify
% 2.56/0.97  --stdin                                 false
% 2.56/0.97  --stats_out                             all
% 2.56/0.97  
% 2.56/0.97  ------ General Options
% 2.56/0.97  
% 2.56/0.97  --fof                                   false
% 2.56/0.97  --time_out_real                         305.
% 2.56/0.97  --time_out_virtual                      -1.
% 2.56/0.97  --symbol_type_check                     false
% 2.56/0.97  --clausify_out                          false
% 2.56/0.97  --sig_cnt_out                           false
% 2.56/0.97  --trig_cnt_out                          false
% 2.56/0.97  --trig_cnt_out_tolerance                1.
% 2.56/0.97  --trig_cnt_out_sk_spl                   false
% 2.56/0.97  --abstr_cl_out                          false
% 2.56/0.97  
% 2.56/0.97  ------ Global Options
% 2.56/0.97  
% 2.56/0.97  --schedule                              default
% 2.56/0.97  --add_important_lit                     false
% 2.56/0.97  --prop_solver_per_cl                    1000
% 2.56/0.97  --min_unsat_core                        false
% 2.56/0.97  --soft_assumptions                      false
% 2.56/0.97  --soft_lemma_size                       3
% 2.56/0.97  --prop_impl_unit_size                   0
% 2.56/0.97  --prop_impl_unit                        []
% 2.56/0.97  --share_sel_clauses                     true
% 2.56/0.97  --reset_solvers                         false
% 2.56/0.97  --bc_imp_inh                            [conj_cone]
% 2.56/0.97  --conj_cone_tolerance                   3.
% 2.56/0.97  --extra_neg_conj                        none
% 2.56/0.97  --large_theory_mode                     true
% 2.56/0.97  --prolific_symb_bound                   200
% 2.56/0.97  --lt_threshold                          2000
% 2.56/0.97  --clause_weak_htbl                      true
% 2.56/0.97  --gc_record_bc_elim                     false
% 2.56/0.97  
% 2.56/0.97  ------ Preprocessing Options
% 2.56/0.97  
% 2.56/0.97  --preprocessing_flag                    true
% 2.56/0.97  --time_out_prep_mult                    0.1
% 2.56/0.97  --splitting_mode                        input
% 2.56/0.97  --splitting_grd                         true
% 2.56/0.97  --splitting_cvd                         false
% 2.56/0.97  --splitting_cvd_svl                     false
% 2.56/0.97  --splitting_nvd                         32
% 2.56/0.97  --sub_typing                            true
% 2.56/0.97  --prep_gs_sim                           true
% 2.56/0.97  --prep_unflatten                        true
% 2.56/0.97  --prep_res_sim                          true
% 2.56/0.97  --prep_upred                            true
% 2.56/0.97  --prep_sem_filter                       exhaustive
% 2.56/0.97  --prep_sem_filter_out                   false
% 2.56/0.97  --pred_elim                             true
% 2.56/0.97  --res_sim_input                         true
% 2.56/0.97  --eq_ax_congr_red                       true
% 2.56/0.97  --pure_diseq_elim                       true
% 2.56/0.97  --brand_transform                       false
% 2.56/0.97  --non_eq_to_eq                          false
% 2.56/0.97  --prep_def_merge                        true
% 2.56/0.97  --prep_def_merge_prop_impl              false
% 2.56/0.97  --prep_def_merge_mbd                    true
% 2.56/0.97  --prep_def_merge_tr_red                 false
% 2.56/0.97  --prep_def_merge_tr_cl                  false
% 2.56/0.97  --smt_preprocessing                     true
% 2.56/0.97  --smt_ac_axioms                         fast
% 2.56/0.97  --preprocessed_out                      false
% 2.56/0.97  --preprocessed_stats                    false
% 2.56/0.97  
% 2.56/0.97  ------ Abstraction refinement Options
% 2.56/0.97  
% 2.56/0.97  --abstr_ref                             []
% 2.56/0.97  --abstr_ref_prep                        false
% 2.56/0.97  --abstr_ref_until_sat                   false
% 2.56/0.97  --abstr_ref_sig_restrict                funpre
% 2.56/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/0.97  --abstr_ref_under                       []
% 2.56/0.97  
% 2.56/0.97  ------ SAT Options
% 2.56/0.97  
% 2.56/0.97  --sat_mode                              false
% 2.56/0.97  --sat_fm_restart_options                ""
% 2.56/0.97  --sat_gr_def                            false
% 2.56/0.97  --sat_epr_types                         true
% 2.56/0.97  --sat_non_cyclic_types                  false
% 2.56/0.97  --sat_finite_models                     false
% 2.56/0.97  --sat_fm_lemmas                         false
% 2.56/0.97  --sat_fm_prep                           false
% 2.56/0.97  --sat_fm_uc_incr                        true
% 2.56/0.97  --sat_out_model                         small
% 2.56/0.97  --sat_out_clauses                       false
% 2.56/0.97  
% 2.56/0.97  ------ QBF Options
% 2.56/0.97  
% 2.56/0.97  --qbf_mode                              false
% 2.56/0.97  --qbf_elim_univ                         false
% 2.56/0.97  --qbf_dom_inst                          none
% 2.56/0.97  --qbf_dom_pre_inst                      false
% 2.56/0.97  --qbf_sk_in                             false
% 2.56/0.97  --qbf_pred_elim                         true
% 2.56/0.97  --qbf_split                             512
% 2.56/0.97  
% 2.56/0.97  ------ BMC1 Options
% 2.56/0.97  
% 2.56/0.97  --bmc1_incremental                      false
% 2.56/0.97  --bmc1_axioms                           reachable_all
% 2.56/0.97  --bmc1_min_bound                        0
% 2.56/0.97  --bmc1_max_bound                        -1
% 2.56/0.97  --bmc1_max_bound_default                -1
% 2.56/0.97  --bmc1_symbol_reachability              true
% 2.56/0.97  --bmc1_property_lemmas                  false
% 2.56/0.97  --bmc1_k_induction                      false
% 2.56/0.97  --bmc1_non_equiv_states                 false
% 2.56/0.97  --bmc1_deadlock                         false
% 2.56/0.97  --bmc1_ucm                              false
% 2.56/0.97  --bmc1_add_unsat_core                   none
% 2.56/0.97  --bmc1_unsat_core_children              false
% 2.56/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/0.97  --bmc1_out_stat                         full
% 2.56/0.97  --bmc1_ground_init                      false
% 2.56/0.97  --bmc1_pre_inst_next_state              false
% 2.56/0.97  --bmc1_pre_inst_state                   false
% 2.56/0.97  --bmc1_pre_inst_reach_state             false
% 2.56/0.97  --bmc1_out_unsat_core                   false
% 2.56/0.97  --bmc1_aig_witness_out                  false
% 2.56/0.97  --bmc1_verbose                          false
% 2.56/0.97  --bmc1_dump_clauses_tptp                false
% 2.56/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.56/0.97  --bmc1_dump_file                        -
% 2.56/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.56/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.56/0.97  --bmc1_ucm_extend_mode                  1
% 2.56/0.97  --bmc1_ucm_init_mode                    2
% 2.56/0.97  --bmc1_ucm_cone_mode                    none
% 2.56/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.56/0.97  --bmc1_ucm_relax_model                  4
% 2.56/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.56/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/0.97  --bmc1_ucm_layered_model                none
% 2.56/0.97  --bmc1_ucm_max_lemma_size               10
% 2.56/0.97  
% 2.56/0.97  ------ AIG Options
% 2.56/0.97  
% 2.56/0.97  --aig_mode                              false
% 2.56/0.97  
% 2.56/0.97  ------ Instantiation Options
% 2.56/0.97  
% 2.56/0.97  --instantiation_flag                    true
% 2.56/0.97  --inst_sos_flag                         false
% 2.56/0.97  --inst_sos_phase                        true
% 2.56/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/0.97  --inst_lit_sel_side                     num_symb
% 2.56/0.97  --inst_solver_per_active                1400
% 2.56/0.97  --inst_solver_calls_frac                1.
% 2.56/0.97  --inst_passive_queue_type               priority_queues
% 2.56/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/0.97  --inst_passive_queues_freq              [25;2]
% 2.56/0.97  --inst_dismatching                      true
% 2.56/0.97  --inst_eager_unprocessed_to_passive     true
% 2.56/0.97  --inst_prop_sim_given                   true
% 2.56/0.97  --inst_prop_sim_new                     false
% 2.56/0.97  --inst_subs_new                         false
% 2.56/0.97  --inst_eq_res_simp                      false
% 2.56/0.97  --inst_subs_given                       false
% 2.56/0.97  --inst_orphan_elimination               true
% 2.56/0.97  --inst_learning_loop_flag               true
% 2.56/0.97  --inst_learning_start                   3000
% 2.56/0.97  --inst_learning_factor                  2
% 2.56/0.97  --inst_start_prop_sim_after_learn       3
% 2.56/0.97  --inst_sel_renew                        solver
% 2.56/0.97  --inst_lit_activity_flag                true
% 2.56/0.97  --inst_restr_to_given                   false
% 2.56/0.97  --inst_activity_threshold               500
% 2.56/0.97  --inst_out_proof                        true
% 2.56/0.97  
% 2.56/0.97  ------ Resolution Options
% 2.56/0.97  
% 2.56/0.97  --resolution_flag                       true
% 2.56/0.97  --res_lit_sel                           adaptive
% 2.56/0.97  --res_lit_sel_side                      none
% 2.56/0.97  --res_ordering                          kbo
% 2.56/0.97  --res_to_prop_solver                    active
% 2.56/0.97  --res_prop_simpl_new                    false
% 2.56/0.97  --res_prop_simpl_given                  true
% 2.56/0.97  --res_passive_queue_type                priority_queues
% 2.56/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/0.97  --res_passive_queues_freq               [15;5]
% 2.56/0.97  --res_forward_subs                      full
% 2.56/0.97  --res_backward_subs                     full
% 2.56/0.97  --res_forward_subs_resolution           true
% 2.56/0.97  --res_backward_subs_resolution          true
% 2.56/0.97  --res_orphan_elimination                true
% 2.56/0.97  --res_time_limit                        2.
% 2.56/0.97  --res_out_proof                         true
% 2.56/0.97  
% 2.56/0.97  ------ Superposition Options
% 2.56/0.97  
% 2.56/0.97  --superposition_flag                    true
% 2.56/0.97  --sup_passive_queue_type                priority_queues
% 2.56/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.56/0.97  --demod_completeness_check              fast
% 2.56/0.97  --demod_use_ground                      true
% 2.56/0.97  --sup_to_prop_solver                    passive
% 2.56/0.97  --sup_prop_simpl_new                    true
% 2.56/0.97  --sup_prop_simpl_given                  true
% 2.56/0.97  --sup_fun_splitting                     false
% 2.56/0.97  --sup_smt_interval                      50000
% 2.56/0.97  
% 2.56/0.97  ------ Superposition Simplification Setup
% 2.56/0.97  
% 2.56/0.97  --sup_indices_passive                   []
% 2.56/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.97  --sup_full_bw                           [BwDemod]
% 2.56/0.97  --sup_immed_triv                        [TrivRules]
% 2.56/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.97  --sup_immed_bw_main                     []
% 2.56/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.97  
% 2.56/0.97  ------ Combination Options
% 2.56/0.97  
% 2.56/0.97  --comb_res_mult                         3
% 2.56/0.97  --comb_sup_mult                         2
% 2.56/0.97  --comb_inst_mult                        10
% 2.56/0.97  
% 2.56/0.97  ------ Debug Options
% 2.56/0.97  
% 2.56/0.97  --dbg_backtrace                         false
% 2.56/0.97  --dbg_dump_prop_clauses                 false
% 2.56/0.97  --dbg_dump_prop_clauses_file            -
% 2.56/0.97  --dbg_out_stat                          false
% 2.56/0.97  ------ Parsing...
% 2.56/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.56/0.97  
% 2.56/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.56/0.97  
% 2.56/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.56/0.97  
% 2.56/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.56/0.97  ------ Proving...
% 2.56/0.97  ------ Problem Properties 
% 2.56/0.97  
% 2.56/0.97  
% 2.56/0.97  clauses                                 18
% 2.56/0.97  conjectures                             5
% 2.56/0.97  EPR                                     6
% 2.56/0.97  Horn                                    15
% 2.56/0.97  unary                                   4
% 2.56/0.97  binary                                  4
% 2.56/0.97  lits                                    42
% 2.56/0.97  lits eq                                 3
% 2.56/0.97  fd_pure                                 0
% 2.56/0.97  fd_pseudo                               0
% 2.56/0.97  fd_cond                                 2
% 2.56/0.97  fd_pseudo_cond                          0
% 2.56/0.97  AC symbols                              0
% 2.56/0.97  
% 2.56/0.97  ------ Schedule dynamic 5 is on 
% 2.56/0.97  
% 2.56/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.56/0.97  
% 2.56/0.97  
% 2.56/0.97  ------ 
% 2.56/0.97  Current options:
% 2.56/0.97  ------ 
% 2.56/0.97  
% 2.56/0.97  ------ Input Options
% 2.56/0.97  
% 2.56/0.97  --out_options                           all
% 2.56/0.97  --tptp_safe_out                         true
% 2.56/0.97  --problem_path                          ""
% 2.56/0.97  --include_path                          ""
% 2.56/0.97  --clausifier                            res/vclausify_rel
% 2.56/0.97  --clausifier_options                    --mode clausify
% 2.56/0.97  --stdin                                 false
% 2.56/0.97  --stats_out                             all
% 2.56/0.97  
% 2.56/0.97  ------ General Options
% 2.56/0.97  
% 2.56/0.97  --fof                                   false
% 2.56/0.97  --time_out_real                         305.
% 2.56/0.97  --time_out_virtual                      -1.
% 2.56/0.97  --symbol_type_check                     false
% 2.56/0.97  --clausify_out                          false
% 2.56/0.97  --sig_cnt_out                           false
% 2.56/0.97  --trig_cnt_out                          false
% 2.56/0.97  --trig_cnt_out_tolerance                1.
% 2.56/0.97  --trig_cnt_out_sk_spl                   false
% 2.56/0.97  --abstr_cl_out                          false
% 2.56/0.97  
% 2.56/0.97  ------ Global Options
% 2.56/0.97  
% 2.56/0.97  --schedule                              default
% 2.56/0.97  --add_important_lit                     false
% 2.56/0.97  --prop_solver_per_cl                    1000
% 2.56/0.97  --min_unsat_core                        false
% 2.56/0.97  --soft_assumptions                      false
% 2.56/0.97  --soft_lemma_size                       3
% 2.56/0.97  --prop_impl_unit_size                   0
% 2.56/0.97  --prop_impl_unit                        []
% 2.56/0.97  --share_sel_clauses                     true
% 2.56/0.97  --reset_solvers                         false
% 2.56/0.97  --bc_imp_inh                            [conj_cone]
% 2.56/0.97  --conj_cone_tolerance                   3.
% 2.56/0.97  --extra_neg_conj                        none
% 2.56/0.97  --large_theory_mode                     true
% 2.56/0.97  --prolific_symb_bound                   200
% 2.56/0.97  --lt_threshold                          2000
% 2.56/0.97  --clause_weak_htbl                      true
% 2.56/0.97  --gc_record_bc_elim                     false
% 2.56/0.97  
% 2.56/0.97  ------ Preprocessing Options
% 2.56/0.97  
% 2.56/0.97  --preprocessing_flag                    true
% 2.56/0.97  --time_out_prep_mult                    0.1
% 2.56/0.97  --splitting_mode                        input
% 2.56/0.97  --splitting_grd                         true
% 2.56/0.97  --splitting_cvd                         false
% 2.56/0.97  --splitting_cvd_svl                     false
% 2.56/0.97  --splitting_nvd                         32
% 2.56/0.97  --sub_typing                            true
% 2.56/0.97  --prep_gs_sim                           true
% 2.56/0.97  --prep_unflatten                        true
% 2.56/0.97  --prep_res_sim                          true
% 2.56/0.97  --prep_upred                            true
% 2.56/0.97  --prep_sem_filter                       exhaustive
% 2.56/0.97  --prep_sem_filter_out                   false
% 2.56/0.97  --pred_elim                             true
% 2.56/0.97  --res_sim_input                         true
% 2.56/0.97  --eq_ax_congr_red                       true
% 2.56/0.97  --pure_diseq_elim                       true
% 2.56/0.97  --brand_transform                       false
% 2.56/0.97  --non_eq_to_eq                          false
% 2.56/0.97  --prep_def_merge                        true
% 2.56/0.97  --prep_def_merge_prop_impl              false
% 2.56/0.97  --prep_def_merge_mbd                    true
% 2.56/0.97  --prep_def_merge_tr_red                 false
% 2.56/0.97  --prep_def_merge_tr_cl                  false
% 2.56/0.97  --smt_preprocessing                     true
% 2.56/0.97  --smt_ac_axioms                         fast
% 2.56/0.97  --preprocessed_out                      false
% 2.56/0.97  --preprocessed_stats                    false
% 2.56/0.97  
% 2.56/0.97  ------ Abstraction refinement Options
% 2.56/0.97  
% 2.56/0.97  --abstr_ref                             []
% 2.56/0.97  --abstr_ref_prep                        false
% 2.56/0.97  --abstr_ref_until_sat                   false
% 2.56/0.97  --abstr_ref_sig_restrict                funpre
% 2.56/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/0.97  --abstr_ref_under                       []
% 2.56/0.97  
% 2.56/0.97  ------ SAT Options
% 2.56/0.97  
% 2.56/0.97  --sat_mode                              false
% 2.56/0.97  --sat_fm_restart_options                ""
% 2.56/0.97  --sat_gr_def                            false
% 2.56/0.97  --sat_epr_types                         true
% 2.56/0.97  --sat_non_cyclic_types                  false
% 2.56/0.97  --sat_finite_models                     false
% 2.56/0.97  --sat_fm_lemmas                         false
% 2.56/0.97  --sat_fm_prep                           false
% 2.56/0.97  --sat_fm_uc_incr                        true
% 2.56/0.97  --sat_out_model                         small
% 2.56/0.97  --sat_out_clauses                       false
% 2.56/0.97  
% 2.56/0.97  ------ QBF Options
% 2.56/0.97  
% 2.56/0.97  --qbf_mode                              false
% 2.56/0.97  --qbf_elim_univ                         false
% 2.56/0.97  --qbf_dom_inst                          none
% 2.56/0.97  --qbf_dom_pre_inst                      false
% 2.56/0.97  --qbf_sk_in                             false
% 2.56/0.97  --qbf_pred_elim                         true
% 2.56/0.97  --qbf_split                             512
% 2.56/0.97  
% 2.56/0.97  ------ BMC1 Options
% 2.56/0.97  
% 2.56/0.97  --bmc1_incremental                      false
% 2.56/0.97  --bmc1_axioms                           reachable_all
% 2.56/0.97  --bmc1_min_bound                        0
% 2.56/0.97  --bmc1_max_bound                        -1
% 2.56/0.97  --bmc1_max_bound_default                -1
% 2.56/0.97  --bmc1_symbol_reachability              true
% 2.56/0.97  --bmc1_property_lemmas                  false
% 2.56/0.97  --bmc1_k_induction                      false
% 2.56/0.97  --bmc1_non_equiv_states                 false
% 2.56/0.97  --bmc1_deadlock                         false
% 2.56/0.97  --bmc1_ucm                              false
% 2.56/0.97  --bmc1_add_unsat_core                   none
% 2.56/0.97  --bmc1_unsat_core_children              false
% 2.56/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/0.97  --bmc1_out_stat                         full
% 2.56/0.97  --bmc1_ground_init                      false
% 2.56/0.97  --bmc1_pre_inst_next_state              false
% 2.56/0.97  --bmc1_pre_inst_state                   false
% 2.56/0.97  --bmc1_pre_inst_reach_state             false
% 2.56/0.97  --bmc1_out_unsat_core                   false
% 2.56/0.97  --bmc1_aig_witness_out                  false
% 2.56/0.97  --bmc1_verbose                          false
% 2.56/0.97  --bmc1_dump_clauses_tptp                false
% 2.56/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.56/0.97  --bmc1_dump_file                        -
% 2.56/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.56/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.56/0.97  --bmc1_ucm_extend_mode                  1
% 2.56/0.97  --bmc1_ucm_init_mode                    2
% 2.56/0.97  --bmc1_ucm_cone_mode                    none
% 2.56/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.56/0.97  --bmc1_ucm_relax_model                  4
% 2.56/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.56/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/0.97  --bmc1_ucm_layered_model                none
% 2.56/0.97  --bmc1_ucm_max_lemma_size               10
% 2.56/0.97  
% 2.56/0.97  ------ AIG Options
% 2.56/0.97  
% 2.56/0.97  --aig_mode                              false
% 2.56/0.97  
% 2.56/0.97  ------ Instantiation Options
% 2.56/0.97  
% 2.56/0.97  --instantiation_flag                    true
% 2.56/0.97  --inst_sos_flag                         false
% 2.56/0.97  --inst_sos_phase                        true
% 2.56/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/0.97  --inst_lit_sel_side                     none
% 2.56/0.97  --inst_solver_per_active                1400
% 2.56/0.97  --inst_solver_calls_frac                1.
% 2.56/0.97  --inst_passive_queue_type               priority_queues
% 2.56/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/0.97  --inst_passive_queues_freq              [25;2]
% 2.56/0.97  --inst_dismatching                      true
% 2.56/0.97  --inst_eager_unprocessed_to_passive     true
% 2.56/0.97  --inst_prop_sim_given                   true
% 2.56/0.97  --inst_prop_sim_new                     false
% 2.56/0.97  --inst_subs_new                         false
% 2.56/0.97  --inst_eq_res_simp                      false
% 2.56/0.97  --inst_subs_given                       false
% 2.56/0.97  --inst_orphan_elimination               true
% 2.56/0.97  --inst_learning_loop_flag               true
% 2.56/0.97  --inst_learning_start                   3000
% 2.56/0.97  --inst_learning_factor                  2
% 2.56/0.97  --inst_start_prop_sim_after_learn       3
% 2.56/0.97  --inst_sel_renew                        solver
% 2.56/0.97  --inst_lit_activity_flag                true
% 2.56/0.97  --inst_restr_to_given                   false
% 2.56/0.97  --inst_activity_threshold               500
% 2.56/0.97  --inst_out_proof                        true
% 2.56/0.97  
% 2.56/0.97  ------ Resolution Options
% 2.56/0.97  
% 2.56/0.97  --resolution_flag                       false
% 2.56/0.97  --res_lit_sel                           adaptive
% 2.56/0.97  --res_lit_sel_side                      none
% 2.56/0.97  --res_ordering                          kbo
% 2.56/0.97  --res_to_prop_solver                    active
% 2.56/0.97  --res_prop_simpl_new                    false
% 2.56/0.97  --res_prop_simpl_given                  true
% 2.56/0.97  --res_passive_queue_type                priority_queues
% 2.56/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/0.97  --res_passive_queues_freq               [15;5]
% 2.56/0.97  --res_forward_subs                      full
% 2.56/0.97  --res_backward_subs                     full
% 2.56/0.97  --res_forward_subs_resolution           true
% 2.56/0.97  --res_backward_subs_resolution          true
% 2.56/0.97  --res_orphan_elimination                true
% 2.56/0.97  --res_time_limit                        2.
% 2.56/0.97  --res_out_proof                         true
% 2.56/0.97  
% 2.56/0.97  ------ Superposition Options
% 2.56/0.97  
% 2.56/0.97  --superposition_flag                    true
% 2.56/0.97  --sup_passive_queue_type                priority_queues
% 2.56/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.56/0.97  --demod_completeness_check              fast
% 2.56/0.97  --demod_use_ground                      true
% 2.56/0.97  --sup_to_prop_solver                    passive
% 2.56/0.97  --sup_prop_simpl_new                    true
% 2.56/0.97  --sup_prop_simpl_given                  true
% 2.56/0.97  --sup_fun_splitting                     false
% 2.56/0.97  --sup_smt_interval                      50000
% 2.56/0.97  
% 2.56/0.97  ------ Superposition Simplification Setup
% 2.56/0.97  
% 2.56/0.97  --sup_indices_passive                   []
% 2.56/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.97  --sup_full_bw                           [BwDemod]
% 2.56/0.97  --sup_immed_triv                        [TrivRules]
% 2.56/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.97  --sup_immed_bw_main                     []
% 2.56/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.97  
% 2.56/0.97  ------ Combination Options
% 2.56/0.97  
% 2.56/0.97  --comb_res_mult                         3
% 2.56/0.97  --comb_sup_mult                         2
% 2.56/0.97  --comb_inst_mult                        10
% 2.56/0.97  
% 2.56/0.97  ------ Debug Options
% 2.56/0.97  
% 2.56/0.97  --dbg_backtrace                         false
% 2.56/0.97  --dbg_dump_prop_clauses                 false
% 2.56/0.97  --dbg_dump_prop_clauses_file            -
% 2.56/0.97  --dbg_out_stat                          false
% 2.56/0.97  
% 2.56/0.97  
% 2.56/0.97  
% 2.56/0.97  
% 2.56/0.97  ------ Proving...
% 2.56/0.97  
% 2.56/0.97  
% 2.56/0.97  % SZS status Theorem for theBenchmark.p
% 2.56/0.97  
% 2.56/0.97   Resolution empty clause
% 2.56/0.97  
% 2.56/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.56/0.97  
% 2.56/0.97  fof(f4,axiom,(
% 2.56/0.97    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.97  
% 2.56/0.97  fof(f16,plain,(
% 2.56/0.97    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 2.56/0.97    inference(ennf_transformation,[],[f4])).
% 2.56/0.97  
% 2.56/0.97  fof(f17,plain,(
% 2.56/0.97    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 2.56/0.97    inference(flattening,[],[f16])).
% 2.56/0.97  
% 2.56/0.97  fof(f34,plain,(
% 2.56/0.97    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 2.56/0.97    introduced(choice_axiom,[])).
% 2.56/0.97  
% 2.56/0.97  fof(f35,plain,(
% 2.56/0.97    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 2.56/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f34])).
% 2.56/0.97  
% 2.56/0.97  fof(f47,plain,(
% 2.56/0.97    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK3(X0,X1),X0)) )),
% 2.56/0.97    inference(cnf_transformation,[],[f35])).
% 2.56/0.97  
% 2.56/0.97  fof(f8,conjecture,(
% 2.56/0.97    ! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 2.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.97  
% 2.56/0.97  fof(f9,negated_conjecture,(
% 2.56/0.97    ~! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 2.56/0.97    inference(negated_conjecture,[],[f8])).
% 2.56/0.97  
% 2.56/0.97  fof(f23,plain,(
% 2.56/0.97    ? [X0,X1] : ((! [X2] : ((? [X3] : ((~r1_ordinal1(X2,X3) & r2_hidden(X3,X0)) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0)) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1)) & v3_ordinal1(X1))),
% 2.56/0.97    inference(ennf_transformation,[],[f9])).
% 2.56/0.97  
% 2.56/0.97  fof(f24,plain,(
% 2.56/0.97    ? [X0,X1] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1))),
% 2.56/0.97    inference(flattening,[],[f23])).
% 2.56/0.97  
% 2.56/0.97  fof(f37,plain,(
% 2.56/0.97    ( ! [X0] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) => (~r1_ordinal1(X2,sK6(X2)) & r2_hidden(sK6(X2),X0) & v3_ordinal1(sK6(X2))))) )),
% 2.56/0.97    introduced(choice_axiom,[])).
% 2.56/0.97  
% 2.56/0.97  fof(f36,plain,(
% 2.56/0.97    ? [X0,X1] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1)) => (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,sK4) & v3_ordinal1(X3)) | ~r2_hidden(X2,sK4) | ~v3_ordinal1(X2)) & k1_xboole_0 != sK4 & r1_tarski(sK4,sK5) & v3_ordinal1(sK5))),
% 2.56/0.97    introduced(choice_axiom,[])).
% 2.56/0.97  
% 2.56/0.97  fof(f38,plain,(
% 2.56/0.97    ! [X2] : ((~r1_ordinal1(X2,sK6(X2)) & r2_hidden(sK6(X2),sK4) & v3_ordinal1(sK6(X2))) | ~r2_hidden(X2,sK4) | ~v3_ordinal1(X2)) & k1_xboole_0 != sK4 & r1_tarski(sK4,sK5) & v3_ordinal1(sK5)),
% 2.56/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f37,f36])).
% 2.56/0.97  
% 2.56/0.97  fof(f56,plain,(
% 2.56/0.97    ( ! [X2] : (r2_hidden(sK6(X2),sK4) | ~r2_hidden(X2,sK4) | ~v3_ordinal1(X2)) )),
% 2.56/0.97    inference(cnf_transformation,[],[f38])).
% 2.56/0.97  
% 2.56/0.97  fof(f6,axiom,(
% 2.56/0.97    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 2.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.97  
% 2.56/0.97  fof(f20,plain,(
% 2.56/0.97    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.56/0.97    inference(ennf_transformation,[],[f6])).
% 2.56/0.97  
% 2.56/0.97  fof(f21,plain,(
% 2.56/0.97    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.56/0.97    inference(flattening,[],[f20])).
% 2.56/0.97  
% 2.56/0.97  fof(f50,plain,(
% 2.56/0.97    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.56/0.97    inference(cnf_transformation,[],[f21])).
% 2.56/0.97  
% 2.56/0.97  fof(f57,plain,(
% 2.56/0.97    ( ! [X2] : (~r1_ordinal1(X2,sK6(X2)) | ~r2_hidden(X2,sK4) | ~v3_ordinal1(X2)) )),
% 2.56/0.97    inference(cnf_transformation,[],[f38])).
% 2.56/0.97  
% 2.56/0.97  fof(f55,plain,(
% 2.56/0.97    ( ! [X2] : (v3_ordinal1(sK6(X2)) | ~r2_hidden(X2,sK4) | ~v3_ordinal1(X2)) )),
% 2.56/0.97    inference(cnf_transformation,[],[f38])).
% 2.56/0.97  
% 2.56/0.97  fof(f3,axiom,(
% 2.56/0.97    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 2.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.97  
% 2.56/0.97  fof(f15,plain,(
% 2.56/0.97    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 2.56/0.97    inference(ennf_transformation,[],[f3])).
% 2.56/0.97  
% 2.56/0.97  fof(f32,plain,(
% 2.56/0.97    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)))),
% 2.56/0.97    introduced(choice_axiom,[])).
% 2.56/0.97  
% 2.56/0.97  fof(f33,plain,(
% 2.56/0.97    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)) | ~r2_hidden(X0,X1))),
% 2.56/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f32])).
% 2.56/0.97  
% 2.56/0.97  fof(f46,plain,(
% 2.56/0.97    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 2.56/0.97    inference(cnf_transformation,[],[f33])).
% 2.56/0.97  
% 2.56/0.97  fof(f52,plain,(
% 2.56/0.97    v3_ordinal1(sK5)),
% 2.56/0.97    inference(cnf_transformation,[],[f38])).
% 2.56/0.97  
% 2.56/0.97  fof(f53,plain,(
% 2.56/0.97    r1_tarski(sK4,sK5)),
% 2.56/0.97    inference(cnf_transformation,[],[f38])).
% 2.56/0.97  
% 2.56/0.97  fof(f1,axiom,(
% 2.56/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.97  
% 2.56/0.97  fof(f12,plain,(
% 2.56/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.56/0.97    inference(ennf_transformation,[],[f1])).
% 2.56/0.97  
% 2.56/0.97  fof(f25,plain,(
% 2.56/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.56/0.97    inference(nnf_transformation,[],[f12])).
% 2.56/0.97  
% 2.56/0.97  fof(f26,plain,(
% 2.56/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.56/0.97    inference(rectify,[],[f25])).
% 2.56/0.97  
% 2.56/0.97  fof(f27,plain,(
% 2.56/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.56/0.97    introduced(choice_axiom,[])).
% 2.56/0.97  
% 2.56/0.97  fof(f28,plain,(
% 2.56/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.56/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 2.56/0.97  
% 2.56/0.97  fof(f39,plain,(
% 2.56/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.56/0.97    inference(cnf_transformation,[],[f28])).
% 2.56/0.97  
% 2.56/0.97  fof(f5,axiom,(
% 2.56/0.97    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 2.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.97  
% 2.56/0.97  fof(f18,plain,(
% 2.56/0.97    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 2.56/0.97    inference(ennf_transformation,[],[f5])).
% 2.56/0.97  
% 2.56/0.97  fof(f19,plain,(
% 2.56/0.97    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 2.56/0.97    inference(flattening,[],[f18])).
% 2.56/0.97  
% 2.56/0.97  fof(f49,plain,(
% 2.56/0.97    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 2.56/0.97    inference(cnf_transformation,[],[f19])).
% 2.56/0.97  
% 2.56/0.97  fof(f45,plain,(
% 2.56/0.97    ( ! [X0,X1] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X0,X1)) )),
% 2.56/0.97    inference(cnf_transformation,[],[f33])).
% 2.56/0.97  
% 2.56/0.97  fof(f54,plain,(
% 2.56/0.97    k1_xboole_0 != sK4),
% 2.56/0.97    inference(cnf_transformation,[],[f38])).
% 2.56/0.97  
% 2.56/0.97  fof(f2,axiom,(
% 2.56/0.97    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X2] : (r2_hidden(X2,X1) => r2_hidden(k1_zfmisc_1(X2),X1)) & ! [X2,X3] : ((r1_tarski(X3,X2) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)) & r2_hidden(X0,X1))),
% 2.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.97  
% 2.56/0.97  fof(f10,plain,(
% 2.56/0.97    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X3] : (r2_hidden(X3,X1) => r2_hidden(k1_zfmisc_1(X3),X1)) & ! [X4,X5] : ((r1_tarski(X5,X4) & r2_hidden(X4,X1)) => r2_hidden(X5,X1)) & r2_hidden(X0,X1))),
% 2.56/0.97    inference(rectify,[],[f2])).
% 2.56/0.97  
% 2.56/0.97  fof(f11,plain,(
% 2.56/0.97    ! [X0] : ? [X1] : (! [X3] : (r2_hidden(X3,X1) => r2_hidden(k1_zfmisc_1(X3),X1)) & ! [X4,X5] : ((r1_tarski(X5,X4) & r2_hidden(X4,X1)) => r2_hidden(X5,X1)) & r2_hidden(X0,X1))),
% 2.56/0.97    inference(pure_predicate_removal,[],[f10])).
% 2.56/0.97  
% 2.56/0.97  fof(f13,plain,(
% 2.56/0.97    ! [X0] : ? [X1] : (! [X3] : (r2_hidden(k1_zfmisc_1(X3),X1) | ~r2_hidden(X3,X1)) & ! [X4,X5] : (r2_hidden(X5,X1) | (~r1_tarski(X5,X4) | ~r2_hidden(X4,X1))) & r2_hidden(X0,X1))),
% 2.56/0.97    inference(ennf_transformation,[],[f11])).
% 2.56/0.97  
% 2.56/0.97  fof(f14,plain,(
% 2.56/0.97    ! [X0] : ? [X1] : (! [X3] : (r2_hidden(k1_zfmisc_1(X3),X1) | ~r2_hidden(X3,X1)) & ! [X4,X5] : (r2_hidden(X5,X1) | ~r1_tarski(X5,X4) | ~r2_hidden(X4,X1)) & r2_hidden(X0,X1))),
% 2.56/0.97    inference(flattening,[],[f13])).
% 2.56/0.97  
% 2.56/0.97  fof(f29,plain,(
% 2.56/0.97    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(k1_zfmisc_1(X2),X1) | ~r2_hidden(X2,X1)) & ! [X3,X4] : (r2_hidden(X4,X1) | ~r1_tarski(X4,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X0,X1))),
% 2.56/0.97    inference(rectify,[],[f14])).
% 2.56/0.97  
% 2.56/0.97  fof(f30,plain,(
% 2.56/0.97    ! [X0] : (? [X1] : (! [X2] : (r2_hidden(k1_zfmisc_1(X2),X1) | ~r2_hidden(X2,X1)) & ! [X3,X4] : (r2_hidden(X4,X1) | ~r1_tarski(X4,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X0,X1)) => (! [X2] : (r2_hidden(k1_zfmisc_1(X2),sK1(X0)) | ~r2_hidden(X2,sK1(X0))) & ! [X4,X3] : (r2_hidden(X4,sK1(X0)) | ~r1_tarski(X4,X3) | ~r2_hidden(X3,sK1(X0))) & r2_hidden(X0,sK1(X0))))),
% 2.56/0.97    introduced(choice_axiom,[])).
% 2.56/0.97  
% 2.56/0.97  fof(f31,plain,(
% 2.56/0.97    ! [X0] : (! [X2] : (r2_hidden(k1_zfmisc_1(X2),sK1(X0)) | ~r2_hidden(X2,sK1(X0))) & ! [X3,X4] : (r2_hidden(X4,sK1(X0)) | ~r1_tarski(X4,X3) | ~r2_hidden(X3,sK1(X0))) & r2_hidden(X0,sK1(X0)))),
% 2.56/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 2.56/0.97  
% 2.56/0.97  fof(f42,plain,(
% 2.56/0.97    ( ! [X0] : (r2_hidden(X0,sK1(X0))) )),
% 2.56/0.97    inference(cnf_transformation,[],[f31])).
% 2.56/0.97  
% 2.56/0.97  fof(f7,axiom,(
% 2.56/0.97    ! [X0,X1,X2] : ~(r2_hidden(X2,X0) & r2_hidden(X1,X2) & r2_hidden(X0,X1))),
% 2.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.97  
% 2.56/0.97  fof(f22,plain,(
% 2.56/0.97    ! [X0,X1,X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X1))),
% 2.56/0.97    inference(ennf_transformation,[],[f7])).
% 2.56/0.97  
% 2.56/0.97  fof(f51,plain,(
% 2.56/0.97    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X1)) )),
% 2.56/0.97    inference(cnf_transformation,[],[f22])).
% 2.56/0.97  
% 2.56/0.97  cnf(c_9,plain,
% 2.56/0.97      ( r2_hidden(sK3(X0,X1),X0)
% 2.56/0.97      | r1_tarski(X1,k1_setfam_1(X0))
% 2.56/0.97      | k1_xboole_0 = X0 ),
% 2.56/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_632,plain,
% 2.56/0.97      ( k1_xboole_0 = X0
% 2.56/0.97      | r2_hidden(sK3(X0,X1),X0) = iProver_top
% 2.56/0.97      | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top ),
% 2.56/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_14,negated_conjecture,
% 2.56/0.97      ( ~ r2_hidden(X0,sK4) | r2_hidden(sK6(X0),sK4) | ~ v3_ordinal1(X0) ),
% 2.56/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_629,plain,
% 2.56/0.97      ( r2_hidden(X0,sK4) != iProver_top
% 2.56/0.97      | r2_hidden(sK6(X0),sK4) = iProver_top
% 2.56/0.97      | v3_ordinal1(X0) != iProver_top ),
% 2.56/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_11,plain,
% 2.56/0.97      ( r1_ordinal1(X0,X1)
% 2.56/0.97      | r2_hidden(X1,X0)
% 2.56/0.97      | ~ v3_ordinal1(X1)
% 2.56/0.97      | ~ v3_ordinal1(X0) ),
% 2.56/0.97      inference(cnf_transformation,[],[f50]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_13,negated_conjecture,
% 2.56/0.97      ( ~ r1_ordinal1(X0,sK6(X0)) | ~ r2_hidden(X0,sK4) | ~ v3_ordinal1(X0) ),
% 2.56/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_196,plain,
% 2.56/0.97      ( r2_hidden(X0,X1)
% 2.56/0.97      | ~ r2_hidden(X2,sK4)
% 2.56/0.97      | ~ v3_ordinal1(X0)
% 2.56/0.97      | ~ v3_ordinal1(X1)
% 2.56/0.97      | ~ v3_ordinal1(X2)
% 2.56/0.97      | X2 != X1
% 2.56/0.97      | sK6(X2) != X0 ),
% 2.56/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_13]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_197,plain,
% 2.56/0.97      ( ~ r2_hidden(X0,sK4)
% 2.56/0.97      | r2_hidden(sK6(X0),X0)
% 2.56/0.97      | ~ v3_ordinal1(X0)
% 2.56/0.97      | ~ v3_ordinal1(sK6(X0)) ),
% 2.56/0.97      inference(unflattening,[status(thm)],[c_196]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_15,negated_conjecture,
% 2.56/0.97      ( ~ r2_hidden(X0,sK4) | ~ v3_ordinal1(X0) | v3_ordinal1(sK6(X0)) ),
% 2.56/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_199,plain,
% 2.56/0.97      ( ~ v3_ordinal1(X0) | r2_hidden(sK6(X0),X0) | ~ r2_hidden(X0,sK4) ),
% 2.56/0.97      inference(global_propositional_subsumption,[status(thm)],[c_197,c_15]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_200,plain,
% 2.56/0.97      ( ~ r2_hidden(X0,sK4) | r2_hidden(sK6(X0),X0) | ~ v3_ordinal1(X0) ),
% 2.56/0.97      inference(renaming,[status(thm)],[c_199]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_625,plain,
% 2.56/0.97      ( r2_hidden(X0,sK4) != iProver_top
% 2.56/0.97      | r2_hidden(sK6(X0),X0) = iProver_top
% 2.56/0.97      | v3_ordinal1(X0) != iProver_top ),
% 2.56/0.97      inference(predicate_to_equality,[status(thm)],[c_200]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_6,plain,
% 2.56/0.97      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,sK2(X1)) ),
% 2.56/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_635,plain,
% 2.56/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.56/0.97      | r2_hidden(X2,X1) != iProver_top
% 2.56/0.97      | r2_hidden(X2,sK2(X1)) != iProver_top ),
% 2.56/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_3267,plain,
% 2.56/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.56/0.97      | r2_hidden(sK6(sK2(X1)),X1) != iProver_top
% 2.56/0.97      | r2_hidden(sK2(X1),sK4) != iProver_top
% 2.56/0.97      | v3_ordinal1(sK2(X1)) != iProver_top ),
% 2.56/0.97      inference(superposition,[status(thm)],[c_625,c_635]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_4050,plain,
% 2.56/0.97      ( r2_hidden(X0,sK4) != iProver_top
% 2.56/0.97      | r2_hidden(sK2(sK4),sK4) != iProver_top
% 2.56/0.97      | v3_ordinal1(sK2(sK4)) != iProver_top ),
% 2.56/0.97      inference(superposition,[status(thm)],[c_629,c_3267]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_18,negated_conjecture,
% 2.56/0.97      ( v3_ordinal1(sK5) ),
% 2.56/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_19,plain,
% 2.56/0.97      ( v3_ordinal1(sK5) = iProver_top ),
% 2.56/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_17,negated_conjecture,
% 2.56/0.97      ( r1_tarski(sK4,sK5) ),
% 2.56/0.97      inference(cnf_transformation,[],[f53]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_20,plain,
% 2.56/0.97      ( r1_tarski(sK4,sK5) = iProver_top ),
% 2.56/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_2,plain,
% 2.56/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.56/0.97      inference(cnf_transformation,[],[f39]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_1416,plain,
% 2.56/0.97      ( ~ r2_hidden(sK2(X0),X0) | r2_hidden(sK2(X0),X1) | ~ r1_tarski(X0,X1) ),
% 2.56/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_2812,plain,
% 2.56/0.97      ( ~ r2_hidden(sK2(X0),X0)
% 2.56/0.97      | r2_hidden(sK2(X0),sK5)
% 2.56/0.97      | ~ r1_tarski(X0,sK5) ),
% 2.56/0.97      inference(instantiation,[status(thm)],[c_1416]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_2814,plain,
% 2.56/0.97      ( r2_hidden(sK2(X0),X0) != iProver_top
% 2.56/0.97      | r2_hidden(sK2(X0),sK5) = iProver_top
% 2.56/0.97      | r1_tarski(X0,sK5) != iProver_top ),
% 2.56/0.97      inference(predicate_to_equality,[status(thm)],[c_2812]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_2816,plain,
% 2.56/0.97      ( r2_hidden(sK2(sK4),sK5) = iProver_top
% 2.56/0.97      | r2_hidden(sK2(sK4),sK4) != iProver_top
% 2.56/0.97      | r1_tarski(sK4,sK5) != iProver_top ),
% 2.56/0.97      inference(instantiation,[status(thm)],[c_2814]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_10,plain,
% 2.56/0.97      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 2.56/0.97      inference(cnf_transformation,[],[f49]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_785,plain,
% 2.56/0.97      ( ~ r2_hidden(X0,sK5) | v3_ordinal1(X0) | ~ v3_ordinal1(sK5) ),
% 2.56/0.97      inference(instantiation,[status(thm)],[c_10]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_2813,plain,
% 2.56/0.97      ( ~ r2_hidden(sK2(X0),sK5) | v3_ordinal1(sK2(X0)) | ~ v3_ordinal1(sK5) ),
% 2.56/0.97      inference(instantiation,[status(thm)],[c_785]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_2818,plain,
% 2.56/0.97      ( r2_hidden(sK2(X0),sK5) != iProver_top
% 2.56/0.97      | v3_ordinal1(sK2(X0)) = iProver_top
% 2.56/0.97      | v3_ordinal1(sK5) != iProver_top ),
% 2.56/0.97      inference(predicate_to_equality,[status(thm)],[c_2813]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_2820,plain,
% 2.56/0.97      ( r2_hidden(sK2(sK4),sK5) != iProver_top
% 2.56/0.97      | v3_ordinal1(sK2(sK4)) = iProver_top
% 2.56/0.97      | v3_ordinal1(sK5) != iProver_top ),
% 2.56/0.97      inference(instantiation,[status(thm)],[c_2818]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_4099,plain,
% 2.56/0.97      ( r2_hidden(sK2(sK4),sK4) != iProver_top
% 2.56/0.97      | r2_hidden(X0,sK4) != iProver_top ),
% 2.56/0.97      inference(global_propositional_subsumption,
% 2.56/0.97                [status(thm)],
% 2.56/0.97                [c_4050,c_19,c_20,c_2816,c_2820]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_4100,plain,
% 2.56/0.97      ( r2_hidden(X0,sK4) != iProver_top
% 2.56/0.97      | r2_hidden(sK2(sK4),sK4) != iProver_top ),
% 2.56/0.97      inference(renaming,[status(thm)],[c_4099]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_7,plain,
% 2.56/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(sK2(X1),X1) ),
% 2.56/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_634,plain,
% 2.56/0.97      ( r2_hidden(X0,X1) != iProver_top | r2_hidden(sK2(X1),X1) = iProver_top ),
% 2.56/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_4105,plain,
% 2.56/0.97      ( r2_hidden(X0,sK4) != iProver_top ),
% 2.56/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_4100,c_634]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_4108,plain,
% 2.56/0.97      ( sK4 = k1_xboole_0 | r1_tarski(X0,k1_setfam_1(sK4)) = iProver_top ),
% 2.56/0.97      inference(superposition,[status(thm)],[c_632,c_4105]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_16,negated_conjecture,
% 2.56/0.97      ( k1_xboole_0 != sK4 ),
% 2.56/0.97      inference(cnf_transformation,[],[f54]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_331,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_861,plain,
% 2.56/0.97      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 2.56/0.97      inference(instantiation,[status(thm)],[c_331]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_911,plain,
% 2.56/0.97      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 2.56/0.97      inference(instantiation,[status(thm)],[c_861]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_330,plain,( X0 = X0 ),theory(equality) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_912,plain,
% 2.56/0.97      ( k1_xboole_0 = k1_xboole_0 ),
% 2.56/0.97      inference(instantiation,[status(thm)],[c_330]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_4344,plain,
% 2.56/0.97      ( r1_tarski(X0,k1_setfam_1(sK4)) = iProver_top ),
% 2.56/0.97      inference(global_propositional_subsumption,
% 2.56/0.97                [status(thm)],
% 2.56/0.97                [c_4108,c_16,c_911,c_912]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_5,plain,
% 2.56/0.97      ( r2_hidden(X0,sK1(X0)) ),
% 2.56/0.97      inference(cnf_transformation,[],[f42]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_636,plain,
% 2.56/0.97      ( r2_hidden(X0,sK1(X0)) = iProver_top ),
% 2.56/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_639,plain,
% 2.56/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.56/0.97      | r2_hidden(X0,X2) = iProver_top
% 2.56/0.97      | r1_tarski(X1,X2) != iProver_top ),
% 2.56/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_2200,plain,
% 2.56/0.97      ( r2_hidden(X0,X1) = iProver_top | r1_tarski(sK1(X0),X1) != iProver_top ),
% 2.56/0.97      inference(superposition,[status(thm)],[c_636,c_639]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_4665,plain,
% 2.56/0.97      ( r2_hidden(X0,k1_setfam_1(sK4)) = iProver_top ),
% 2.56/0.97      inference(superposition,[status(thm)],[c_4344,c_2200]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_12,plain,
% 2.56/0.97      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X1,X2) ),
% 2.56/0.97      inference(cnf_transformation,[],[f51]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_630,plain,
% 2.56/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.56/0.97      | r2_hidden(X2,X0) != iProver_top
% 2.56/0.97      | r2_hidden(X1,X2) != iProver_top ),
% 2.56/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_1119,plain,
% 2.56/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.56/0.97      | r2_hidden(sK1(X1),X0) != iProver_top ),
% 2.56/0.97      inference(superposition,[status(thm)],[c_636,c_630]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_4190,plain,
% 2.56/0.97      ( r2_hidden(sK1(sK1(X0)),X0) != iProver_top ),
% 2.56/0.97      inference(superposition,[status(thm)],[c_636,c_1119]) ).
% 2.56/0.97  
% 2.56/0.97  cnf(c_7486,plain,
% 2.56/0.97      ( $false ),
% 2.56/0.97      inference(superposition,[status(thm)],[c_4665,c_4190]) ).
% 2.56/0.97  
% 2.56/0.97  
% 2.56/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.56/0.97  
% 2.56/0.97  ------                               Statistics
% 2.56/0.97  
% 2.56/0.97  ------ General
% 2.56/0.97  
% 2.56/0.97  abstr_ref_over_cycles:                  0
% 2.56/0.97  abstr_ref_under_cycles:                 0
% 2.56/0.97  gc_basic_clause_elim:                   0
% 2.56/0.97  forced_gc_time:                         0
% 2.56/0.97  parsing_time:                           0.009
% 2.56/0.97  unif_index_cands_time:                  0.
% 2.56/0.97  unif_index_add_time:                    0.
% 2.56/0.97  orderings_time:                         0.
% 2.56/0.97  out_proof_time:                         0.007
% 2.56/0.97  total_time:                             0.23
% 2.56/0.97  num_of_symbols:                         45
% 2.56/0.97  num_of_terms:                           7384
% 2.56/0.97  
% 2.56/0.97  ------ Preprocessing
% 2.56/0.97  
% 2.56/0.97  num_of_splits:                          0
% 2.56/0.97  num_of_split_atoms:                     0
% 2.56/0.97  num_of_reused_defs:                     0
% 2.56/0.97  num_eq_ax_congr_red:                    28
% 2.56/0.97  num_of_sem_filtered_clauses:            1
% 2.56/0.97  num_of_subtypes:                        0
% 2.56/0.97  monotx_restored_types:                  0
% 2.56/0.97  sat_num_of_epr_types:                   0
% 2.56/0.97  sat_num_of_non_cyclic_types:            0
% 2.56/0.97  sat_guarded_non_collapsed_types:        0
% 2.56/0.97  num_pure_diseq_elim:                    0
% 2.56/0.97  simp_replaced_by:                       0
% 2.56/0.97  res_preprocessed:                       84
% 2.56/0.97  prep_upred:                             0
% 2.56/0.97  prep_unflattend:                        2
% 2.56/0.97  smt_new_axioms:                         0
% 2.56/0.97  pred_elim_cands:                        3
% 2.56/0.97  pred_elim:                              1
% 2.56/0.97  pred_elim_cl:                           1
% 2.56/0.97  pred_elim_cycles:                       3
% 2.56/0.97  merged_defs:                            0
% 2.56/0.97  merged_defs_ncl:                        0
% 2.56/0.97  bin_hyper_res:                          0
% 2.56/0.97  prep_cycles:                            4
% 2.56/0.97  pred_elim_time:                         0.001
% 2.56/0.97  splitting_time:                         0.
% 2.56/0.97  sem_filter_time:                        0.
% 2.56/0.97  monotx_time:                            0.001
% 2.56/0.97  subtype_inf_time:                       0.
% 2.56/0.97  
% 2.56/0.97  ------ Problem properties
% 2.56/0.97  
% 2.56/0.97  clauses:                                18
% 2.56/0.97  conjectures:                            5
% 2.56/0.97  epr:                                    6
% 2.56/0.97  horn:                                   15
% 2.56/0.97  ground:                                 3
% 2.56/0.97  unary:                                  4
% 2.56/0.97  binary:                                 4
% 2.56/0.97  lits:                                   42
% 2.56/0.97  lits_eq:                                3
% 2.56/0.97  fd_pure:                                0
% 2.56/0.97  fd_pseudo:                              0
% 2.56/0.97  fd_cond:                                2
% 2.56/0.97  fd_pseudo_cond:                         0
% 2.56/0.97  ac_symbols:                             0
% 2.56/0.97  
% 2.56/0.97  ------ Propositional Solver
% 2.56/0.97  
% 2.56/0.97  prop_solver_calls:                      29
% 2.56/0.97  prop_fast_solver_calls:                 800
% 2.56/0.97  smt_solver_calls:                       0
% 2.56/0.97  smt_fast_solver_calls:                  0
% 2.56/0.97  prop_num_of_clauses:                    2572
% 2.56/0.97  prop_preprocess_simplified:             5895
% 2.56/0.97  prop_fo_subsumed:                       65
% 2.56/0.97  prop_solver_time:                       0.
% 2.56/0.97  smt_solver_time:                        0.
% 2.56/0.97  smt_fast_solver_time:                   0.
% 2.56/0.97  prop_fast_solver_time:                  0.
% 2.56/0.97  prop_unsat_core_time:                   0.
% 2.56/0.97  
% 2.56/0.97  ------ QBF
% 2.56/0.97  
% 2.56/0.97  qbf_q_res:                              0
% 2.56/0.97  qbf_num_tautologies:                    0
% 2.56/0.97  qbf_prep_cycles:                        0
% 2.56/0.97  
% 2.56/0.97  ------ BMC1
% 2.56/0.97  
% 2.56/0.97  bmc1_current_bound:                     -1
% 2.56/0.97  bmc1_last_solved_bound:                 -1
% 2.56/0.97  bmc1_unsat_core_size:                   -1
% 2.56/0.97  bmc1_unsat_core_parents_size:           -1
% 2.56/0.97  bmc1_merge_next_fun:                    0
% 2.56/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.56/0.97  
% 2.56/0.97  ------ Instantiation
% 2.56/0.97  
% 2.56/0.97  inst_num_of_clauses:                    598
% 2.56/0.97  inst_num_in_passive:                    89
% 2.56/0.97  inst_num_in_active:                     320
% 2.56/0.97  inst_num_in_unprocessed:                189
% 2.56/0.97  inst_num_of_loops:                      370
% 2.56/0.97  inst_num_of_learning_restarts:          0
% 2.56/0.97  inst_num_moves_active_passive:          47
% 2.56/0.97  inst_lit_activity:                      0
% 2.56/0.97  inst_lit_activity_moves:                0
% 2.56/0.97  inst_num_tautologies:                   0
% 2.56/0.97  inst_num_prop_implied:                  0
% 2.56/0.97  inst_num_existing_simplified:           0
% 2.56/0.97  inst_num_eq_res_simplified:             0
% 2.56/0.97  inst_num_child_elim:                    0
% 2.56/0.97  inst_num_of_dismatching_blockings:      561
% 2.56/0.97  inst_num_of_non_proper_insts:           558
% 2.56/0.97  inst_num_of_duplicates:                 0
% 2.56/0.97  inst_inst_num_from_inst_to_res:         0
% 2.56/0.97  inst_dismatching_checking_time:         0.
% 2.56/0.97  
% 2.56/0.97  ------ Resolution
% 2.56/0.97  
% 2.56/0.97  res_num_of_clauses:                     0
% 2.56/0.97  res_num_in_passive:                     0
% 2.56/0.97  res_num_in_active:                      0
% 2.56/0.97  res_num_of_loops:                       88
% 2.56/0.97  res_forward_subset_subsumed:            54
% 2.56/0.97  res_backward_subset_subsumed:           0
% 2.56/0.97  res_forward_subsumed:                   0
% 2.56/0.97  res_backward_subsumed:                  0
% 2.56/0.97  res_forward_subsumption_resolution:     0
% 2.56/0.97  res_backward_subsumption_resolution:    0
% 2.56/0.97  res_clause_to_clause_subsumption:       1162
% 2.56/0.97  res_orphan_elimination:                 0
% 2.56/0.97  res_tautology_del:                      77
% 2.56/0.97  res_num_eq_res_simplified:              0
% 2.56/0.97  res_num_sel_changes:                    0
% 2.56/0.97  res_moves_from_active_to_pass:          0
% 2.56/0.97  
% 2.56/0.97  ------ Superposition
% 2.56/0.97  
% 2.56/0.97  sup_time_total:                         0.
% 2.56/0.97  sup_time_generating:                    0.
% 2.56/0.97  sup_time_sim_full:                      0.
% 2.56/0.97  sup_time_sim_immed:                     0.
% 2.56/0.97  
% 2.56/0.97  sup_num_of_clauses:                     161
% 2.56/0.97  sup_num_in_active:                      56
% 2.56/0.97  sup_num_in_passive:                     105
% 2.56/0.97  sup_num_of_loops:                       72
% 2.56/0.97  sup_fw_superposition:                   140
% 2.56/0.97  sup_bw_superposition:                   154
% 2.56/0.97  sup_immediate_simplified:               67
% 2.56/0.97  sup_given_eliminated:                   0
% 2.56/0.97  comparisons_done:                       0
% 2.56/0.97  comparisons_avoided:                    0
% 2.56/0.97  
% 2.56/0.97  ------ Simplifications
% 2.56/0.97  
% 2.56/0.97  
% 2.56/0.97  sim_fw_subset_subsumed:                 30
% 2.56/0.97  sim_bw_subset_subsumed:                 36
% 2.56/0.97  sim_fw_subsumed:                        47
% 2.56/0.97  sim_bw_subsumed:                        4
% 2.56/0.97  sim_fw_subsumption_res:                 1
% 2.56/0.97  sim_bw_subsumption_res:                 0
% 2.56/0.97  sim_tautology_del:                      2
% 2.56/0.97  sim_eq_tautology_del:                   0
% 2.56/0.97  sim_eq_res_simp:                        0
% 2.56/0.97  sim_fw_demodulated:                     0
% 2.56/0.97  sim_bw_demodulated:                     0
% 2.56/0.97  sim_light_normalised:                   0
% 2.56/0.97  sim_joinable_taut:                      0
% 2.56/0.97  sim_joinable_simp:                      0
% 2.56/0.97  sim_ac_normalised:                      0
% 2.56/0.97  sim_smt_subsumption:                    0
% 2.56/0.97  
%------------------------------------------------------------------------------
