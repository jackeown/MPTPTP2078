%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:14 EST 2020

% Result     : Theorem 7.35s
% Output     : CNFRefutation 7.35s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 680 expanded)
%              Number of clauses        :   92 ( 283 expanded)
%              Number of leaves         :   17 ( 119 expanded)
%              Depth                    :   24
%              Number of atoms          :  359 (1781 expanded)
%              Number of equality atoms :  172 ( 671 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
              | ~ r2_hidden(X2,X1) )
            & ( r2_hidden(X2,X1)
              | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_xboole_0 != X1
         => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f32,plain,(
    ? [X0,X1] :
      ( k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ? [X0,X1] :
      ( k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f32])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1))
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) != k5_setfam_1(sK2,k7_setfam_1(sK2,sK3))
      & k1_xboole_0 != sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) != k5_setfam_1(sK2,k7_setfam_1(sK2,sK3))
    & k1_xboole_0 != sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f42])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) != k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1406,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_168,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_169,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_168])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_170,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_171,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_170])).

cnf(c_208,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0))
    | ~ r1_tarski(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_171])).

cnf(c_481,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ r2_hidden(X4,X2)
    | r2_hidden(k3_subset_1(X3,X4),k7_setfam_1(X3,X2))
    | X4 != X0
    | X3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_169,c_208])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_482,c_14])).

cnf(c_1388,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1391,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1401,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1396,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3184,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_1396])).

cnf(c_13497,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) = iProver_top
    | r2_hidden(X0,k7_setfam_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1391,c_3184])).

cnf(c_13567,plain,
    ( m1_subset_1(k3_subset_1(sK2,X0),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1388,c_13497])).

cnf(c_23,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13905,plain,
    ( m1_subset_1(k3_subset_1(sK2,X0),k1_zfmisc_1(sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13567,c_23])).

cnf(c_13917,plain,
    ( m1_subset_1(X0,sK2) = iProver_top
    | r2_hidden(X0,k3_subset_1(sK2,X1)) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13905,c_1396])).

cnf(c_14582,plain,
    ( m1_subset_1(sK0(k3_subset_1(sK2,X0),X1),sK2) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(k3_subset_1(sK2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1406,c_13917])).

cnf(c_1397,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13916,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(k3_subset_1(sK2,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_13905,c_1397])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1400,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2448,plain,
    ( k7_setfam_1(sK2,k7_setfam_1(sK2,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_1391,c_1400])).

cnf(c_2574,plain,
    ( m1_subset_1(k7_setfam_1(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(sK2,sK3)) != iProver_top
    | r2_hidden(k3_subset_1(sK2,X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2448,c_1388])).

cnf(c_1568,plain,
    ( m1_subset_1(k7_setfam_1(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1569,plain,
    ( m1_subset_1(k7_setfam_1(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_2683,plain,
    ( r2_hidden(X0,k7_setfam_1(sK2,sK3)) != iProver_top
    | r2_hidden(k3_subset_1(sK2,X0),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2574,c_23,c_1569])).

cnf(c_2693,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k3_subset_1(sK2,k3_subset_1(sK2,X0)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1388,c_2683])).

cnf(c_2782,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k3_subset_1(sK2,k3_subset_1(sK2,X0)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2693,c_23])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,k7_setfam_1(X1,X0)) = k3_subset_1(X1,k5_setfam_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1392,plain,
    ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3328,plain,
    ( k6_setfam_1(X0,k7_setfam_1(X0,k7_setfam_1(X0,X1))) = k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))
    | k7_setfam_1(X0,X1) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_1392])).

cnf(c_22161,plain,
    ( k6_setfam_1(sK2,k7_setfam_1(sK2,k7_setfam_1(sK2,sK3))) = k3_subset_1(sK2,k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)))
    | k7_setfam_1(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1391,c_3328])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1399,plain,
    ( k5_setfam_1(X0,X1) = k3_tarski(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3183,plain,
    ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_tarski(k7_setfam_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_1399])).

cnf(c_8700,plain,
    ( k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)) = k3_tarski(k7_setfam_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_1391,c_3183])).

cnf(c_22197,plain,
    ( k7_setfam_1(sK2,sK3) = k1_xboole_0
    | k3_subset_1(sK2,k3_tarski(k7_setfam_1(sK2,sK3))) = k6_setfam_1(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_22161,c_2448,c_8700])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1395,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2790,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(sK3,k3_subset_1(sK2,k3_subset_1(sK2,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2782,c_1395])).

cnf(c_23450,plain,
    ( k7_setfam_1(sK2,sK3) = k1_xboole_0
    | r2_hidden(k3_tarski(k7_setfam_1(sK2,sK3)),sK3) != iProver_top
    | r1_tarski(sK3,k3_subset_1(sK2,k6_setfam_1(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22197,c_2790])).

cnf(c_20,negated_conjecture,
    ( k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) != k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1627,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)) = k3_tarski(k7_setfam_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_911,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1579,plain,
    ( k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)) != X0
    | k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) != X0
    | k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) = k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_911])).

cnf(c_1772,plain,
    ( k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)) != k3_tarski(k7_setfam_1(sK2,sK3))
    | k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) = k5_setfam_1(sK2,k7_setfam_1(sK2,sK3))
    | k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) != k3_tarski(k7_setfam_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1579])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1402,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3021,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(k5_setfam_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1402,c_1397])).

cnf(c_5515,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(k5_setfam_1(X1,k7_setfam_1(X1,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_3021])).

cnf(c_8750,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
    | r1_tarski(k3_tarski(k7_setfam_1(sK2,sK3)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_8700,c_5515])).

cnf(c_1662,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2635,plain,
    ( ~ m1_subset_1(k3_tarski(k7_setfam_1(sK2,sK3)),k1_zfmisc_1(sK2))
    | r1_tarski(k3_tarski(k7_setfam_1(sK2,sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_1662])).

cnf(c_2641,plain,
    ( m1_subset_1(k3_tarski(k7_setfam_1(sK2,sK3)),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k3_tarski(k7_setfam_1(sK2,sK3)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2635])).

cnf(c_8749,plain,
    ( m1_subset_1(k7_setfam_1(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
    | m1_subset_1(k3_tarski(k7_setfam_1(sK2,sK3)),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8700,c_1402])).

cnf(c_8811,plain,
    ( r1_tarski(k3_tarski(k7_setfam_1(sK2,sK3)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8750,c_23,c_1569,c_2641,c_8749])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_205,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_171])).

cnf(c_1390,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_205])).

cnf(c_8817,plain,
    ( k3_subset_1(sK2,k3_subset_1(sK2,k3_tarski(k7_setfam_1(sK2,sK3)))) = k3_tarski(k7_setfam_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_8811,c_1390])).

cnf(c_23465,plain,
    ( k7_setfam_1(sK2,sK3) = k1_xboole_0
    | k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) = k3_tarski(k7_setfam_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_22197,c_8817])).

cnf(c_23869,plain,
    ( k7_setfam_1(sK2,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23450,c_22,c_20,c_1568,c_1627,c_1772,c_23465])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0))
    | ~ r1_tarski(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_171])).

cnf(c_1389,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X2,X0) = iProver_top
    | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0)) != iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_2573,plain,
    ( m1_subset_1(k7_setfam_1(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(sK2,sK3)) = iProver_top
    | r2_hidden(k3_subset_1(sK2,X0),sK3) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2448,c_1389])).

cnf(c_2716,plain,
    ( r2_hidden(X0,k7_setfam_1(sK2,sK3)) = iProver_top
    | r2_hidden(k3_subset_1(sK2,X0),sK3) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2573,c_23,c_1569])).

cnf(c_23961,plain,
    ( r2_hidden(X0,k1_xboole_0) = iProver_top
    | r2_hidden(k3_subset_1(sK2,X0),sK3) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23869,c_2716])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_551,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_552,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_553,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_25962,plain,
    ( r2_hidden(k3_subset_1(sK2,X0),sK3) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23961,c_553])).

cnf(c_25970,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(k3_subset_1(sK2,X0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2782,c_25962])).

cnf(c_26666,plain,
    ( r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14582,c_13916,c_25970])).

cnf(c_26671,plain,
    ( r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1406,c_26666])).

cnf(c_26688,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_26671])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1549,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1550,plain,
    ( k1_xboole_0 = sK3
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1549])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26688,c_1550,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.35/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.35/1.50  
% 7.35/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.35/1.50  
% 7.35/1.50  ------  iProver source info
% 7.35/1.50  
% 7.35/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.35/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.35/1.50  git: non_committed_changes: false
% 7.35/1.50  git: last_make_outside_of_git: false
% 7.35/1.50  
% 7.35/1.50  ------ 
% 7.35/1.50  
% 7.35/1.50  ------ Input Options
% 7.35/1.50  
% 7.35/1.50  --out_options                           all
% 7.35/1.50  --tptp_safe_out                         true
% 7.35/1.50  --problem_path                          ""
% 7.35/1.50  --include_path                          ""
% 7.35/1.50  --clausifier                            res/vclausify_rel
% 7.35/1.50  --clausifier_options                    --mode clausify
% 7.35/1.50  --stdin                                 false
% 7.35/1.50  --stats_out                             all
% 7.35/1.50  
% 7.35/1.50  ------ General Options
% 7.35/1.50  
% 7.35/1.50  --fof                                   false
% 7.35/1.50  --time_out_real                         305.
% 7.35/1.50  --time_out_virtual                      -1.
% 7.35/1.50  --symbol_type_check                     false
% 7.35/1.50  --clausify_out                          false
% 7.35/1.50  --sig_cnt_out                           false
% 7.35/1.50  --trig_cnt_out                          false
% 7.35/1.50  --trig_cnt_out_tolerance                1.
% 7.35/1.50  --trig_cnt_out_sk_spl                   false
% 7.35/1.50  --abstr_cl_out                          false
% 7.35/1.50  
% 7.35/1.50  ------ Global Options
% 7.35/1.50  
% 7.35/1.50  --schedule                              default
% 7.35/1.50  --add_important_lit                     false
% 7.35/1.50  --prop_solver_per_cl                    1000
% 7.35/1.50  --min_unsat_core                        false
% 7.35/1.50  --soft_assumptions                      false
% 7.35/1.50  --soft_lemma_size                       3
% 7.35/1.50  --prop_impl_unit_size                   0
% 7.35/1.50  --prop_impl_unit                        []
% 7.35/1.50  --share_sel_clauses                     true
% 7.35/1.50  --reset_solvers                         false
% 7.35/1.50  --bc_imp_inh                            [conj_cone]
% 7.35/1.50  --conj_cone_tolerance                   3.
% 7.35/1.50  --extra_neg_conj                        none
% 7.35/1.50  --large_theory_mode                     true
% 7.35/1.50  --prolific_symb_bound                   200
% 7.35/1.50  --lt_threshold                          2000
% 7.35/1.50  --clause_weak_htbl                      true
% 7.35/1.50  --gc_record_bc_elim                     false
% 7.35/1.50  
% 7.35/1.50  ------ Preprocessing Options
% 7.35/1.50  
% 7.35/1.50  --preprocessing_flag                    true
% 7.35/1.50  --time_out_prep_mult                    0.1
% 7.35/1.50  --splitting_mode                        input
% 7.35/1.50  --splitting_grd                         true
% 7.35/1.50  --splitting_cvd                         false
% 7.35/1.50  --splitting_cvd_svl                     false
% 7.35/1.50  --splitting_nvd                         32
% 7.35/1.50  --sub_typing                            true
% 7.35/1.50  --prep_gs_sim                           true
% 7.35/1.50  --prep_unflatten                        true
% 7.35/1.50  --prep_res_sim                          true
% 7.35/1.50  --prep_upred                            true
% 7.35/1.50  --prep_sem_filter                       exhaustive
% 7.35/1.50  --prep_sem_filter_out                   false
% 7.35/1.50  --pred_elim                             true
% 7.35/1.50  --res_sim_input                         true
% 7.35/1.50  --eq_ax_congr_red                       true
% 7.35/1.50  --pure_diseq_elim                       true
% 7.35/1.50  --brand_transform                       false
% 7.35/1.50  --non_eq_to_eq                          false
% 7.35/1.50  --prep_def_merge                        true
% 7.35/1.50  --prep_def_merge_prop_impl              false
% 7.35/1.50  --prep_def_merge_mbd                    true
% 7.35/1.50  --prep_def_merge_tr_red                 false
% 7.35/1.50  --prep_def_merge_tr_cl                  false
% 7.35/1.50  --smt_preprocessing                     true
% 7.35/1.50  --smt_ac_axioms                         fast
% 7.35/1.50  --preprocessed_out                      false
% 7.35/1.50  --preprocessed_stats                    false
% 7.35/1.50  
% 7.35/1.50  ------ Abstraction refinement Options
% 7.35/1.50  
% 7.35/1.50  --abstr_ref                             []
% 7.35/1.50  --abstr_ref_prep                        false
% 7.35/1.50  --abstr_ref_until_sat                   false
% 7.35/1.50  --abstr_ref_sig_restrict                funpre
% 7.35/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.35/1.50  --abstr_ref_under                       []
% 7.35/1.50  
% 7.35/1.50  ------ SAT Options
% 7.35/1.50  
% 7.35/1.50  --sat_mode                              false
% 7.35/1.50  --sat_fm_restart_options                ""
% 7.35/1.50  --sat_gr_def                            false
% 7.35/1.50  --sat_epr_types                         true
% 7.35/1.50  --sat_non_cyclic_types                  false
% 7.35/1.50  --sat_finite_models                     false
% 7.35/1.50  --sat_fm_lemmas                         false
% 7.35/1.50  --sat_fm_prep                           false
% 7.35/1.50  --sat_fm_uc_incr                        true
% 7.35/1.50  --sat_out_model                         small
% 7.35/1.50  --sat_out_clauses                       false
% 7.35/1.50  
% 7.35/1.50  ------ QBF Options
% 7.35/1.50  
% 7.35/1.50  --qbf_mode                              false
% 7.35/1.50  --qbf_elim_univ                         false
% 7.35/1.50  --qbf_dom_inst                          none
% 7.35/1.50  --qbf_dom_pre_inst                      false
% 7.35/1.50  --qbf_sk_in                             false
% 7.35/1.50  --qbf_pred_elim                         true
% 7.35/1.50  --qbf_split                             512
% 7.35/1.50  
% 7.35/1.50  ------ BMC1 Options
% 7.35/1.50  
% 7.35/1.50  --bmc1_incremental                      false
% 7.35/1.50  --bmc1_axioms                           reachable_all
% 7.35/1.50  --bmc1_min_bound                        0
% 7.35/1.50  --bmc1_max_bound                        -1
% 7.35/1.50  --bmc1_max_bound_default                -1
% 7.35/1.50  --bmc1_symbol_reachability              true
% 7.35/1.50  --bmc1_property_lemmas                  false
% 7.35/1.50  --bmc1_k_induction                      false
% 7.35/1.50  --bmc1_non_equiv_states                 false
% 7.35/1.50  --bmc1_deadlock                         false
% 7.35/1.50  --bmc1_ucm                              false
% 7.35/1.50  --bmc1_add_unsat_core                   none
% 7.35/1.50  --bmc1_unsat_core_children              false
% 7.35/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.35/1.50  --bmc1_out_stat                         full
% 7.35/1.50  --bmc1_ground_init                      false
% 7.35/1.50  --bmc1_pre_inst_next_state              false
% 7.35/1.50  --bmc1_pre_inst_state                   false
% 7.35/1.50  --bmc1_pre_inst_reach_state             false
% 7.35/1.50  --bmc1_out_unsat_core                   false
% 7.35/1.50  --bmc1_aig_witness_out                  false
% 7.35/1.50  --bmc1_verbose                          false
% 7.35/1.50  --bmc1_dump_clauses_tptp                false
% 7.35/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.35/1.50  --bmc1_dump_file                        -
% 7.35/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.35/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.35/1.50  --bmc1_ucm_extend_mode                  1
% 7.35/1.50  --bmc1_ucm_init_mode                    2
% 7.35/1.50  --bmc1_ucm_cone_mode                    none
% 7.35/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.35/1.50  --bmc1_ucm_relax_model                  4
% 7.35/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.35/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.35/1.50  --bmc1_ucm_layered_model                none
% 7.35/1.50  --bmc1_ucm_max_lemma_size               10
% 7.35/1.50  
% 7.35/1.50  ------ AIG Options
% 7.35/1.50  
% 7.35/1.50  --aig_mode                              false
% 7.35/1.50  
% 7.35/1.50  ------ Instantiation Options
% 7.35/1.50  
% 7.35/1.50  --instantiation_flag                    true
% 7.35/1.50  --inst_sos_flag                         false
% 7.35/1.50  --inst_sos_phase                        true
% 7.35/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.35/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.35/1.50  --inst_lit_sel_side                     num_symb
% 7.35/1.50  --inst_solver_per_active                1400
% 7.35/1.50  --inst_solver_calls_frac                1.
% 7.35/1.50  --inst_passive_queue_type               priority_queues
% 7.35/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.35/1.50  --inst_passive_queues_freq              [25;2]
% 7.35/1.50  --inst_dismatching                      true
% 7.35/1.50  --inst_eager_unprocessed_to_passive     true
% 7.35/1.50  --inst_prop_sim_given                   true
% 7.35/1.50  --inst_prop_sim_new                     false
% 7.35/1.50  --inst_subs_new                         false
% 7.35/1.50  --inst_eq_res_simp                      false
% 7.35/1.50  --inst_subs_given                       false
% 7.35/1.50  --inst_orphan_elimination               true
% 7.35/1.50  --inst_learning_loop_flag               true
% 7.35/1.50  --inst_learning_start                   3000
% 7.35/1.50  --inst_learning_factor                  2
% 7.35/1.50  --inst_start_prop_sim_after_learn       3
% 7.35/1.50  --inst_sel_renew                        solver
% 7.35/1.50  --inst_lit_activity_flag                true
% 7.35/1.50  --inst_restr_to_given                   false
% 7.35/1.50  --inst_activity_threshold               500
% 7.35/1.50  --inst_out_proof                        true
% 7.35/1.50  
% 7.35/1.50  ------ Resolution Options
% 7.35/1.50  
% 7.35/1.50  --resolution_flag                       true
% 7.35/1.50  --res_lit_sel                           adaptive
% 7.35/1.50  --res_lit_sel_side                      none
% 7.35/1.50  --res_ordering                          kbo
% 7.35/1.50  --res_to_prop_solver                    active
% 7.35/1.50  --res_prop_simpl_new                    false
% 7.35/1.50  --res_prop_simpl_given                  true
% 7.35/1.50  --res_passive_queue_type                priority_queues
% 7.35/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.35/1.50  --res_passive_queues_freq               [15;5]
% 7.35/1.50  --res_forward_subs                      full
% 7.35/1.50  --res_backward_subs                     full
% 7.35/1.50  --res_forward_subs_resolution           true
% 7.35/1.50  --res_backward_subs_resolution          true
% 7.35/1.50  --res_orphan_elimination                true
% 7.35/1.50  --res_time_limit                        2.
% 7.35/1.50  --res_out_proof                         true
% 7.35/1.50  
% 7.35/1.50  ------ Superposition Options
% 7.35/1.50  
% 7.35/1.50  --superposition_flag                    true
% 7.35/1.50  --sup_passive_queue_type                priority_queues
% 7.35/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.35/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.35/1.50  --demod_completeness_check              fast
% 7.35/1.50  --demod_use_ground                      true
% 7.35/1.50  --sup_to_prop_solver                    passive
% 7.35/1.50  --sup_prop_simpl_new                    true
% 7.35/1.50  --sup_prop_simpl_given                  true
% 7.35/1.50  --sup_fun_splitting                     false
% 7.35/1.50  --sup_smt_interval                      50000
% 7.35/1.50  
% 7.35/1.50  ------ Superposition Simplification Setup
% 7.35/1.50  
% 7.35/1.50  --sup_indices_passive                   []
% 7.35/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.35/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.35/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.35/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.35/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.35/1.50  --sup_full_bw                           [BwDemod]
% 7.35/1.50  --sup_immed_triv                        [TrivRules]
% 7.35/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.35/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.35/1.50  --sup_immed_bw_main                     []
% 7.35/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.35/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.35/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.35/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.35/1.50  
% 7.35/1.50  ------ Combination Options
% 7.35/1.50  
% 7.35/1.50  --comb_res_mult                         3
% 7.35/1.50  --comb_sup_mult                         2
% 7.35/1.50  --comb_inst_mult                        10
% 7.35/1.50  
% 7.35/1.50  ------ Debug Options
% 7.35/1.50  
% 7.35/1.50  --dbg_backtrace                         false
% 7.35/1.50  --dbg_dump_prop_clauses                 false
% 7.35/1.50  --dbg_dump_prop_clauses_file            -
% 7.35/1.50  --dbg_out_stat                          false
% 7.35/1.50  ------ Parsing...
% 7.35/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.35/1.50  
% 7.35/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.35/1.50  
% 7.35/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.35/1.50  
% 7.35/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.35/1.50  ------ Proving...
% 7.35/1.50  ------ Problem Properties 
% 7.35/1.50  
% 7.35/1.50  
% 7.35/1.50  clauses                                 23
% 7.35/1.50  conjectures                             3
% 7.35/1.50  EPR                                     5
% 7.35/1.50  Horn                                    20
% 7.35/1.50  unary                                   4
% 7.35/1.50  binary                                  13
% 7.35/1.50  lits                                    49
% 7.35/1.50  lits eq                                 13
% 7.35/1.50  fd_pure                                 0
% 7.35/1.50  fd_pseudo                               0
% 7.35/1.50  fd_cond                                 3
% 7.35/1.50  fd_pseudo_cond                          0
% 7.35/1.50  AC symbols                              0
% 7.35/1.50  
% 7.35/1.50  ------ Schedule dynamic 5 is on 
% 7.35/1.50  
% 7.35/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.35/1.50  
% 7.35/1.50  
% 7.35/1.50  ------ 
% 7.35/1.50  Current options:
% 7.35/1.50  ------ 
% 7.35/1.50  
% 7.35/1.50  ------ Input Options
% 7.35/1.50  
% 7.35/1.50  --out_options                           all
% 7.35/1.50  --tptp_safe_out                         true
% 7.35/1.50  --problem_path                          ""
% 7.35/1.50  --include_path                          ""
% 7.35/1.50  --clausifier                            res/vclausify_rel
% 7.35/1.50  --clausifier_options                    --mode clausify
% 7.35/1.50  --stdin                                 false
% 7.35/1.50  --stats_out                             all
% 7.35/1.50  
% 7.35/1.50  ------ General Options
% 7.35/1.50  
% 7.35/1.50  --fof                                   false
% 7.35/1.50  --time_out_real                         305.
% 7.35/1.50  --time_out_virtual                      -1.
% 7.35/1.50  --symbol_type_check                     false
% 7.35/1.50  --clausify_out                          false
% 7.35/1.50  --sig_cnt_out                           false
% 7.35/1.50  --trig_cnt_out                          false
% 7.35/1.50  --trig_cnt_out_tolerance                1.
% 7.35/1.50  --trig_cnt_out_sk_spl                   false
% 7.35/1.50  --abstr_cl_out                          false
% 7.35/1.50  
% 7.35/1.50  ------ Global Options
% 7.35/1.50  
% 7.35/1.50  --schedule                              default
% 7.35/1.50  --add_important_lit                     false
% 7.35/1.50  --prop_solver_per_cl                    1000
% 7.35/1.50  --min_unsat_core                        false
% 7.35/1.50  --soft_assumptions                      false
% 7.35/1.50  --soft_lemma_size                       3
% 7.35/1.50  --prop_impl_unit_size                   0
% 7.35/1.50  --prop_impl_unit                        []
% 7.35/1.50  --share_sel_clauses                     true
% 7.35/1.50  --reset_solvers                         false
% 7.35/1.50  --bc_imp_inh                            [conj_cone]
% 7.35/1.50  --conj_cone_tolerance                   3.
% 7.35/1.50  --extra_neg_conj                        none
% 7.35/1.50  --large_theory_mode                     true
% 7.35/1.50  --prolific_symb_bound                   200
% 7.35/1.50  --lt_threshold                          2000
% 7.35/1.50  --clause_weak_htbl                      true
% 7.35/1.50  --gc_record_bc_elim                     false
% 7.35/1.50  
% 7.35/1.50  ------ Preprocessing Options
% 7.35/1.50  
% 7.35/1.50  --preprocessing_flag                    true
% 7.35/1.50  --time_out_prep_mult                    0.1
% 7.35/1.50  --splitting_mode                        input
% 7.35/1.50  --splitting_grd                         true
% 7.35/1.50  --splitting_cvd                         false
% 7.35/1.50  --splitting_cvd_svl                     false
% 7.35/1.50  --splitting_nvd                         32
% 7.35/1.50  --sub_typing                            true
% 7.35/1.50  --prep_gs_sim                           true
% 7.35/1.50  --prep_unflatten                        true
% 7.35/1.50  --prep_res_sim                          true
% 7.35/1.50  --prep_upred                            true
% 7.35/1.50  --prep_sem_filter                       exhaustive
% 7.35/1.50  --prep_sem_filter_out                   false
% 7.35/1.50  --pred_elim                             true
% 7.35/1.50  --res_sim_input                         true
% 7.35/1.50  --eq_ax_congr_red                       true
% 7.35/1.50  --pure_diseq_elim                       true
% 7.35/1.50  --brand_transform                       false
% 7.35/1.50  --non_eq_to_eq                          false
% 7.35/1.50  --prep_def_merge                        true
% 7.35/1.50  --prep_def_merge_prop_impl              false
% 7.35/1.50  --prep_def_merge_mbd                    true
% 7.35/1.50  --prep_def_merge_tr_red                 false
% 7.35/1.50  --prep_def_merge_tr_cl                  false
% 7.35/1.50  --smt_preprocessing                     true
% 7.35/1.50  --smt_ac_axioms                         fast
% 7.35/1.50  --preprocessed_out                      false
% 7.35/1.50  --preprocessed_stats                    false
% 7.35/1.50  
% 7.35/1.50  ------ Abstraction refinement Options
% 7.35/1.50  
% 7.35/1.50  --abstr_ref                             []
% 7.35/1.50  --abstr_ref_prep                        false
% 7.35/1.50  --abstr_ref_until_sat                   false
% 7.35/1.50  --abstr_ref_sig_restrict                funpre
% 7.35/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.35/1.50  --abstr_ref_under                       []
% 7.35/1.50  
% 7.35/1.50  ------ SAT Options
% 7.35/1.50  
% 7.35/1.50  --sat_mode                              false
% 7.35/1.50  --sat_fm_restart_options                ""
% 7.35/1.50  --sat_gr_def                            false
% 7.35/1.50  --sat_epr_types                         true
% 7.35/1.50  --sat_non_cyclic_types                  false
% 7.35/1.50  --sat_finite_models                     false
% 7.35/1.50  --sat_fm_lemmas                         false
% 7.35/1.50  --sat_fm_prep                           false
% 7.35/1.50  --sat_fm_uc_incr                        true
% 7.35/1.50  --sat_out_model                         small
% 7.35/1.50  --sat_out_clauses                       false
% 7.35/1.50  
% 7.35/1.50  ------ QBF Options
% 7.35/1.50  
% 7.35/1.50  --qbf_mode                              false
% 7.35/1.50  --qbf_elim_univ                         false
% 7.35/1.50  --qbf_dom_inst                          none
% 7.35/1.50  --qbf_dom_pre_inst                      false
% 7.35/1.50  --qbf_sk_in                             false
% 7.35/1.50  --qbf_pred_elim                         true
% 7.35/1.50  --qbf_split                             512
% 7.35/1.50  
% 7.35/1.50  ------ BMC1 Options
% 7.35/1.50  
% 7.35/1.50  --bmc1_incremental                      false
% 7.35/1.50  --bmc1_axioms                           reachable_all
% 7.35/1.50  --bmc1_min_bound                        0
% 7.35/1.50  --bmc1_max_bound                        -1
% 7.35/1.50  --bmc1_max_bound_default                -1
% 7.35/1.50  --bmc1_symbol_reachability              true
% 7.35/1.50  --bmc1_property_lemmas                  false
% 7.35/1.50  --bmc1_k_induction                      false
% 7.35/1.50  --bmc1_non_equiv_states                 false
% 7.35/1.50  --bmc1_deadlock                         false
% 7.35/1.50  --bmc1_ucm                              false
% 7.35/1.50  --bmc1_add_unsat_core                   none
% 7.35/1.50  --bmc1_unsat_core_children              false
% 7.35/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.35/1.50  --bmc1_out_stat                         full
% 7.35/1.50  --bmc1_ground_init                      false
% 7.35/1.50  --bmc1_pre_inst_next_state              false
% 7.35/1.50  --bmc1_pre_inst_state                   false
% 7.35/1.50  --bmc1_pre_inst_reach_state             false
% 7.35/1.50  --bmc1_out_unsat_core                   false
% 7.35/1.50  --bmc1_aig_witness_out                  false
% 7.35/1.50  --bmc1_verbose                          false
% 7.35/1.50  --bmc1_dump_clauses_tptp                false
% 7.35/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.35/1.50  --bmc1_dump_file                        -
% 7.35/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.35/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.35/1.50  --bmc1_ucm_extend_mode                  1
% 7.35/1.50  --bmc1_ucm_init_mode                    2
% 7.35/1.50  --bmc1_ucm_cone_mode                    none
% 7.35/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.35/1.50  --bmc1_ucm_relax_model                  4
% 7.35/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.35/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.35/1.50  --bmc1_ucm_layered_model                none
% 7.35/1.50  --bmc1_ucm_max_lemma_size               10
% 7.35/1.50  
% 7.35/1.50  ------ AIG Options
% 7.35/1.50  
% 7.35/1.50  --aig_mode                              false
% 7.35/1.50  
% 7.35/1.50  ------ Instantiation Options
% 7.35/1.50  
% 7.35/1.50  --instantiation_flag                    true
% 7.35/1.50  --inst_sos_flag                         false
% 7.35/1.50  --inst_sos_phase                        true
% 7.35/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.35/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.35/1.50  --inst_lit_sel_side                     none
% 7.35/1.50  --inst_solver_per_active                1400
% 7.35/1.50  --inst_solver_calls_frac                1.
% 7.35/1.50  --inst_passive_queue_type               priority_queues
% 7.35/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.35/1.50  --inst_passive_queues_freq              [25;2]
% 7.35/1.50  --inst_dismatching                      true
% 7.35/1.50  --inst_eager_unprocessed_to_passive     true
% 7.35/1.50  --inst_prop_sim_given                   true
% 7.35/1.50  --inst_prop_sim_new                     false
% 7.35/1.50  --inst_subs_new                         false
% 7.35/1.50  --inst_eq_res_simp                      false
% 7.35/1.50  --inst_subs_given                       false
% 7.35/1.50  --inst_orphan_elimination               true
% 7.35/1.50  --inst_learning_loop_flag               true
% 7.35/1.50  --inst_learning_start                   3000
% 7.35/1.50  --inst_learning_factor                  2
% 7.35/1.50  --inst_start_prop_sim_after_learn       3
% 7.35/1.50  --inst_sel_renew                        solver
% 7.35/1.50  --inst_lit_activity_flag                true
% 7.35/1.50  --inst_restr_to_given                   false
% 7.35/1.50  --inst_activity_threshold               500
% 7.35/1.50  --inst_out_proof                        true
% 7.35/1.50  
% 7.35/1.50  ------ Resolution Options
% 7.35/1.50  
% 7.35/1.50  --resolution_flag                       false
% 7.35/1.50  --res_lit_sel                           adaptive
% 7.35/1.50  --res_lit_sel_side                      none
% 7.35/1.50  --res_ordering                          kbo
% 7.35/1.50  --res_to_prop_solver                    active
% 7.35/1.50  --res_prop_simpl_new                    false
% 7.35/1.50  --res_prop_simpl_given                  true
% 7.35/1.50  --res_passive_queue_type                priority_queues
% 7.35/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.35/1.50  --res_passive_queues_freq               [15;5]
% 7.35/1.50  --res_forward_subs                      full
% 7.35/1.50  --res_backward_subs                     full
% 7.35/1.50  --res_forward_subs_resolution           true
% 7.35/1.50  --res_backward_subs_resolution          true
% 7.35/1.50  --res_orphan_elimination                true
% 7.35/1.50  --res_time_limit                        2.
% 7.35/1.50  --res_out_proof                         true
% 7.35/1.50  
% 7.35/1.50  ------ Superposition Options
% 7.35/1.50  
% 7.35/1.50  --superposition_flag                    true
% 7.35/1.50  --sup_passive_queue_type                priority_queues
% 7.35/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.35/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.35/1.50  --demod_completeness_check              fast
% 7.35/1.50  --demod_use_ground                      true
% 7.35/1.50  --sup_to_prop_solver                    passive
% 7.35/1.50  --sup_prop_simpl_new                    true
% 7.35/1.50  --sup_prop_simpl_given                  true
% 7.35/1.50  --sup_fun_splitting                     false
% 7.35/1.50  --sup_smt_interval                      50000
% 7.35/1.50  
% 7.35/1.50  ------ Superposition Simplification Setup
% 7.35/1.50  
% 7.35/1.50  --sup_indices_passive                   []
% 7.35/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.35/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.35/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.35/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.35/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.35/1.50  --sup_full_bw                           [BwDemod]
% 7.35/1.50  --sup_immed_triv                        [TrivRules]
% 7.35/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.35/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.35/1.50  --sup_immed_bw_main                     []
% 7.35/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.35/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.35/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.35/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.35/1.50  
% 7.35/1.50  ------ Combination Options
% 7.35/1.50  
% 7.35/1.50  --comb_res_mult                         3
% 7.35/1.50  --comb_sup_mult                         2
% 7.35/1.50  --comb_inst_mult                        10
% 7.35/1.50  
% 7.35/1.50  ------ Debug Options
% 7.35/1.50  
% 7.35/1.50  --dbg_backtrace                         false
% 7.35/1.50  --dbg_dump_prop_clauses                 false
% 7.35/1.50  --dbg_dump_prop_clauses_file            -
% 7.35/1.50  --dbg_out_stat                          false
% 7.35/1.50  
% 7.35/1.50  
% 7.35/1.50  
% 7.35/1.50  
% 7.35/1.50  ------ Proving...
% 7.35/1.50  
% 7.35/1.50  
% 7.35/1.50  % SZS status Theorem for theBenchmark.p
% 7.35/1.50  
% 7.35/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.35/1.50  
% 7.35/1.50  fof(f1,axiom,(
% 7.35/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.35/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f18,plain,(
% 7.35/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.35/1.50    inference(ennf_transformation,[],[f1])).
% 7.35/1.50  
% 7.35/1.50  fof(f34,plain,(
% 7.35/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.35/1.50    inference(nnf_transformation,[],[f18])).
% 7.35/1.50  
% 7.35/1.50  fof(f35,plain,(
% 7.35/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.35/1.50    inference(rectify,[],[f34])).
% 7.35/1.50  
% 7.35/1.50  fof(f36,plain,(
% 7.35/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.35/1.50    introduced(choice_axiom,[])).
% 7.35/1.50  
% 7.35/1.50  fof(f37,plain,(
% 7.35/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.35/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 7.35/1.50  
% 7.35/1.50  fof(f45,plain,(
% 7.35/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.35/1.50    inference(cnf_transformation,[],[f37])).
% 7.35/1.50  
% 7.35/1.50  fof(f9,axiom,(
% 7.35/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.35/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f38,plain,(
% 7.35/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.35/1.50    inference(nnf_transformation,[],[f9])).
% 7.35/1.50  
% 7.35/1.50  fof(f54,plain,(
% 7.35/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.35/1.50    inference(cnf_transformation,[],[f38])).
% 7.35/1.50  
% 7.35/1.50  fof(f10,axiom,(
% 7.35/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 7.35/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f25,plain,(
% 7.35/1.50    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.35/1.50    inference(ennf_transformation,[],[f10])).
% 7.35/1.50  
% 7.35/1.50  fof(f39,plain,(
% 7.35/1.50    ! [X0,X1] : (! [X2] : (((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1)) & (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.35/1.50    inference(nnf_transformation,[],[f25])).
% 7.35/1.50  
% 7.35/1.50  fof(f57,plain,(
% 7.35/1.50    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.35/1.50    inference(cnf_transformation,[],[f39])).
% 7.35/1.50  
% 7.35/1.50  fof(f55,plain,(
% 7.35/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.35/1.50    inference(cnf_transformation,[],[f38])).
% 7.35/1.50  
% 7.35/1.50  fof(f11,axiom,(
% 7.35/1.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.35/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f26,plain,(
% 7.35/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.35/1.50    inference(ennf_transformation,[],[f11])).
% 7.35/1.50  
% 7.35/1.50  fof(f27,plain,(
% 7.35/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.35/1.50    inference(flattening,[],[f26])).
% 7.35/1.50  
% 7.35/1.50  fof(f58,plain,(
% 7.35/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.35/1.50    inference(cnf_transformation,[],[f27])).
% 7.35/1.50  
% 7.35/1.50  fof(f15,conjecture,(
% 7.35/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 7.35/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f16,negated_conjecture,(
% 7.35/1.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 7.35/1.50    inference(negated_conjecture,[],[f15])).
% 7.35/1.50  
% 7.35/1.50  fof(f32,plain,(
% 7.35/1.50    ? [X0,X1] : ((k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.35/1.50    inference(ennf_transformation,[],[f16])).
% 7.35/1.50  
% 7.35/1.50  fof(f33,plain,(
% 7.35/1.50    ? [X0,X1] : (k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.35/1.50    inference(flattening,[],[f32])).
% 7.35/1.50  
% 7.35/1.50  fof(f42,plain,(
% 7.35/1.50    ? [X0,X1] : (k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) != k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)) & k1_xboole_0 != sK3 & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))))),
% 7.35/1.50    introduced(choice_axiom,[])).
% 7.35/1.50  
% 7.35/1.50  fof(f43,plain,(
% 7.35/1.50    k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) != k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)) & k1_xboole_0 != sK3 & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 7.35/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f42])).
% 7.35/1.50  
% 7.35/1.50  fof(f64,plain,(
% 7.35/1.50    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 7.35/1.50    inference(cnf_transformation,[],[f43])).
% 7.35/1.50  
% 7.35/1.50  fof(f6,axiom,(
% 7.35/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.35/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f22,plain,(
% 7.35/1.50    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.35/1.50    inference(ennf_transformation,[],[f6])).
% 7.35/1.50  
% 7.35/1.50  fof(f51,plain,(
% 7.35/1.50    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.35/1.50    inference(cnf_transformation,[],[f22])).
% 7.35/1.50  
% 7.35/1.50  fof(f7,axiom,(
% 7.35/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 7.35/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f23,plain,(
% 7.35/1.50    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.35/1.50    inference(ennf_transformation,[],[f7])).
% 7.35/1.50  
% 7.35/1.50  fof(f52,plain,(
% 7.35/1.50    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.35/1.50    inference(cnf_transformation,[],[f23])).
% 7.35/1.50  
% 7.35/1.50  fof(f14,axiom,(
% 7.35/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 7.35/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f30,plain,(
% 7.35/1.50    ! [X0,X1] : ((k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.35/1.50    inference(ennf_transformation,[],[f14])).
% 7.35/1.50  
% 7.35/1.50  fof(f31,plain,(
% 7.35/1.50    ! [X0,X1] : (k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.35/1.50    inference(flattening,[],[f30])).
% 7.35/1.50  
% 7.35/1.50  fof(f63,plain,(
% 7.35/1.50    ( ! [X0,X1] : (k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.35/1.50    inference(cnf_transformation,[],[f31])).
% 7.35/1.50  
% 7.35/1.50  fof(f8,axiom,(
% 7.35/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k5_setfam_1(X0,X1) = k3_tarski(X1))),
% 7.35/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f24,plain,(
% 7.35/1.50    ! [X0,X1] : (k5_setfam_1(X0,X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.35/1.50    inference(ennf_transformation,[],[f8])).
% 7.35/1.50  
% 7.35/1.50  fof(f53,plain,(
% 7.35/1.50    ( ! [X0,X1] : (k5_setfam_1(X0,X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.35/1.50    inference(cnf_transformation,[],[f24])).
% 7.35/1.50  
% 7.35/1.50  fof(f12,axiom,(
% 7.35/1.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.35/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f28,plain,(
% 7.35/1.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.35/1.50    inference(ennf_transformation,[],[f12])).
% 7.35/1.50  
% 7.35/1.50  fof(f59,plain,(
% 7.35/1.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.35/1.50    inference(cnf_transformation,[],[f28])).
% 7.35/1.50  
% 7.35/1.50  fof(f66,plain,(
% 7.35/1.50    k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) != k5_setfam_1(sK2,k7_setfam_1(sK2,sK3))),
% 7.35/1.50    inference(cnf_transformation,[],[f43])).
% 7.35/1.50  
% 7.35/1.50  fof(f5,axiom,(
% 7.35/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.35/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f21,plain,(
% 7.35/1.50    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.35/1.50    inference(ennf_transformation,[],[f5])).
% 7.35/1.50  
% 7.35/1.50  fof(f50,plain,(
% 7.35/1.50    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.35/1.50    inference(cnf_transformation,[],[f21])).
% 7.35/1.50  
% 7.35/1.50  fof(f4,axiom,(
% 7.35/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.35/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f20,plain,(
% 7.35/1.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.35/1.50    inference(ennf_transformation,[],[f4])).
% 7.35/1.50  
% 7.35/1.50  fof(f49,plain,(
% 7.35/1.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.35/1.50    inference(cnf_transformation,[],[f20])).
% 7.35/1.50  
% 7.35/1.50  fof(f56,plain,(
% 7.35/1.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.35/1.50    inference(cnf_transformation,[],[f39])).
% 7.35/1.50  
% 7.35/1.50  fof(f2,axiom,(
% 7.35/1.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.35/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f47,plain,(
% 7.35/1.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.35/1.50    inference(cnf_transformation,[],[f2])).
% 7.35/1.50  
% 7.35/1.50  fof(f3,axiom,(
% 7.35/1.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 7.35/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.35/1.50  
% 7.35/1.50  fof(f19,plain,(
% 7.35/1.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 7.35/1.50    inference(ennf_transformation,[],[f3])).
% 7.35/1.50  
% 7.35/1.50  fof(f48,plain,(
% 7.35/1.50    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 7.35/1.50    inference(cnf_transformation,[],[f19])).
% 7.35/1.50  
% 7.35/1.50  fof(f65,plain,(
% 7.35/1.50    k1_xboole_0 != sK3),
% 7.35/1.50    inference(cnf_transformation,[],[f43])).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1,plain,
% 7.35/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.35/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1406,plain,
% 7.35/1.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.35/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_11,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.35/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_168,plain,
% 7.35/1.50      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.35/1.50      inference(prop_impl,[status(thm)],[c_11]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_169,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.35/1.50      inference(renaming,[status(thm)],[c_168]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_12,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.35/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.35/1.50      | ~ r2_hidden(X0,X2)
% 7.35/1.50      | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
% 7.35/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_10,plain,
% 7.35/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.35/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_170,plain,
% 7.35/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.35/1.50      inference(prop_impl,[status(thm)],[c_10]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_171,plain,
% 7.35/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.35/1.50      inference(renaming,[status(thm)],[c_170]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_208,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.35/1.50      | ~ r2_hidden(X2,X0)
% 7.35/1.50      | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0))
% 7.35/1.50      | ~ r1_tarski(X2,X1) ),
% 7.35/1.50      inference(bin_hyper_res,[status(thm)],[c_12,c_171]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_481,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.35/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
% 7.35/1.50      | ~ r2_hidden(X4,X2)
% 7.35/1.50      | r2_hidden(k3_subset_1(X3,X4),k7_setfam_1(X3,X2))
% 7.35/1.50      | X4 != X0
% 7.35/1.50      | X3 != X1 ),
% 7.35/1.50      inference(resolution_lifted,[status(thm)],[c_169,c_208]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_482,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.35/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.35/1.50      | ~ r2_hidden(X0,X2)
% 7.35/1.50      | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
% 7.35/1.50      inference(unflattening,[status(thm)],[c_481]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_14,plain,
% 7.35/1.50      ( m1_subset_1(X0,X1)
% 7.35/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.35/1.50      | ~ r2_hidden(X0,X2) ),
% 7.35/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_492,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.35/1.50      | ~ r2_hidden(X2,X0)
% 7.35/1.50      | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0)) ),
% 7.35/1.50      inference(forward_subsumption_resolution,
% 7.35/1.50                [status(thm)],
% 7.35/1.50                [c_482,c_14]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1388,plain,
% 7.35/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 7.35/1.50      | r2_hidden(X2,X0) != iProver_top
% 7.35/1.50      | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0)) = iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_22,negated_conjecture,
% 7.35/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 7.35/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1391,plain,
% 7.35/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_7,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.35/1.50      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
% 7.35/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1401,plain,
% 7.35/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 7.35/1.50      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1396,plain,
% 7.35/1.50      ( m1_subset_1(X0,X1) = iProver_top
% 7.35/1.50      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.35/1.50      | r2_hidden(X0,X2) != iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_3184,plain,
% 7.35/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.35/1.50      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 7.35/1.50      | r2_hidden(X0,k7_setfam_1(X1,X2)) != iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_1401,c_1396]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_13497,plain,
% 7.35/1.50      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) = iProver_top
% 7.35/1.50      | r2_hidden(X0,k7_setfam_1(sK2,sK3)) != iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_1391,c_3184]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_13567,plain,
% 7.35/1.50      ( m1_subset_1(k3_subset_1(sK2,X0),k1_zfmisc_1(sK2)) = iProver_top
% 7.35/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
% 7.35/1.50      | r2_hidden(X0,sK3) != iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_1388,c_13497]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_23,plain,
% 7.35/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_13905,plain,
% 7.35/1.50      ( m1_subset_1(k3_subset_1(sK2,X0),k1_zfmisc_1(sK2)) = iProver_top
% 7.35/1.50      | r2_hidden(X0,sK3) != iProver_top ),
% 7.35/1.50      inference(global_propositional_subsumption,
% 7.35/1.50                [status(thm)],
% 7.35/1.50                [c_13567,c_23]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_13917,plain,
% 7.35/1.50      ( m1_subset_1(X0,sK2) = iProver_top
% 7.35/1.50      | r2_hidden(X0,k3_subset_1(sK2,X1)) != iProver_top
% 7.35/1.50      | r2_hidden(X1,sK3) != iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_13905,c_1396]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_14582,plain,
% 7.35/1.50      ( m1_subset_1(sK0(k3_subset_1(sK2,X0),X1),sK2) = iProver_top
% 7.35/1.50      | r2_hidden(X0,sK3) != iProver_top
% 7.35/1.50      | r1_tarski(k3_subset_1(sK2,X0),X1) = iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_1406,c_13917]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1397,plain,
% 7.35/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.35/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_13916,plain,
% 7.35/1.50      ( r2_hidden(X0,sK3) != iProver_top
% 7.35/1.50      | r1_tarski(k3_subset_1(sK2,X0),sK2) = iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_13905,c_1397]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_8,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.35/1.50      | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
% 7.35/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1400,plain,
% 7.35/1.50      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
% 7.35/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2448,plain,
% 7.35/1.50      ( k7_setfam_1(sK2,k7_setfam_1(sK2,sK3)) = sK3 ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_1391,c_1400]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2574,plain,
% 7.35/1.50      ( m1_subset_1(k7_setfam_1(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
% 7.35/1.50      | r2_hidden(X0,k7_setfam_1(sK2,sK3)) != iProver_top
% 7.35/1.50      | r2_hidden(k3_subset_1(sK2,X0),sK3) = iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_2448,c_1388]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1568,plain,
% 7.35/1.50      ( m1_subset_1(k7_setfam_1(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 7.35/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 7.35/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1569,plain,
% 7.35/1.50      ( m1_subset_1(k7_setfam_1(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top
% 7.35/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_1568]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2683,plain,
% 7.35/1.50      ( r2_hidden(X0,k7_setfam_1(sK2,sK3)) != iProver_top
% 7.35/1.50      | r2_hidden(k3_subset_1(sK2,X0),sK3) = iProver_top ),
% 7.35/1.50      inference(global_propositional_subsumption,
% 7.35/1.50                [status(thm)],
% 7.35/1.50                [c_2574,c_23,c_1569]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2693,plain,
% 7.35/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
% 7.35/1.50      | r2_hidden(X0,sK3) != iProver_top
% 7.35/1.50      | r2_hidden(k3_subset_1(sK2,k3_subset_1(sK2,X0)),sK3) = iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_1388,c_2683]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2782,plain,
% 7.35/1.50      ( r2_hidden(X0,sK3) != iProver_top
% 7.35/1.50      | r2_hidden(k3_subset_1(sK2,k3_subset_1(sK2,X0)),sK3) = iProver_top ),
% 7.35/1.50      inference(global_propositional_subsumption,
% 7.35/1.50                [status(thm)],
% 7.35/1.50                [c_2693,c_23]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_19,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.35/1.50      | k6_setfam_1(X1,k7_setfam_1(X1,X0)) = k3_subset_1(X1,k5_setfam_1(X1,X0))
% 7.35/1.50      | k1_xboole_0 = X0 ),
% 7.35/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1392,plain,
% 7.35/1.50      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
% 7.35/1.50      | k1_xboole_0 = X1
% 7.35/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_3328,plain,
% 7.35/1.50      ( k6_setfam_1(X0,k7_setfam_1(X0,k7_setfam_1(X0,X1))) = k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))
% 7.35/1.50      | k7_setfam_1(X0,X1) = k1_xboole_0
% 7.35/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_1401,c_1392]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_22161,plain,
% 7.35/1.50      ( k6_setfam_1(sK2,k7_setfam_1(sK2,k7_setfam_1(sK2,sK3))) = k3_subset_1(sK2,k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)))
% 7.35/1.50      | k7_setfam_1(sK2,sK3) = k1_xboole_0 ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_1391,c_3328]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_9,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.35/1.50      | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
% 7.35/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1399,plain,
% 7.35/1.50      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
% 7.35/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_3183,plain,
% 7.35/1.50      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_tarski(k7_setfam_1(X0,X1))
% 7.35/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_1401,c_1399]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_8700,plain,
% 7.35/1.50      ( k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)) = k3_tarski(k7_setfam_1(sK2,sK3)) ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_1391,c_3183]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_22197,plain,
% 7.35/1.50      ( k7_setfam_1(sK2,sK3) = k1_xboole_0
% 7.35/1.50      | k3_subset_1(sK2,k3_tarski(k7_setfam_1(sK2,sK3))) = k6_setfam_1(sK2,sK3) ),
% 7.35/1.50      inference(light_normalisation,
% 7.35/1.50                [status(thm)],
% 7.35/1.50                [c_22161,c_2448,c_8700]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_15,plain,
% 7.35/1.50      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.35/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1395,plain,
% 7.35/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.35/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2790,plain,
% 7.35/1.50      ( r2_hidden(X0,sK3) != iProver_top
% 7.35/1.50      | r1_tarski(sK3,k3_subset_1(sK2,k3_subset_1(sK2,X0))) != iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_2782,c_1395]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_23450,plain,
% 7.35/1.50      ( k7_setfam_1(sK2,sK3) = k1_xboole_0
% 7.35/1.50      | r2_hidden(k3_tarski(k7_setfam_1(sK2,sK3)),sK3) != iProver_top
% 7.35/1.50      | r1_tarski(sK3,k3_subset_1(sK2,k6_setfam_1(sK2,sK3))) != iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_22197,c_2790]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_20,negated_conjecture,
% 7.35/1.50      ( k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) != k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)) ),
% 7.35/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1627,plain,
% 7.35/1.50      ( ~ m1_subset_1(k7_setfam_1(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 7.35/1.50      | k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)) = k3_tarski(k7_setfam_1(sK2,sK3)) ),
% 7.35/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_911,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1579,plain,
% 7.35/1.50      ( k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)) != X0
% 7.35/1.50      | k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) != X0
% 7.35/1.50      | k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) = k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)) ),
% 7.35/1.50      inference(instantiation,[status(thm)],[c_911]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1772,plain,
% 7.35/1.50      ( k5_setfam_1(sK2,k7_setfam_1(sK2,sK3)) != k3_tarski(k7_setfam_1(sK2,sK3))
% 7.35/1.50      | k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) = k5_setfam_1(sK2,k7_setfam_1(sK2,sK3))
% 7.35/1.50      | k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) != k3_tarski(k7_setfam_1(sK2,sK3)) ),
% 7.35/1.50      inference(instantiation,[status(thm)],[c_1579]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_6,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.35/1.50      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.35/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1402,plain,
% 7.35/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 7.35/1.50      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_3021,plain,
% 7.35/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 7.35/1.50      | r1_tarski(k5_setfam_1(X1,X0),X1) = iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_1402,c_1397]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_5515,plain,
% 7.35/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 7.35/1.50      | r1_tarski(k5_setfam_1(X1,k7_setfam_1(X1,X0)),X1) = iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_1401,c_3021]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_8750,plain,
% 7.35/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
% 7.35/1.50      | r1_tarski(k3_tarski(k7_setfam_1(sK2,sK3)),sK2) = iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_8700,c_5515]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1662,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) | r1_tarski(X0,sK2) ),
% 7.35/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2635,plain,
% 7.35/1.50      ( ~ m1_subset_1(k3_tarski(k7_setfam_1(sK2,sK3)),k1_zfmisc_1(sK2))
% 7.35/1.50      | r1_tarski(k3_tarski(k7_setfam_1(sK2,sK3)),sK2) ),
% 7.35/1.50      inference(instantiation,[status(thm)],[c_1662]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2641,plain,
% 7.35/1.50      ( m1_subset_1(k3_tarski(k7_setfam_1(sK2,sK3)),k1_zfmisc_1(sK2)) != iProver_top
% 7.35/1.50      | r1_tarski(k3_tarski(k7_setfam_1(sK2,sK3)),sK2) = iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_2635]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_8749,plain,
% 7.35/1.50      ( m1_subset_1(k7_setfam_1(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
% 7.35/1.50      | m1_subset_1(k3_tarski(k7_setfam_1(sK2,sK3)),k1_zfmisc_1(sK2)) = iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_8700,c_1402]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_8811,plain,
% 7.35/1.50      ( r1_tarski(k3_tarski(k7_setfam_1(sK2,sK3)),sK2) = iProver_top ),
% 7.35/1.50      inference(global_propositional_subsumption,
% 7.35/1.50                [status(thm)],
% 7.35/1.50                [c_8750,c_23,c_1569,c_2641,c_8749]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_5,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.35/1.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.35/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_205,plain,
% 7.35/1.50      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.35/1.50      inference(bin_hyper_res,[status(thm)],[c_5,c_171]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1390,plain,
% 7.35/1.50      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 7.35/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_205]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_8817,plain,
% 7.35/1.50      ( k3_subset_1(sK2,k3_subset_1(sK2,k3_tarski(k7_setfam_1(sK2,sK3)))) = k3_tarski(k7_setfam_1(sK2,sK3)) ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_8811,c_1390]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_23465,plain,
% 7.35/1.50      ( k7_setfam_1(sK2,sK3) = k1_xboole_0
% 7.35/1.50      | k3_subset_1(sK2,k6_setfam_1(sK2,sK3)) = k3_tarski(k7_setfam_1(sK2,sK3)) ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_22197,c_8817]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_23869,plain,
% 7.35/1.50      ( k7_setfam_1(sK2,sK3) = k1_xboole_0 ),
% 7.35/1.50      inference(global_propositional_subsumption,
% 7.35/1.50                [status(thm)],
% 7.35/1.50                [c_23450,c_22,c_20,c_1568,c_1627,c_1772,c_23465]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_13,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.35/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.35/1.50      | r2_hidden(X0,X2)
% 7.35/1.50      | ~ r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
% 7.35/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_209,plain,
% 7.35/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.35/1.50      | r2_hidden(X2,X0)
% 7.35/1.50      | ~ r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0))
% 7.35/1.50      | ~ r1_tarski(X2,X1) ),
% 7.35/1.50      inference(bin_hyper_res,[status(thm)],[c_13,c_171]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1389,plain,
% 7.35/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 7.35/1.50      | r2_hidden(X2,X0) = iProver_top
% 7.35/1.50      | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0)) != iProver_top
% 7.35/1.50      | r1_tarski(X2,X1) != iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2573,plain,
% 7.35/1.50      ( m1_subset_1(k7_setfam_1(sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
% 7.35/1.50      | r2_hidden(X0,k7_setfam_1(sK2,sK3)) = iProver_top
% 7.35/1.50      | r2_hidden(k3_subset_1(sK2,X0),sK3) != iProver_top
% 7.35/1.50      | r1_tarski(X0,sK2) != iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_2448,c_1389]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_2716,plain,
% 7.35/1.50      ( r2_hidden(X0,k7_setfam_1(sK2,sK3)) = iProver_top
% 7.35/1.50      | r2_hidden(k3_subset_1(sK2,X0),sK3) != iProver_top
% 7.35/1.50      | r1_tarski(X0,sK2) != iProver_top ),
% 7.35/1.50      inference(global_propositional_subsumption,
% 7.35/1.50                [status(thm)],
% 7.35/1.50                [c_2573,c_23,c_1569]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_23961,plain,
% 7.35/1.50      ( r2_hidden(X0,k1_xboole_0) = iProver_top
% 7.35/1.50      | r2_hidden(k3_subset_1(sK2,X0),sK3) != iProver_top
% 7.35/1.50      | r1_tarski(X0,sK2) != iProver_top ),
% 7.35/1.50      inference(demodulation,[status(thm)],[c_23869,c_2716]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_3,plain,
% 7.35/1.50      ( r1_tarski(k1_xboole_0,X0) ),
% 7.35/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_551,plain,
% 7.35/1.50      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 7.35/1.50      inference(resolution_lifted,[status(thm)],[c_3,c_15]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_552,plain,
% 7.35/1.50      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.35/1.50      inference(unflattening,[status(thm)],[c_551]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_553,plain,
% 7.35/1.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_25962,plain,
% 7.35/1.50      ( r2_hidden(k3_subset_1(sK2,X0),sK3) != iProver_top
% 7.35/1.50      | r1_tarski(X0,sK2) != iProver_top ),
% 7.35/1.50      inference(global_propositional_subsumption,
% 7.35/1.50                [status(thm)],
% 7.35/1.50                [c_23961,c_553]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_25970,plain,
% 7.35/1.50      ( r2_hidden(X0,sK3) != iProver_top
% 7.35/1.50      | r1_tarski(k3_subset_1(sK2,X0),sK2) != iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_2782,c_25962]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_26666,plain,
% 7.35/1.50      ( r2_hidden(X0,sK3) != iProver_top ),
% 7.35/1.50      inference(global_propositional_subsumption,
% 7.35/1.50                [status(thm)],
% 7.35/1.50                [c_14582,c_13916,c_25970]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_26671,plain,
% 7.35/1.50      ( r1_tarski(sK3,X0) = iProver_top ),
% 7.35/1.50      inference(superposition,[status(thm)],[c_1406,c_26666]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_26688,plain,
% 7.35/1.50      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 7.35/1.50      inference(instantiation,[status(thm)],[c_26671]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_4,plain,
% 7.35/1.50      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 7.35/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1549,plain,
% 7.35/1.50      ( ~ r1_tarski(sK3,k1_xboole_0) | k1_xboole_0 = sK3 ),
% 7.35/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_1550,plain,
% 7.35/1.50      ( k1_xboole_0 = sK3 | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 7.35/1.50      inference(predicate_to_equality,[status(thm)],[c_1549]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(c_21,negated_conjecture,
% 7.35/1.50      ( k1_xboole_0 != sK3 ),
% 7.35/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.35/1.50  
% 7.35/1.50  cnf(contradiction,plain,
% 7.35/1.50      ( $false ),
% 7.35/1.50      inference(minisat,[status(thm)],[c_26688,c_1550,c_21]) ).
% 7.35/1.50  
% 7.35/1.50  
% 7.35/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.35/1.50  
% 7.35/1.50  ------                               Statistics
% 7.35/1.50  
% 7.35/1.50  ------ General
% 7.35/1.50  
% 7.35/1.50  abstr_ref_over_cycles:                  0
% 7.35/1.50  abstr_ref_under_cycles:                 0
% 7.35/1.50  gc_basic_clause_elim:                   0
% 7.35/1.50  forced_gc_time:                         0
% 7.35/1.50  parsing_time:                           0.008
% 7.35/1.50  unif_index_cands_time:                  0.
% 7.35/1.50  unif_index_add_time:                    0.
% 7.35/1.50  orderings_time:                         0.
% 7.35/1.50  out_proof_time:                         0.011
% 7.35/1.50  total_time:                             0.748
% 7.35/1.50  num_of_symbols:                         45
% 7.35/1.50  num_of_terms:                           17450
% 7.35/1.50  
% 7.35/1.50  ------ Preprocessing
% 7.35/1.50  
% 7.35/1.50  num_of_splits:                          0
% 7.35/1.50  num_of_split_atoms:                     0
% 7.35/1.50  num_of_reused_defs:                     0
% 7.35/1.50  num_eq_ax_congr_red:                    8
% 7.35/1.50  num_of_sem_filtered_clauses:            1
% 7.35/1.50  num_of_subtypes:                        0
% 7.35/1.50  monotx_restored_types:                  0
% 7.35/1.50  sat_num_of_epr_types:                   0
% 7.35/1.50  sat_num_of_non_cyclic_types:            0
% 7.35/1.50  sat_guarded_non_collapsed_types:        0
% 7.35/1.50  num_pure_diseq_elim:                    0
% 7.35/1.50  simp_replaced_by:                       0
% 7.35/1.50  res_preprocessed:                       90
% 7.35/1.50  prep_upred:                             0
% 7.35/1.50  prep_unflattend:                        80
% 7.35/1.50  smt_new_axioms:                         0
% 7.35/1.50  pred_elim_cands:                        3
% 7.35/1.50  pred_elim:                              0
% 7.35/1.50  pred_elim_cl:                           0
% 7.35/1.50  pred_elim_cycles:                       2
% 7.35/1.50  merged_defs:                            6
% 7.35/1.50  merged_defs_ncl:                        0
% 7.35/1.50  bin_hyper_res:                          9
% 7.35/1.50  prep_cycles:                            3
% 7.35/1.50  pred_elim_time:                         0.009
% 7.35/1.50  splitting_time:                         0.
% 7.35/1.50  sem_filter_time:                        0.
% 7.35/1.50  monotx_time:                            0.
% 7.35/1.50  subtype_inf_time:                       0.
% 7.35/1.50  
% 7.35/1.50  ------ Problem properties
% 7.35/1.50  
% 7.35/1.50  clauses:                                23
% 7.35/1.50  conjectures:                            3
% 7.35/1.50  epr:                                    5
% 7.35/1.50  horn:                                   20
% 7.35/1.50  ground:                                 3
% 7.35/1.50  unary:                                  4
% 7.35/1.50  binary:                                 13
% 7.35/1.50  lits:                                   49
% 7.35/1.50  lits_eq:                                13
% 7.35/1.50  fd_pure:                                0
% 7.35/1.50  fd_pseudo:                              0
% 7.35/1.50  fd_cond:                                3
% 7.35/1.50  fd_pseudo_cond:                         0
% 7.35/1.50  ac_symbols:                             0
% 7.35/1.50  
% 7.35/1.50  ------ Propositional Solver
% 7.35/1.50  
% 7.35/1.50  prop_solver_calls:                      28
% 7.35/1.50  prop_fast_solver_calls:                 1239
% 7.35/1.50  smt_solver_calls:                       0
% 7.35/1.50  smt_fast_solver_calls:                  0
% 7.35/1.50  prop_num_of_clauses:                    8333
% 7.35/1.50  prop_preprocess_simplified:             12419
% 7.35/1.50  prop_fo_subsumed:                       37
% 7.35/1.50  prop_solver_time:                       0.
% 7.35/1.50  smt_solver_time:                        0.
% 7.35/1.50  smt_fast_solver_time:                   0.
% 7.35/1.50  prop_fast_solver_time:                  0.
% 7.35/1.50  prop_unsat_core_time:                   0.
% 7.35/1.50  
% 7.35/1.50  ------ QBF
% 7.35/1.50  
% 7.35/1.50  qbf_q_res:                              0
% 7.35/1.50  qbf_num_tautologies:                    0
% 7.35/1.50  qbf_prep_cycles:                        0
% 7.35/1.50  
% 7.35/1.50  ------ BMC1
% 7.35/1.50  
% 7.35/1.50  bmc1_current_bound:                     -1
% 7.35/1.50  bmc1_last_solved_bound:                 -1
% 7.35/1.50  bmc1_unsat_core_size:                   -1
% 7.35/1.50  bmc1_unsat_core_parents_size:           -1
% 7.35/1.50  bmc1_merge_next_fun:                    0
% 7.35/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.35/1.50  
% 7.35/1.50  ------ Instantiation
% 7.35/1.50  
% 7.35/1.50  inst_num_of_clauses:                    2273
% 7.35/1.50  inst_num_in_passive:                    92
% 7.35/1.50  inst_num_in_active:                     1109
% 7.35/1.50  inst_num_in_unprocessed:                1072
% 7.35/1.50  inst_num_of_loops:                      1260
% 7.35/1.50  inst_num_of_learning_restarts:          0
% 7.35/1.50  inst_num_moves_active_passive:          146
% 7.35/1.50  inst_lit_activity:                      0
% 7.35/1.50  inst_lit_activity_moves:                0
% 7.35/1.50  inst_num_tautologies:                   0
% 7.35/1.50  inst_num_prop_implied:                  0
% 7.35/1.50  inst_num_existing_simplified:           0
% 7.35/1.50  inst_num_eq_res_simplified:             0
% 7.35/1.50  inst_num_child_elim:                    0
% 7.35/1.50  inst_num_of_dismatching_blockings:      1175
% 7.35/1.50  inst_num_of_non_proper_insts:           2667
% 7.35/1.50  inst_num_of_duplicates:                 0
% 7.35/1.50  inst_inst_num_from_inst_to_res:         0
% 7.35/1.50  inst_dismatching_checking_time:         0.
% 7.35/1.50  
% 7.35/1.50  ------ Resolution
% 7.35/1.50  
% 7.35/1.50  res_num_of_clauses:                     0
% 7.35/1.50  res_num_in_passive:                     0
% 7.35/1.50  res_num_in_active:                      0
% 7.35/1.50  res_num_of_loops:                       93
% 7.35/1.50  res_forward_subset_subsumed:            114
% 7.35/1.50  res_backward_subset_subsumed:           1
% 7.35/1.50  res_forward_subsumed:                   1
% 7.35/1.50  res_backward_subsumed:                  3
% 7.35/1.50  res_forward_subsumption_resolution:     1
% 7.35/1.50  res_backward_subsumption_resolution:    0
% 7.35/1.50  res_clause_to_clause_subsumption:       6296
% 7.35/1.50  res_orphan_elimination:                 0
% 7.35/1.50  res_tautology_del:                      231
% 7.35/1.50  res_num_eq_res_simplified:              0
% 7.35/1.50  res_num_sel_changes:                    0
% 7.35/1.50  res_moves_from_active_to_pass:          0
% 7.35/1.50  
% 7.35/1.50  ------ Superposition
% 7.35/1.50  
% 7.35/1.50  sup_time_total:                         0.
% 7.35/1.50  sup_time_generating:                    0.
% 7.35/1.50  sup_time_sim_full:                      0.
% 7.35/1.50  sup_time_sim_immed:                     0.
% 7.35/1.50  
% 7.35/1.50  sup_num_of_clauses:                     777
% 7.35/1.50  sup_num_in_active:                      143
% 7.35/1.50  sup_num_in_passive:                     634
% 7.35/1.50  sup_num_of_loops:                       250
% 7.35/1.50  sup_fw_superposition:                   735
% 7.35/1.50  sup_bw_superposition:                   717
% 7.35/1.50  sup_immediate_simplified:               479
% 7.35/1.50  sup_given_eliminated:                   0
% 7.35/1.50  comparisons_done:                       0
% 7.35/1.50  comparisons_avoided:                    28
% 7.35/1.50  
% 7.35/1.50  ------ Simplifications
% 7.35/1.50  
% 7.35/1.50  
% 7.35/1.50  sim_fw_subset_subsumed:                 115
% 7.35/1.50  sim_bw_subset_subsumed:                 104
% 7.35/1.50  sim_fw_subsumed:                        258
% 7.35/1.50  sim_bw_subsumed:                        6
% 7.35/1.50  sim_fw_subsumption_res:                 1
% 7.35/1.50  sim_bw_subsumption_res:                 1
% 7.35/1.50  sim_tautology_del:                      30
% 7.35/1.50  sim_eq_tautology_del:                   22
% 7.35/1.50  sim_eq_res_simp:                        0
% 7.35/1.50  sim_fw_demodulated:                     25
% 7.35/1.50  sim_bw_demodulated:                     94
% 7.35/1.50  sim_light_normalised:                   120
% 7.35/1.50  sim_joinable_taut:                      0
% 7.35/1.50  sim_joinable_simp:                      0
% 7.35/1.50  sim_ac_normalised:                      0
% 7.35/1.50  sim_smt_subsumption:                    0
% 7.35/1.50  
%------------------------------------------------------------------------------
