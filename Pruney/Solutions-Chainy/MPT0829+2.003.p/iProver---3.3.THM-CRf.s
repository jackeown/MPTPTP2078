%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:20 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 285 expanded)
%              Number of clauses        :   65 ( 104 expanded)
%              Number of leaves         :   14 (  53 expanded)
%              Depth                    :   17
%              Number of atoms          :  297 ( 896 expanded)
%              Number of equality atoms :  108 ( 201 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k2_relset_1(sK1,sK2,sK3) != sK2
        | ~ r1_tarski(sK2,k1_relset_1(sK1,sK2,sK3)) )
      & r1_tarski(k6_relat_1(sK2),sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( k2_relset_1(sK1,sK2,sK3) != sK2
      | ~ r1_tarski(sK2,k1_relset_1(sK1,sK2,sK3)) )
    & r1_tarski(k6_relat_1(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f34])).

fof(f58,plain,(
    r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f15])).

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

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    | ~ r1_tarski(sK2,k1_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_13,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1311,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1315,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1306,plain,
    ( r1_tarski(k6_relat_1(sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1318,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1317,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3196,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1318,c_1317])).

cnf(c_5608,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3196,c_1317])).

cnf(c_6871,plain,
    ( r2_hidden(sK0(X0,X1),sK3) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k6_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1306,c_5608])).

cnf(c_7112,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k6_relat_1(sK2)) != iProver_top
    | r1_tarski(sK3,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6871,c_1317])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1319,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7591,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k6_relat_1(sK2)) != iProver_top
    | r1_tarski(sK3,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7112,c_1319])).

cnf(c_8924,plain,
    ( r1_tarski(k6_relat_1(sK2),X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_7591])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1314,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_293,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_9])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_297,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_293,c_16])).

cnf(c_298,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_297])).

cnf(c_1304,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_2090,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_1304])).

cnf(c_9048,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK2)),X0) = iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8924,c_2090])).

cnf(c_15,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_9120,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(X0,X1)) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9048,c_15])).

cnf(c_10534,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_9120])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_11])).

cnf(c_318,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_314,c_16])).

cnf(c_319,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_318])).

cnf(c_1303,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_1650,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_1303])).

cnf(c_9049,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK2)),X0) = iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8924,c_1650])).

cnf(c_14,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_9115,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(X0,X1)) != iProver_top
    | r1_tarski(sK2,X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9049,c_14])).

cnf(c_9235,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_9115])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1305,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1308,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2270,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1305,c_1308])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(sK2,k1_relset_1(sK1,sK2,sK3))
    | k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1307,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    | r1_tarski(sK2,k1_relset_1(sK1,sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2758,plain,
    ( k2_relat_1(sK3) != sK2
    | r1_tarski(sK2,k1_relset_1(sK1,sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2270,c_1307])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1309,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2388,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1305,c_1309])).

cnf(c_3125,plain,
    ( k2_relat_1(sK3) != sK2
    | r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2758,c_2388])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2318,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK3))
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | k2_relat_1(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2319,plain,
    ( k2_relat_1(sK3) = X0
    | r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2318])).

cnf(c_2321,plain,
    ( k2_relat_1(sK3) = sK2
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2319])).

cnf(c_1464,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_1465,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1464])).

cnf(c_1441,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1442,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1441])).

cnf(c_24,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10534,c_9235,c_3125,c_2321,c_1465,c_1442,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.32  % Computer   : n013.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 14:24:54 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.72/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/0.98  
% 3.72/0.98  ------  iProver source info
% 3.72/0.98  
% 3.72/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.72/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/0.98  git: non_committed_changes: false
% 3.72/0.98  git: last_make_outside_of_git: false
% 3.72/0.98  
% 3.72/0.98  ------ 
% 3.72/0.98  
% 3.72/0.98  ------ Input Options
% 3.72/0.98  
% 3.72/0.98  --out_options                           all
% 3.72/0.98  --tptp_safe_out                         true
% 3.72/0.98  --problem_path                          ""
% 3.72/0.98  --include_path                          ""
% 3.72/0.98  --clausifier                            res/vclausify_rel
% 3.72/0.98  --clausifier_options                    --mode clausify
% 3.72/0.98  --stdin                                 false
% 3.72/0.98  --stats_out                             all
% 3.72/0.98  
% 3.72/0.98  ------ General Options
% 3.72/0.98  
% 3.72/0.98  --fof                                   false
% 3.72/0.98  --time_out_real                         305.
% 3.72/0.98  --time_out_virtual                      -1.
% 3.72/0.98  --symbol_type_check                     false
% 3.72/0.98  --clausify_out                          false
% 3.72/0.98  --sig_cnt_out                           false
% 3.72/0.98  --trig_cnt_out                          false
% 3.72/0.98  --trig_cnt_out_tolerance                1.
% 3.72/0.98  --trig_cnt_out_sk_spl                   false
% 3.72/0.98  --abstr_cl_out                          false
% 3.72/0.98  
% 3.72/0.98  ------ Global Options
% 3.72/0.98  
% 3.72/0.98  --schedule                              default
% 3.72/0.98  --add_important_lit                     false
% 3.72/0.98  --prop_solver_per_cl                    1000
% 3.72/0.98  --min_unsat_core                        false
% 3.72/0.98  --soft_assumptions                      false
% 3.72/0.98  --soft_lemma_size                       3
% 3.72/0.98  --prop_impl_unit_size                   0
% 3.72/0.98  --prop_impl_unit                        []
% 3.72/0.98  --share_sel_clauses                     true
% 3.72/0.98  --reset_solvers                         false
% 3.72/0.98  --bc_imp_inh                            [conj_cone]
% 3.72/0.98  --conj_cone_tolerance                   3.
% 3.72/0.98  --extra_neg_conj                        none
% 3.72/0.98  --large_theory_mode                     true
% 3.72/0.98  --prolific_symb_bound                   200
% 3.72/0.98  --lt_threshold                          2000
% 3.72/0.98  --clause_weak_htbl                      true
% 3.72/0.98  --gc_record_bc_elim                     false
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing Options
% 3.72/0.98  
% 3.72/0.98  --preprocessing_flag                    true
% 3.72/0.98  --time_out_prep_mult                    0.1
% 3.72/0.98  --splitting_mode                        input
% 3.72/0.98  --splitting_grd                         true
% 3.72/0.98  --splitting_cvd                         false
% 3.72/0.98  --splitting_cvd_svl                     false
% 3.72/0.98  --splitting_nvd                         32
% 3.72/0.98  --sub_typing                            true
% 3.72/0.98  --prep_gs_sim                           true
% 3.72/0.98  --prep_unflatten                        true
% 3.72/0.98  --prep_res_sim                          true
% 3.72/0.98  --prep_upred                            true
% 3.72/0.98  --prep_sem_filter                       exhaustive
% 3.72/0.98  --prep_sem_filter_out                   false
% 3.72/0.98  --pred_elim                             true
% 3.72/0.98  --res_sim_input                         true
% 3.72/0.98  --eq_ax_congr_red                       true
% 3.72/0.98  --pure_diseq_elim                       true
% 3.72/0.98  --brand_transform                       false
% 3.72/0.98  --non_eq_to_eq                          false
% 3.72/0.98  --prep_def_merge                        true
% 3.72/0.98  --prep_def_merge_prop_impl              false
% 3.72/0.98  --prep_def_merge_mbd                    true
% 3.72/0.98  --prep_def_merge_tr_red                 false
% 3.72/0.98  --prep_def_merge_tr_cl                  false
% 3.72/0.98  --smt_preprocessing                     true
% 3.72/0.98  --smt_ac_axioms                         fast
% 3.72/0.98  --preprocessed_out                      false
% 3.72/0.98  --preprocessed_stats                    false
% 3.72/0.98  
% 3.72/0.98  ------ Abstraction refinement Options
% 3.72/0.98  
% 3.72/0.98  --abstr_ref                             []
% 3.72/0.98  --abstr_ref_prep                        false
% 3.72/0.98  --abstr_ref_until_sat                   false
% 3.72/0.98  --abstr_ref_sig_restrict                funpre
% 3.72/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/0.98  --abstr_ref_under                       []
% 3.72/0.98  
% 3.72/0.98  ------ SAT Options
% 3.72/0.98  
% 3.72/0.98  --sat_mode                              false
% 3.72/0.98  --sat_fm_restart_options                ""
% 3.72/0.98  --sat_gr_def                            false
% 3.72/0.98  --sat_epr_types                         true
% 3.72/0.98  --sat_non_cyclic_types                  false
% 3.72/0.98  --sat_finite_models                     false
% 3.72/0.98  --sat_fm_lemmas                         false
% 3.72/0.98  --sat_fm_prep                           false
% 3.72/0.98  --sat_fm_uc_incr                        true
% 3.72/0.98  --sat_out_model                         small
% 3.72/0.98  --sat_out_clauses                       false
% 3.72/0.98  
% 3.72/0.98  ------ QBF Options
% 3.72/0.98  
% 3.72/0.98  --qbf_mode                              false
% 3.72/0.98  --qbf_elim_univ                         false
% 3.72/0.98  --qbf_dom_inst                          none
% 3.72/0.98  --qbf_dom_pre_inst                      false
% 3.72/0.98  --qbf_sk_in                             false
% 3.72/0.98  --qbf_pred_elim                         true
% 3.72/0.98  --qbf_split                             512
% 3.72/0.98  
% 3.72/0.98  ------ BMC1 Options
% 3.72/0.98  
% 3.72/0.98  --bmc1_incremental                      false
% 3.72/0.98  --bmc1_axioms                           reachable_all
% 3.72/0.98  --bmc1_min_bound                        0
% 3.72/0.98  --bmc1_max_bound                        -1
% 3.72/0.98  --bmc1_max_bound_default                -1
% 3.72/0.98  --bmc1_symbol_reachability              true
% 3.72/0.98  --bmc1_property_lemmas                  false
% 3.72/0.98  --bmc1_k_induction                      false
% 3.72/0.98  --bmc1_non_equiv_states                 false
% 3.72/0.98  --bmc1_deadlock                         false
% 3.72/0.98  --bmc1_ucm                              false
% 3.72/0.98  --bmc1_add_unsat_core                   none
% 3.72/0.98  --bmc1_unsat_core_children              false
% 3.72/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/0.98  --bmc1_out_stat                         full
% 3.72/0.98  --bmc1_ground_init                      false
% 3.72/0.98  --bmc1_pre_inst_next_state              false
% 3.72/0.98  --bmc1_pre_inst_state                   false
% 3.72/0.98  --bmc1_pre_inst_reach_state             false
% 3.72/0.98  --bmc1_out_unsat_core                   false
% 3.72/0.98  --bmc1_aig_witness_out                  false
% 3.72/0.98  --bmc1_verbose                          false
% 3.72/0.98  --bmc1_dump_clauses_tptp                false
% 3.72/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.72/0.98  --bmc1_dump_file                        -
% 3.72/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.72/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.72/0.98  --bmc1_ucm_extend_mode                  1
% 3.72/0.98  --bmc1_ucm_init_mode                    2
% 3.72/0.98  --bmc1_ucm_cone_mode                    none
% 3.72/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.72/0.98  --bmc1_ucm_relax_model                  4
% 3.72/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.72/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/0.98  --bmc1_ucm_layered_model                none
% 3.72/0.98  --bmc1_ucm_max_lemma_size               10
% 3.72/0.98  
% 3.72/0.98  ------ AIG Options
% 3.72/0.98  
% 3.72/0.98  --aig_mode                              false
% 3.72/0.98  
% 3.72/0.98  ------ Instantiation Options
% 3.72/0.98  
% 3.72/0.98  --instantiation_flag                    true
% 3.72/0.98  --inst_sos_flag                         false
% 3.72/0.98  --inst_sos_phase                        true
% 3.72/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/0.98  --inst_lit_sel_side                     num_symb
% 3.72/0.98  --inst_solver_per_active                1400
% 3.72/0.98  --inst_solver_calls_frac                1.
% 3.72/0.98  --inst_passive_queue_type               priority_queues
% 3.72/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/0.98  --inst_passive_queues_freq              [25;2]
% 3.72/0.98  --inst_dismatching                      true
% 3.72/0.98  --inst_eager_unprocessed_to_passive     true
% 3.72/0.98  --inst_prop_sim_given                   true
% 3.72/0.98  --inst_prop_sim_new                     false
% 3.72/0.98  --inst_subs_new                         false
% 3.72/0.98  --inst_eq_res_simp                      false
% 3.72/0.98  --inst_subs_given                       false
% 3.72/0.98  --inst_orphan_elimination               true
% 3.72/0.98  --inst_learning_loop_flag               true
% 3.72/0.98  --inst_learning_start                   3000
% 3.72/0.98  --inst_learning_factor                  2
% 3.72/0.98  --inst_start_prop_sim_after_learn       3
% 3.72/0.98  --inst_sel_renew                        solver
% 3.72/0.98  --inst_lit_activity_flag                true
% 3.72/0.98  --inst_restr_to_given                   false
% 3.72/0.98  --inst_activity_threshold               500
% 3.72/0.98  --inst_out_proof                        true
% 3.72/0.98  
% 3.72/0.98  ------ Resolution Options
% 3.72/0.98  
% 3.72/0.98  --resolution_flag                       true
% 3.72/0.98  --res_lit_sel                           adaptive
% 3.72/0.98  --res_lit_sel_side                      none
% 3.72/0.98  --res_ordering                          kbo
% 3.72/0.98  --res_to_prop_solver                    active
% 3.72/0.98  --res_prop_simpl_new                    false
% 3.72/0.98  --res_prop_simpl_given                  true
% 3.72/0.98  --res_passive_queue_type                priority_queues
% 3.72/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/0.98  --res_passive_queues_freq               [15;5]
% 3.72/0.98  --res_forward_subs                      full
% 3.72/0.98  --res_backward_subs                     full
% 3.72/0.98  --res_forward_subs_resolution           true
% 3.72/0.98  --res_backward_subs_resolution          true
% 3.72/0.98  --res_orphan_elimination                true
% 3.72/0.98  --res_time_limit                        2.
% 3.72/0.98  --res_out_proof                         true
% 3.72/0.98  
% 3.72/0.98  ------ Superposition Options
% 3.72/0.98  
% 3.72/0.98  --superposition_flag                    true
% 3.72/0.98  --sup_passive_queue_type                priority_queues
% 3.72/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.72/0.98  --demod_completeness_check              fast
% 3.72/0.98  --demod_use_ground                      true
% 3.72/0.98  --sup_to_prop_solver                    passive
% 3.72/0.98  --sup_prop_simpl_new                    true
% 3.72/0.98  --sup_prop_simpl_given                  true
% 3.72/0.98  --sup_fun_splitting                     false
% 3.72/0.98  --sup_smt_interval                      50000
% 3.72/0.98  
% 3.72/0.98  ------ Superposition Simplification Setup
% 3.72/0.98  
% 3.72/0.98  --sup_indices_passive                   []
% 3.72/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_full_bw                           [BwDemod]
% 3.72/0.98  --sup_immed_triv                        [TrivRules]
% 3.72/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_immed_bw_main                     []
% 3.72/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/0.98  
% 3.72/0.98  ------ Combination Options
% 3.72/0.98  
% 3.72/0.98  --comb_res_mult                         3
% 3.72/0.98  --comb_sup_mult                         2
% 3.72/0.98  --comb_inst_mult                        10
% 3.72/0.98  
% 3.72/0.98  ------ Debug Options
% 3.72/0.98  
% 3.72/0.98  --dbg_backtrace                         false
% 3.72/0.98  --dbg_dump_prop_clauses                 false
% 3.72/0.98  --dbg_dump_prop_clauses_file            -
% 3.72/0.98  --dbg_out_stat                          false
% 3.72/0.98  ------ Parsing...
% 3.72/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/0.98  ------ Proving...
% 3.72/0.98  ------ Problem Properties 
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  clauses                                 19
% 3.72/0.98  conjectures                             3
% 3.72/0.98  EPR                                     3
% 3.72/0.98  Horn                                    18
% 3.72/0.98  unary                                   6
% 3.72/0.98  binary                                  11
% 3.72/0.98  lits                                    34
% 3.72/0.98  lits eq                                 6
% 3.72/0.98  fd_pure                                 0
% 3.72/0.98  fd_pseudo                               0
% 3.72/0.98  fd_cond                                 0
% 3.72/0.98  fd_pseudo_cond                          1
% 3.72/0.98  AC symbols                              0
% 3.72/0.98  
% 3.72/0.98  ------ Schedule dynamic 5 is on 
% 3.72/0.98  
% 3.72/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  ------ 
% 3.72/0.98  Current options:
% 3.72/0.98  ------ 
% 3.72/0.98  
% 3.72/0.98  ------ Input Options
% 3.72/0.98  
% 3.72/0.98  --out_options                           all
% 3.72/0.98  --tptp_safe_out                         true
% 3.72/0.98  --problem_path                          ""
% 3.72/0.98  --include_path                          ""
% 3.72/0.98  --clausifier                            res/vclausify_rel
% 3.72/0.98  --clausifier_options                    --mode clausify
% 3.72/0.98  --stdin                                 false
% 3.72/0.98  --stats_out                             all
% 3.72/0.98  
% 3.72/0.98  ------ General Options
% 3.72/0.98  
% 3.72/0.98  --fof                                   false
% 3.72/0.98  --time_out_real                         305.
% 3.72/0.98  --time_out_virtual                      -1.
% 3.72/0.98  --symbol_type_check                     false
% 3.72/0.98  --clausify_out                          false
% 3.72/0.98  --sig_cnt_out                           false
% 3.72/0.98  --trig_cnt_out                          false
% 3.72/0.98  --trig_cnt_out_tolerance                1.
% 3.72/0.98  --trig_cnt_out_sk_spl                   false
% 3.72/0.98  --abstr_cl_out                          false
% 3.72/0.98  
% 3.72/0.98  ------ Global Options
% 3.72/0.98  
% 3.72/0.98  --schedule                              default
% 3.72/0.98  --add_important_lit                     false
% 3.72/0.98  --prop_solver_per_cl                    1000
% 3.72/0.98  --min_unsat_core                        false
% 3.72/0.98  --soft_assumptions                      false
% 3.72/0.98  --soft_lemma_size                       3
% 3.72/0.98  --prop_impl_unit_size                   0
% 3.72/0.98  --prop_impl_unit                        []
% 3.72/0.98  --share_sel_clauses                     true
% 3.72/0.98  --reset_solvers                         false
% 3.72/0.98  --bc_imp_inh                            [conj_cone]
% 3.72/0.98  --conj_cone_tolerance                   3.
% 3.72/0.98  --extra_neg_conj                        none
% 3.72/0.98  --large_theory_mode                     true
% 3.72/0.98  --prolific_symb_bound                   200
% 3.72/0.98  --lt_threshold                          2000
% 3.72/0.98  --clause_weak_htbl                      true
% 3.72/0.98  --gc_record_bc_elim                     false
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing Options
% 3.72/0.98  
% 3.72/0.98  --preprocessing_flag                    true
% 3.72/0.98  --time_out_prep_mult                    0.1
% 3.72/0.98  --splitting_mode                        input
% 3.72/0.98  --splitting_grd                         true
% 3.72/0.98  --splitting_cvd                         false
% 3.72/0.98  --splitting_cvd_svl                     false
% 3.72/0.98  --splitting_nvd                         32
% 3.72/0.98  --sub_typing                            true
% 3.72/0.98  --prep_gs_sim                           true
% 3.72/0.98  --prep_unflatten                        true
% 3.72/0.98  --prep_res_sim                          true
% 3.72/0.98  --prep_upred                            true
% 3.72/0.98  --prep_sem_filter                       exhaustive
% 3.72/0.98  --prep_sem_filter_out                   false
% 3.72/0.98  --pred_elim                             true
% 3.72/0.98  --res_sim_input                         true
% 3.72/0.98  --eq_ax_congr_red                       true
% 3.72/0.98  --pure_diseq_elim                       true
% 3.72/0.98  --brand_transform                       false
% 3.72/0.98  --non_eq_to_eq                          false
% 3.72/0.98  --prep_def_merge                        true
% 3.72/0.98  --prep_def_merge_prop_impl              false
% 3.72/0.98  --prep_def_merge_mbd                    true
% 3.72/0.98  --prep_def_merge_tr_red                 false
% 3.72/0.98  --prep_def_merge_tr_cl                  false
% 3.72/0.98  --smt_preprocessing                     true
% 3.72/0.98  --smt_ac_axioms                         fast
% 3.72/0.98  --preprocessed_out                      false
% 3.72/0.98  --preprocessed_stats                    false
% 3.72/0.98  
% 3.72/0.98  ------ Abstraction refinement Options
% 3.72/0.98  
% 3.72/0.98  --abstr_ref                             []
% 3.72/0.98  --abstr_ref_prep                        false
% 3.72/0.98  --abstr_ref_until_sat                   false
% 3.72/0.98  --abstr_ref_sig_restrict                funpre
% 3.72/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/0.98  --abstr_ref_under                       []
% 3.72/0.98  
% 3.72/0.98  ------ SAT Options
% 3.72/0.98  
% 3.72/0.98  --sat_mode                              false
% 3.72/0.98  --sat_fm_restart_options                ""
% 3.72/0.98  --sat_gr_def                            false
% 3.72/0.98  --sat_epr_types                         true
% 3.72/0.98  --sat_non_cyclic_types                  false
% 3.72/0.98  --sat_finite_models                     false
% 3.72/0.98  --sat_fm_lemmas                         false
% 3.72/0.98  --sat_fm_prep                           false
% 3.72/0.98  --sat_fm_uc_incr                        true
% 3.72/0.98  --sat_out_model                         small
% 3.72/0.98  --sat_out_clauses                       false
% 3.72/0.98  
% 3.72/0.98  ------ QBF Options
% 3.72/0.98  
% 3.72/0.98  --qbf_mode                              false
% 3.72/0.98  --qbf_elim_univ                         false
% 3.72/0.98  --qbf_dom_inst                          none
% 3.72/0.98  --qbf_dom_pre_inst                      false
% 3.72/0.98  --qbf_sk_in                             false
% 3.72/0.98  --qbf_pred_elim                         true
% 3.72/0.98  --qbf_split                             512
% 3.72/0.98  
% 3.72/0.98  ------ BMC1 Options
% 3.72/0.98  
% 3.72/0.98  --bmc1_incremental                      false
% 3.72/0.98  --bmc1_axioms                           reachable_all
% 3.72/0.98  --bmc1_min_bound                        0
% 3.72/0.98  --bmc1_max_bound                        -1
% 3.72/0.98  --bmc1_max_bound_default                -1
% 3.72/0.98  --bmc1_symbol_reachability              true
% 3.72/0.98  --bmc1_property_lemmas                  false
% 3.72/0.98  --bmc1_k_induction                      false
% 3.72/0.98  --bmc1_non_equiv_states                 false
% 3.72/0.98  --bmc1_deadlock                         false
% 3.72/0.98  --bmc1_ucm                              false
% 3.72/0.98  --bmc1_add_unsat_core                   none
% 3.72/0.98  --bmc1_unsat_core_children              false
% 3.72/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/0.98  --bmc1_out_stat                         full
% 3.72/0.98  --bmc1_ground_init                      false
% 3.72/0.98  --bmc1_pre_inst_next_state              false
% 3.72/0.98  --bmc1_pre_inst_state                   false
% 3.72/0.98  --bmc1_pre_inst_reach_state             false
% 3.72/0.98  --bmc1_out_unsat_core                   false
% 3.72/0.98  --bmc1_aig_witness_out                  false
% 3.72/0.98  --bmc1_verbose                          false
% 3.72/0.98  --bmc1_dump_clauses_tptp                false
% 3.72/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.72/0.98  --bmc1_dump_file                        -
% 3.72/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.72/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.72/0.98  --bmc1_ucm_extend_mode                  1
% 3.72/0.98  --bmc1_ucm_init_mode                    2
% 3.72/0.98  --bmc1_ucm_cone_mode                    none
% 3.72/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.72/0.98  --bmc1_ucm_relax_model                  4
% 3.72/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.72/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/0.98  --bmc1_ucm_layered_model                none
% 3.72/0.98  --bmc1_ucm_max_lemma_size               10
% 3.72/0.98  
% 3.72/0.98  ------ AIG Options
% 3.72/0.98  
% 3.72/0.98  --aig_mode                              false
% 3.72/0.98  
% 3.72/0.98  ------ Instantiation Options
% 3.72/0.98  
% 3.72/0.98  --instantiation_flag                    true
% 3.72/0.98  --inst_sos_flag                         false
% 3.72/0.98  --inst_sos_phase                        true
% 3.72/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/0.98  --inst_lit_sel_side                     none
% 3.72/0.98  --inst_solver_per_active                1400
% 3.72/0.98  --inst_solver_calls_frac                1.
% 3.72/0.98  --inst_passive_queue_type               priority_queues
% 3.72/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/0.98  --inst_passive_queues_freq              [25;2]
% 3.72/0.98  --inst_dismatching                      true
% 3.72/0.98  --inst_eager_unprocessed_to_passive     true
% 3.72/0.98  --inst_prop_sim_given                   true
% 3.72/0.98  --inst_prop_sim_new                     false
% 3.72/0.98  --inst_subs_new                         false
% 3.72/0.98  --inst_eq_res_simp                      false
% 3.72/0.98  --inst_subs_given                       false
% 3.72/0.98  --inst_orphan_elimination               true
% 3.72/0.98  --inst_learning_loop_flag               true
% 3.72/0.98  --inst_learning_start                   3000
% 3.72/0.98  --inst_learning_factor                  2
% 3.72/0.98  --inst_start_prop_sim_after_learn       3
% 3.72/0.98  --inst_sel_renew                        solver
% 3.72/0.98  --inst_lit_activity_flag                true
% 3.72/0.98  --inst_restr_to_given                   false
% 3.72/0.98  --inst_activity_threshold               500
% 3.72/0.98  --inst_out_proof                        true
% 3.72/0.98  
% 3.72/0.98  ------ Resolution Options
% 3.72/0.98  
% 3.72/0.98  --resolution_flag                       false
% 3.72/0.98  --res_lit_sel                           adaptive
% 3.72/0.98  --res_lit_sel_side                      none
% 3.72/0.98  --res_ordering                          kbo
% 3.72/0.98  --res_to_prop_solver                    active
% 3.72/0.98  --res_prop_simpl_new                    false
% 3.72/0.98  --res_prop_simpl_given                  true
% 3.72/0.98  --res_passive_queue_type                priority_queues
% 3.72/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/0.98  --res_passive_queues_freq               [15;5]
% 3.72/0.98  --res_forward_subs                      full
% 3.72/0.98  --res_backward_subs                     full
% 3.72/0.98  --res_forward_subs_resolution           true
% 3.72/0.98  --res_backward_subs_resolution          true
% 3.72/0.98  --res_orphan_elimination                true
% 3.72/0.98  --res_time_limit                        2.
% 3.72/0.98  --res_out_proof                         true
% 3.72/0.98  
% 3.72/0.98  ------ Superposition Options
% 3.72/0.98  
% 3.72/0.98  --superposition_flag                    true
% 3.72/0.98  --sup_passive_queue_type                priority_queues
% 3.72/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.72/0.98  --demod_completeness_check              fast
% 3.72/0.98  --demod_use_ground                      true
% 3.72/0.98  --sup_to_prop_solver                    passive
% 3.72/0.98  --sup_prop_simpl_new                    true
% 3.72/0.98  --sup_prop_simpl_given                  true
% 3.72/0.98  --sup_fun_splitting                     false
% 3.72/0.98  --sup_smt_interval                      50000
% 3.72/0.98  
% 3.72/0.98  ------ Superposition Simplification Setup
% 3.72/0.98  
% 3.72/0.98  --sup_indices_passive                   []
% 3.72/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_full_bw                           [BwDemod]
% 3.72/0.98  --sup_immed_triv                        [TrivRules]
% 3.72/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_immed_bw_main                     []
% 3.72/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/0.98  
% 3.72/0.98  ------ Combination Options
% 3.72/0.98  
% 3.72/0.98  --comb_res_mult                         3
% 3.72/0.98  --comb_sup_mult                         2
% 3.72/0.98  --comb_inst_mult                        10
% 3.72/0.98  
% 3.72/0.98  ------ Debug Options
% 3.72/0.98  
% 3.72/0.98  --dbg_backtrace                         false
% 3.72/0.98  --dbg_dump_prop_clauses                 false
% 3.72/0.98  --dbg_dump_prop_clauses_file            -
% 3.72/0.98  --dbg_out_stat                          false
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  ------ Proving...
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  % SZS status Theorem for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  fof(f7,axiom,(
% 3.72/0.98    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f18,plain,(
% 3.72/0.98    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.72/0.98    inference(ennf_transformation,[],[f7])).
% 3.72/0.98  
% 3.72/0.98  fof(f49,plain,(
% 3.72/0.98    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f18])).
% 3.72/0.98  
% 3.72/0.98  fof(f2,axiom,(
% 3.72/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f29,plain,(
% 3.72/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.72/0.98    inference(nnf_transformation,[],[f2])).
% 3.72/0.98  
% 3.72/0.98  fof(f30,plain,(
% 3.72/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.72/0.98    inference(flattening,[],[f29])).
% 3.72/0.98  
% 3.72/0.98  fof(f40,plain,(
% 3.72/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.72/0.98    inference(cnf_transformation,[],[f30])).
% 3.72/0.98  
% 3.72/0.98  fof(f60,plain,(
% 3.72/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.72/0.98    inference(equality_resolution,[],[f40])).
% 3.72/0.98  
% 3.72/0.98  fof(f13,conjecture,(
% 3.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f14,negated_conjecture,(
% 3.72/0.98    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 3.72/0.98    inference(negated_conjecture,[],[f13])).
% 3.72/0.98  
% 3.72/0.98  fof(f23,plain,(
% 3.72/0.98    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(ennf_transformation,[],[f14])).
% 3.72/0.98  
% 3.72/0.98  fof(f24,plain,(
% 3.72/0.98    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(flattening,[],[f23])).
% 3.72/0.98  
% 3.72/0.98  fof(f34,plain,(
% 3.72/0.98    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k2_relset_1(sK1,sK2,sK3) != sK2 | ~r1_tarski(sK2,k1_relset_1(sK1,sK2,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))))),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f35,plain,(
% 3.72/0.98    (k2_relset_1(sK1,sK2,sK3) != sK2 | ~r1_tarski(sK2,k1_relset_1(sK1,sK2,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.72/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f34])).
% 3.72/0.98  
% 3.72/0.98  fof(f58,plain,(
% 3.72/0.98    r1_tarski(k6_relat_1(sK2),sK3)),
% 3.72/0.98    inference(cnf_transformation,[],[f35])).
% 3.72/0.98  
% 3.72/0.98  fof(f1,axiom,(
% 3.72/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f15,plain,(
% 3.72/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.72/0.98    inference(ennf_transformation,[],[f1])).
% 3.72/0.98  
% 3.72/0.98  fof(f25,plain,(
% 3.72/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.72/0.98    inference(nnf_transformation,[],[f15])).
% 3.72/0.98  
% 3.72/0.98  fof(f26,plain,(
% 3.72/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.72/0.98    inference(rectify,[],[f25])).
% 3.72/0.98  
% 3.72/0.98  fof(f27,plain,(
% 3.72/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.72/0.98    introduced(choice_axiom,[])).
% 3.72/0.98  
% 3.72/0.98  fof(f28,plain,(
% 3.72/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.72/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.72/0.98  
% 3.72/0.98  fof(f37,plain,(
% 3.72/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f28])).
% 3.72/0.98  
% 3.72/0.98  fof(f36,plain,(
% 3.72/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f28])).
% 3.72/0.98  
% 3.72/0.98  fof(f38,plain,(
% 3.72/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f28])).
% 3.72/0.98  
% 3.72/0.98  fof(f3,axiom,(
% 3.72/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f31,plain,(
% 3.72/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.72/0.98    inference(nnf_transformation,[],[f3])).
% 3.72/0.98  
% 3.72/0.98  fof(f43,plain,(
% 3.72/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f31])).
% 3.72/0.98  
% 3.72/0.98  fof(f10,axiom,(
% 3.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f20,plain,(
% 3.72/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(ennf_transformation,[],[f10])).
% 3.72/0.98  
% 3.72/0.98  fof(f53,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f20])).
% 3.72/0.98  
% 3.72/0.98  fof(f4,axiom,(
% 3.72/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f16,plain,(
% 3.72/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.72/0.98    inference(ennf_transformation,[],[f4])).
% 3.72/0.98  
% 3.72/0.98  fof(f32,plain,(
% 3.72/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.72/0.98    inference(nnf_transformation,[],[f16])).
% 3.72/0.98  
% 3.72/0.98  fof(f44,plain,(
% 3.72/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f32])).
% 3.72/0.98  
% 3.72/0.98  fof(f9,axiom,(
% 3.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f19,plain,(
% 3.72/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(ennf_transformation,[],[f9])).
% 3.72/0.98  
% 3.72/0.98  fof(f52,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f19])).
% 3.72/0.98  
% 3.72/0.98  fof(f8,axiom,(
% 3.72/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f50,plain,(
% 3.72/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.72/0.98    inference(cnf_transformation,[],[f8])).
% 3.72/0.98  
% 3.72/0.98  fof(f54,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f20])).
% 3.72/0.98  
% 3.72/0.98  fof(f5,axiom,(
% 3.72/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f17,plain,(
% 3.72/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.72/0.98    inference(ennf_transformation,[],[f5])).
% 3.72/0.98  
% 3.72/0.98  fof(f33,plain,(
% 3.72/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.72/0.98    inference(nnf_transformation,[],[f17])).
% 3.72/0.98  
% 3.72/0.98  fof(f46,plain,(
% 3.72/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f33])).
% 3.72/0.98  
% 3.72/0.98  fof(f51,plain,(
% 3.72/0.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.72/0.98    inference(cnf_transformation,[],[f8])).
% 3.72/0.98  
% 3.72/0.98  fof(f57,plain,(
% 3.72/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.72/0.98    inference(cnf_transformation,[],[f35])).
% 3.72/0.98  
% 3.72/0.98  fof(f12,axiom,(
% 3.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f22,plain,(
% 3.72/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(ennf_transformation,[],[f12])).
% 3.72/0.98  
% 3.72/0.98  fof(f56,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f22])).
% 3.72/0.98  
% 3.72/0.98  fof(f59,plain,(
% 3.72/0.98    k2_relset_1(sK1,sK2,sK3) != sK2 | ~r1_tarski(sK2,k1_relset_1(sK1,sK2,sK3))),
% 3.72/0.98    inference(cnf_transformation,[],[f35])).
% 3.72/0.98  
% 3.72/0.98  fof(f11,axiom,(
% 3.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/0.98  
% 3.72/0.98  fof(f21,plain,(
% 3.72/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.98    inference(ennf_transformation,[],[f11])).
% 3.72/0.98  
% 3.72/0.98  fof(f55,plain,(
% 3.72/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.98    inference(cnf_transformation,[],[f21])).
% 3.72/0.98  
% 3.72/0.98  fof(f41,plain,(
% 3.72/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.72/0.98    inference(cnf_transformation,[],[f30])).
% 3.72/0.98  
% 3.72/0.98  cnf(c_13,plain,
% 3.72/0.98      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 3.72/0.98      | ~ v1_relat_1(X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1311,plain,
% 3.72/0.98      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 3.72/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_4,plain,
% 3.72/0.98      ( r1_tarski(X0,X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1315,plain,
% 3.72/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_22,negated_conjecture,
% 3.72/0.98      ( r1_tarski(k6_relat_1(sK2),sK3) ),
% 3.72/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1306,plain,
% 3.72/0.98      ( r1_tarski(k6_relat_1(sK2),sK3) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1,plain,
% 3.72/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.72/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1318,plain,
% 3.72/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.72/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2,plain,
% 3.72/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.72/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1317,plain,
% 3.72/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.72/0.98      | r2_hidden(X0,X2) = iProver_top
% 3.72/0.98      | r1_tarski(X1,X2) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3196,plain,
% 3.72/0.98      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 3.72/0.98      | r1_tarski(X0,X2) != iProver_top
% 3.72/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1318,c_1317]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_5608,plain,
% 3.72/0.98      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 3.72/0.98      | r1_tarski(X0,X3) != iProver_top
% 3.72/0.98      | r1_tarski(X3,X2) != iProver_top
% 3.72/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_3196,c_1317]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_6871,plain,
% 3.72/0.98      ( r2_hidden(sK0(X0,X1),sK3) = iProver_top
% 3.72/0.98      | r1_tarski(X0,X1) = iProver_top
% 3.72/0.98      | r1_tarski(X0,k6_relat_1(sK2)) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1306,c_5608]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_7112,plain,
% 3.72/0.98      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 3.72/0.98      | r1_tarski(X0,X1) = iProver_top
% 3.72/0.98      | r1_tarski(X0,k6_relat_1(sK2)) != iProver_top
% 3.72/0.98      | r1_tarski(sK3,X2) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_6871,c_1317]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_0,plain,
% 3.72/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.72/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1319,plain,
% 3.72/0.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.72/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_7591,plain,
% 3.72/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.72/0.98      | r1_tarski(X0,k6_relat_1(sK2)) != iProver_top
% 3.72/0.98      | r1_tarski(sK3,X1) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_7112,c_1319]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_8924,plain,
% 3.72/0.98      ( r1_tarski(k6_relat_1(sK2),X0) = iProver_top
% 3.72/0.98      | r1_tarski(sK3,X0) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1315,c_7591]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_6,plain,
% 3.72/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.72/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1314,plain,
% 3.72/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.72/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_18,plain,
% 3.72/0.98      ( v4_relat_1(X0,X1)
% 3.72/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.72/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_9,plain,
% 3.72/0.98      ( ~ v4_relat_1(X0,X1)
% 3.72/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.72/0.98      | ~ v1_relat_1(X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_293,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.72/0.98      | ~ v1_relat_1(X0) ),
% 3.72/0.98      inference(resolution,[status(thm)],[c_18,c_9]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_16,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | v1_relat_1(X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_297,plain,
% 3.72/0.98      ( r1_tarski(k1_relat_1(X0),X1)
% 3.72/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.72/0.98      inference(global_propositional_subsumption,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_293,c_16]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_298,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.72/0.98      inference(renaming,[status(thm)],[c_297]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1304,plain,
% 3.72/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.72/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2090,plain,
% 3.72/0.98      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.72/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1314,c_1304]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_9048,plain,
% 3.72/0.98      ( r1_tarski(k1_relat_1(k6_relat_1(sK2)),X0) = iProver_top
% 3.72/0.98      | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_8924,c_2090]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_15,plain,
% 3.72/0.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.72/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_9120,plain,
% 3.72/0.98      ( r1_tarski(sK3,k2_zfmisc_1(X0,X1)) != iProver_top
% 3.72/0.98      | r1_tarski(sK2,X0) = iProver_top ),
% 3.72/0.98      inference(demodulation,[status(thm)],[c_9048,c_15]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_10534,plain,
% 3.72/0.98      ( r1_tarski(sK2,k1_relat_1(sK3)) = iProver_top
% 3.72/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1311,c_9120]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_17,plain,
% 3.72/0.98      ( v5_relat_1(X0,X1)
% 3.72/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.72/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_11,plain,
% 3.72/0.98      ( ~ v5_relat_1(X0,X1)
% 3.72/0.98      | r1_tarski(k2_relat_1(X0),X1)
% 3.72/0.98      | ~ v1_relat_1(X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_314,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 3.72/0.98      | ~ v1_relat_1(X0) ),
% 3.72/0.98      inference(resolution,[status(thm)],[c_17,c_11]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_318,plain,
% 3.72/0.98      ( r1_tarski(k2_relat_1(X0),X2)
% 3.72/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.72/0.98      inference(global_propositional_subsumption,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_314,c_16]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_319,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.72/0.98      inference(renaming,[status(thm)],[c_318]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1303,plain,
% 3.72/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.72/0.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1650,plain,
% 3.72/0.98      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.72/0.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1314,c_1303]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_9049,plain,
% 3.72/0.98      ( r1_tarski(k2_relat_1(k6_relat_1(sK2)),X0) = iProver_top
% 3.72/0.98      | r1_tarski(sK3,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_8924,c_1650]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_14,plain,
% 3.72/0.98      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.72/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_9115,plain,
% 3.72/0.98      ( r1_tarski(sK3,k2_zfmisc_1(X0,X1)) != iProver_top
% 3.72/0.98      | r1_tarski(sK2,X1) = iProver_top ),
% 3.72/0.98      inference(demodulation,[status(thm)],[c_9049,c_14]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_9235,plain,
% 3.72/0.98      ( r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top
% 3.72/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1311,c_9115]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_23,negated_conjecture,
% 3.72/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.72/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1305,plain,
% 3.72/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_20,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1308,plain,
% 3.72/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.72/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2270,plain,
% 3.72/0.98      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1305,c_1308]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_21,negated_conjecture,
% 3.72/0.98      ( ~ r1_tarski(sK2,k1_relset_1(sK1,sK2,sK3))
% 3.72/0.98      | k2_relset_1(sK1,sK2,sK3) != sK2 ),
% 3.72/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1307,plain,
% 3.72/0.98      ( k2_relset_1(sK1,sK2,sK3) != sK2
% 3.72/0.98      | r1_tarski(sK2,k1_relset_1(sK1,sK2,sK3)) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2758,plain,
% 3.72/0.98      ( k2_relat_1(sK3) != sK2
% 3.72/0.98      | r1_tarski(sK2,k1_relset_1(sK1,sK2,sK3)) != iProver_top ),
% 3.72/0.98      inference(demodulation,[status(thm)],[c_2270,c_1307]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_19,plain,
% 3.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.72/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.72/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1309,plain,
% 3.72/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.72/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2388,plain,
% 3.72/0.98      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 3.72/0.98      inference(superposition,[status(thm)],[c_1305,c_1309]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3125,plain,
% 3.72/0.98      ( k2_relat_1(sK3) != sK2
% 3.72/0.98      | r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
% 3.72/0.98      inference(light_normalisation,[status(thm)],[c_2758,c_2388]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_3,plain,
% 3.72/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.72/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2318,plain,
% 3.72/0.98      ( ~ r1_tarski(X0,k2_relat_1(sK3))
% 3.72/0.98      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 3.72/0.98      | k2_relat_1(sK3) = X0 ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2319,plain,
% 3.72/0.98      ( k2_relat_1(sK3) = X0
% 3.72/0.98      | r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
% 3.72/0.98      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_2318]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_2321,plain,
% 3.72/0.98      ( k2_relat_1(sK3) = sK2
% 3.72/0.98      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 3.72/0.98      | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_2319]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1464,plain,
% 3.72/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.72/0.98      | r1_tarski(k2_relat_1(sK3),sK2) ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_319]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1465,plain,
% 3.72/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.72/0.98      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_1464]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1441,plain,
% 3.72/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.72/0.98      | v1_relat_1(sK3) ),
% 3.72/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_1442,plain,
% 3.72/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.72/0.98      | v1_relat_1(sK3) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_1441]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(c_24,plain,
% 3.72/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.72/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.72/0.98  
% 3.72/0.98  cnf(contradiction,plain,
% 3.72/0.98      ( $false ),
% 3.72/0.98      inference(minisat,
% 3.72/0.98                [status(thm)],
% 3.72/0.98                [c_10534,c_9235,c_3125,c_2321,c_1465,c_1442,c_24]) ).
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.72/0.98  
% 3.72/0.98  ------                               Statistics
% 3.72/0.98  
% 3.72/0.98  ------ General
% 3.72/0.98  
% 3.72/0.98  abstr_ref_over_cycles:                  0
% 3.72/0.98  abstr_ref_under_cycles:                 0
% 3.72/0.98  gc_basic_clause_elim:                   0
% 3.72/0.98  forced_gc_time:                         0
% 3.72/0.98  parsing_time:                           0.01
% 3.72/0.98  unif_index_cands_time:                  0.
% 3.72/0.98  unif_index_add_time:                    0.
% 3.72/0.98  orderings_time:                         0.
% 3.72/0.98  out_proof_time:                         0.011
% 3.72/0.98  total_time:                             0.391
% 3.72/0.98  num_of_symbols:                         48
% 3.72/0.98  num_of_terms:                           11415
% 3.72/0.98  
% 3.72/0.98  ------ Preprocessing
% 3.72/0.98  
% 3.72/0.98  num_of_splits:                          0
% 3.72/0.98  num_of_split_atoms:                     0
% 3.72/0.98  num_of_reused_defs:                     0
% 3.72/0.98  num_eq_ax_congr_red:                    13
% 3.72/0.98  num_of_sem_filtered_clauses:            1
% 3.72/0.98  num_of_subtypes:                        0
% 3.72/0.98  monotx_restored_types:                  0
% 3.72/0.98  sat_num_of_epr_types:                   0
% 3.72/0.98  sat_num_of_non_cyclic_types:            0
% 3.72/0.98  sat_guarded_non_collapsed_types:        0
% 3.72/0.98  num_pure_diseq_elim:                    0
% 3.72/0.98  simp_replaced_by:                       0
% 3.72/0.98  res_preprocessed:                       107
% 3.72/0.98  prep_upred:                             0
% 3.72/0.98  prep_unflattend:                        24
% 3.72/0.98  smt_new_axioms:                         0
% 3.72/0.98  pred_elim_cands:                        4
% 3.72/0.98  pred_elim:                              2
% 3.72/0.98  pred_elim_cl:                           4
% 3.72/0.98  pred_elim_cycles:                       6
% 3.72/0.98  merged_defs:                            8
% 3.72/0.98  merged_defs_ncl:                        0
% 3.72/0.98  bin_hyper_res:                          8
% 3.72/0.98  prep_cycles:                            4
% 3.72/0.98  pred_elim_time:                         0.006
% 3.72/0.98  splitting_time:                         0.
% 3.72/0.98  sem_filter_time:                        0.
% 3.72/0.98  monotx_time:                            0.001
% 3.72/0.98  subtype_inf_time:                       0.
% 3.72/0.98  
% 3.72/0.98  ------ Problem properties
% 3.72/0.98  
% 3.72/0.98  clauses:                                19
% 3.72/0.98  conjectures:                            3
% 3.72/0.98  epr:                                    3
% 3.72/0.98  horn:                                   18
% 3.72/0.98  ground:                                 3
% 3.72/0.98  unary:                                  6
% 3.72/0.98  binary:                                 11
% 3.72/0.98  lits:                                   34
% 3.72/0.98  lits_eq:                                6
% 3.72/0.98  fd_pure:                                0
% 3.72/0.98  fd_pseudo:                              0
% 3.72/0.98  fd_cond:                                0
% 3.72/0.98  fd_pseudo_cond:                         1
% 3.72/0.98  ac_symbols:                             0
% 3.72/0.98  
% 3.72/0.98  ------ Propositional Solver
% 3.72/0.98  
% 3.72/0.98  prop_solver_calls:                      28
% 3.72/0.98  prop_fast_solver_calls:                 731
% 3.72/0.98  smt_solver_calls:                       0
% 3.72/0.98  smt_fast_solver_calls:                  0
% 3.72/0.98  prop_num_of_clauses:                    4314
% 3.72/0.98  prop_preprocess_simplified:             9006
% 3.72/0.98  prop_fo_subsumed:                       3
% 3.72/0.98  prop_solver_time:                       0.
% 3.72/0.98  smt_solver_time:                        0.
% 3.72/0.98  smt_fast_solver_time:                   0.
% 3.72/0.98  prop_fast_solver_time:                  0.
% 3.72/0.98  prop_unsat_core_time:                   0.
% 3.72/0.98  
% 3.72/0.98  ------ QBF
% 3.72/0.98  
% 3.72/0.98  qbf_q_res:                              0
% 3.72/0.98  qbf_num_tautologies:                    0
% 3.72/0.98  qbf_prep_cycles:                        0
% 3.72/0.98  
% 3.72/0.98  ------ BMC1
% 3.72/0.98  
% 3.72/0.98  bmc1_current_bound:                     -1
% 3.72/0.98  bmc1_last_solved_bound:                 -1
% 3.72/0.98  bmc1_unsat_core_size:                   -1
% 3.72/0.98  bmc1_unsat_core_parents_size:           -1
% 3.72/0.98  bmc1_merge_next_fun:                    0
% 3.72/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.72/0.98  
% 3.72/0.98  ------ Instantiation
% 3.72/0.98  
% 3.72/0.98  inst_num_of_clauses:                    1110
% 3.72/0.98  inst_num_in_passive:                    119
% 3.72/0.98  inst_num_in_active:                     494
% 3.72/0.98  inst_num_in_unprocessed:                497
% 3.72/0.98  inst_num_of_loops:                      640
% 3.72/0.98  inst_num_of_learning_restarts:          0
% 3.72/0.98  inst_num_moves_active_passive:          143
% 3.72/0.98  inst_lit_activity:                      0
% 3.72/0.98  inst_lit_activity_moves:                0
% 3.72/0.98  inst_num_tautologies:                   0
% 3.72/0.98  inst_num_prop_implied:                  0
% 3.72/0.98  inst_num_existing_simplified:           0
% 3.72/0.98  inst_num_eq_res_simplified:             0
% 3.72/0.98  inst_num_child_elim:                    0
% 3.72/0.98  inst_num_of_dismatching_blockings:      499
% 3.72/0.98  inst_num_of_non_proper_insts:           1115
% 3.72/0.98  inst_num_of_duplicates:                 0
% 3.72/0.98  inst_inst_num_from_inst_to_res:         0
% 3.72/0.98  inst_dismatching_checking_time:         0.
% 3.72/0.98  
% 3.72/0.98  ------ Resolution
% 3.72/0.98  
% 3.72/0.98  res_num_of_clauses:                     0
% 3.72/0.98  res_num_in_passive:                     0
% 3.72/0.98  res_num_in_active:                      0
% 3.72/0.98  res_num_of_loops:                       111
% 3.72/0.98  res_forward_subset_subsumed:            70
% 3.72/0.98  res_backward_subset_subsumed:           2
% 3.72/0.98  res_forward_subsumed:                   0
% 3.72/0.98  res_backward_subsumed:                  0
% 3.72/0.98  res_forward_subsumption_resolution:     0
% 3.72/0.98  res_backward_subsumption_resolution:    0
% 3.72/0.98  res_clause_to_clause_subsumption:       1316
% 3.72/0.98  res_orphan_elimination:                 0
% 3.72/0.98  res_tautology_del:                      73
% 3.72/0.98  res_num_eq_res_simplified:              0
% 3.72/0.98  res_num_sel_changes:                    0
% 3.72/0.98  res_moves_from_active_to_pass:          0
% 3.72/0.98  
% 3.72/0.98  ------ Superposition
% 3.72/0.98  
% 3.72/0.98  sup_time_total:                         0.
% 3.72/0.98  sup_time_generating:                    0.
% 3.72/0.98  sup_time_sim_full:                      0.
% 3.72/0.98  sup_time_sim_immed:                     0.
% 3.72/0.98  
% 3.72/0.98  sup_num_of_clauses:                     332
% 3.72/0.98  sup_num_in_active:                      126
% 3.72/0.98  sup_num_in_passive:                     206
% 3.72/0.98  sup_num_of_loops:                       126
% 3.72/0.98  sup_fw_superposition:                   188
% 3.72/0.98  sup_bw_superposition:                   176
% 3.72/0.98  sup_immediate_simplified:               39
% 3.72/0.98  sup_given_eliminated:                   0
% 3.72/0.98  comparisons_done:                       0
% 3.72/0.98  comparisons_avoided:                    0
% 3.72/0.98  
% 3.72/0.98  ------ Simplifications
% 3.72/0.98  
% 3.72/0.98  
% 3.72/0.98  sim_fw_subset_subsumed:                 20
% 3.72/0.98  sim_bw_subset_subsumed:                 0
% 3.72/0.98  sim_fw_subsumed:                        5
% 3.72/0.98  sim_bw_subsumed:                        1
% 3.72/0.98  sim_fw_subsumption_res:                 0
% 3.72/0.98  sim_bw_subsumption_res:                 0
% 3.72/0.98  sim_tautology_del:                      3
% 3.72/0.98  sim_eq_tautology_del:                   3
% 3.72/0.98  sim_eq_res_simp:                        0
% 3.72/0.98  sim_fw_demodulated:                     4
% 3.72/0.98  sim_bw_demodulated:                     1
% 3.72/0.98  sim_light_normalised:                   11
% 3.72/0.98  sim_joinable_taut:                      0
% 3.72/0.98  sim_joinable_simp:                      0
% 3.72/0.98  sim_ac_normalised:                      0
% 3.72/0.98  sim_smt_subsumption:                    0
% 3.72/0.98  
%------------------------------------------------------------------------------
