%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:13 EST 2020

% Result     : Theorem 11.12s
% Output     : CNFRefutation 11.12s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 194 expanded)
%              Number of clauses        :   67 (  81 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  335 ( 596 expanded)
%              Number of equality atoms :   61 ( 129 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
          & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
            & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
        | k1_relset_1(X1,X0,X2) != X1 )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
        | k1_relset_1(X1,X0,X2) != X1 )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f25])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
          | k1_relset_1(X1,X0,X2) != X1 )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
        | k1_relset_1(sK1,sK0,sK2) != sK1 )
      & r1_tarski(k6_relat_1(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
      | k1_relset_1(sK1,sK0,sK2) != sK1 )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f32])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,
    ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | k1_relset_1(sK1,sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1349,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4774,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X3,k2_relset_1(X1,X2,X0))
    | ~ r1_tarski(X4,k2_relat_1(X0))
    | X3 != X4 ),
    inference(resolution,[status(thm)],[c_1349,c_20])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27771,plain,
    ( r1_tarski(X0,k2_relset_1(sK1,sK0,sK2))
    | ~ r1_tarski(X1,k2_relat_1(sK2))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_4774,c_23])).

cnf(c_1348,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1347,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3478,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1348,c_1347])).

cnf(c_11,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4276,plain,
    ( X0 = k2_relat_1(k6_relat_1(X0)) ),
    inference(resolution,[status(thm)],[c_3478,c_11])).

cnf(c_28499,plain,
    ( r1_tarski(X0,k2_relset_1(sK1,sK0,sK2))
    | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(sK2)) ),
    inference(resolution,[status(thm)],[c_27771,c_4276])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_29754,plain,
    ( ~ v5_relat_1(k6_relat_1(X0),k2_relat_1(sK2))
    | r1_tarski(X0,k2_relset_1(sK1,sK0,sK2))
    | ~ v1_relat_1(k6_relat_1(X0)) ),
    inference(resolution,[status(thm)],[c_28499,c_10])).

cnf(c_29756,plain,
    ( ~ v5_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))
    | r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_29754])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2191,plain,
    ( v4_relat_1(sK2,X0)
    | ~ r1_tarski(k1_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_16473,plain,
    ( v4_relat_1(sK2,k1_relat_1(sK2))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2191])).

cnf(c_6,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2185,plain,
    ( v5_relat_1(X0,X1)
    | ~ v5_relat_1(sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4080,plain,
    ( v5_relat_1(k6_relat_1(sK1),X0)
    | ~ v5_relat_1(sK2,X0)
    | ~ m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2185])).

cnf(c_7641,plain,
    ( v5_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))
    | ~ v5_relat_1(sK2,k2_relat_1(sK2))
    | ~ m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4080])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2186,plain,
    ( v4_relat_1(X0,X1)
    | ~ v4_relat_1(sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4079,plain,
    ( v4_relat_1(k6_relat_1(sK1),X0)
    | ~ v4_relat_1(sK2,X0)
    | ~ m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2186])).

cnf(c_7612,plain,
    ( v4_relat_1(k6_relat_1(sK1),k1_relat_1(sK2))
    | ~ v4_relat_1(sK2,k1_relat_1(sK2))
    | ~ m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4079])).

cnf(c_12,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4278,plain,
    ( X0 = k1_relat_1(k6_relat_1(X0)) ),
    inference(resolution,[status(thm)],[c_3478,c_12])).

cnf(c_4279,plain,
    ( sK1 = k1_relat_1(k6_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_4278])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | k1_relset_1(sK1,sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3290,plain,
    ( ~ r1_tarski(k1_relset_1(sK1,sK0,sK2),sK1)
    | ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | ~ r1_tarski(sK1,k1_relset_1(sK1,sK0,sK2)) ),
    inference(resolution,[status(thm)],[c_0,c_21])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_74,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_78,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2093,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2127,plain,
    ( v4_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2172,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2190,plain,
    ( ~ v4_relat_1(sK2,X0)
    | r1_tarski(k1_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2197,plain,
    ( ~ v4_relat_1(sK2,sK1)
    | r1_tarski(k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_2461,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relset_1(sK1,sK0,sK2),X2)
    | X2 != X1
    | k1_relset_1(sK1,sK0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_1349])).

cnf(c_3378,plain,
    ( r1_tarski(k1_relset_1(sK1,sK0,sK2),X0)
    | ~ r1_tarski(k1_relat_1(sK2),X1)
    | X0 != X1
    | k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2461])).

cnf(c_3380,plain,
    ( r1_tarski(k1_relset_1(sK1,sK0,sK2),sK1)
    | ~ r1_tarski(k1_relat_1(sK2),sK1)
    | k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3378])).

cnf(c_3745,plain,
    ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | ~ r1_tarski(sK1,k1_relset_1(sK1,sK0,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3290,c_23,c_74,c_78,c_2093,c_2127,c_2172,c_2197,c_3380])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2514,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2))
    | ~ r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3141,plain,
    ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2))
    | ~ r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_2514])).

cnf(c_2099,plain,
    ( ~ v4_relat_1(k6_relat_1(X0),X1)
    | r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
    | ~ v1_relat_1(k6_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2883,plain,
    ( ~ v4_relat_1(k6_relat_1(X0),k1_relat_1(sK2))
    | r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_2099])).

cnf(c_2889,plain,
    ( ~ v4_relat_1(k6_relat_1(sK1),k1_relat_1(sK2))
    | r1_tarski(k1_relat_1(k6_relat_1(sK1)),k1_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2883])).

cnf(c_2256,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_relset_1(sK1,sK0,sK2))
    | k1_relset_1(sK1,sK0,sK2) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1349])).

cnf(c_2526,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | r1_tarski(sK1,k1_relset_1(sK1,sK0,sK2))
    | k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_2256])).

cnf(c_2882,plain,
    ( ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(sK2))
    | r1_tarski(sK1,k1_relset_1(sK1,sK0,sK2))
    | k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
    | sK1 != k1_relat_1(k6_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_2526])).

cnf(c_2885,plain,
    ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK1)),k1_relat_1(sK2))
    | r1_tarski(sK1,k1_relset_1(sK1,sK0,sK2))
    | k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
    | sK1 != k1_relat_1(k6_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_2882])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2862,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2395,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2189,plain,
    ( v5_relat_1(sK2,X0)
    | ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2394,plain,
    ( v5_relat_1(sK2,k2_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_15,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_43,plain,
    ( v1_relat_1(k6_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29756,c_16473,c_7641,c_7612,c_4279,c_3745,c_3141,c_2889,c_2885,c_2862,c_2395,c_2394,c_2172,c_2093,c_43,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.12/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.12/2.00  
% 11.12/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.12/2.00  
% 11.12/2.00  ------  iProver source info
% 11.12/2.00  
% 11.12/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.12/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.12/2.00  git: non_committed_changes: false
% 11.12/2.00  git: last_make_outside_of_git: false
% 11.12/2.00  
% 11.12/2.00  ------ 
% 11.12/2.00  ------ Parsing...
% 11.12/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.12/2.00  
% 11.12/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.12/2.00  
% 11.12/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.12/2.00  
% 11.12/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.12/2.00  ------ Proving...
% 11.12/2.00  ------ Problem Properties 
% 11.12/2.00  
% 11.12/2.00  
% 11.12/2.00  clauses                                 23
% 11.12/2.00  conjectures                             3
% 11.12/2.00  EPR                                     2
% 11.12/2.00  Horn                                    23
% 11.12/2.00  unary                                   8
% 11.12/2.00  binary                                  8
% 11.12/2.00  lits                                    47
% 11.12/2.00  lits eq                                 6
% 11.12/2.00  fd_pure                                 0
% 11.12/2.00  fd_pseudo                               0
% 11.12/2.00  fd_cond                                 0
% 11.12/2.00  fd_pseudo_cond                          1
% 11.12/2.00  AC symbols                              0
% 11.12/2.00  
% 11.12/2.00  ------ Input Options Time Limit: Unbounded
% 11.12/2.00  
% 11.12/2.00  
% 11.12/2.00  ------ 
% 11.12/2.00  Current options:
% 11.12/2.00  ------ 
% 11.12/2.00  
% 11.12/2.00  
% 11.12/2.00  
% 11.12/2.00  
% 11.12/2.00  ------ Proving...
% 11.12/2.00  
% 11.12/2.00  
% 11.12/2.00  % SZS status Theorem for theBenchmark.p
% 11.12/2.00  
% 11.12/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.12/2.00  
% 11.12/2.00  fof(f12,axiom,(
% 11.12/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.12/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.12/2.00  
% 11.12/2.00  fof(f24,plain,(
% 11.12/2.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.12/2.00    inference(ennf_transformation,[],[f12])).
% 11.12/2.00  
% 11.12/2.00  fof(f54,plain,(
% 11.12/2.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.12/2.00    inference(cnf_transformation,[],[f24])).
% 11.12/2.00  
% 11.12/2.00  fof(f13,conjecture,(
% 11.12/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 11.12/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.12/2.00  
% 11.12/2.00  fof(f14,negated_conjecture,(
% 11.12/2.00    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 11.12/2.00    inference(negated_conjecture,[],[f13])).
% 11.12/2.00  
% 11.12/2.00  fof(f25,plain,(
% 11.12/2.00    ? [X0,X1,X2] : (((~r1_tarski(X1,k2_relset_1(X1,X0,X2)) | k1_relset_1(X1,X0,X2) != X1) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 11.12/2.00    inference(ennf_transformation,[],[f14])).
% 11.12/2.00  
% 11.12/2.00  fof(f26,plain,(
% 11.12/2.00    ? [X0,X1,X2] : ((~r1_tarski(X1,k2_relset_1(X1,X0,X2)) | k1_relset_1(X1,X0,X2) != X1) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 11.12/2.00    inference(flattening,[],[f25])).
% 11.12/2.00  
% 11.12/2.00  fof(f32,plain,(
% 11.12/2.00    ? [X0,X1,X2] : ((~r1_tarski(X1,k2_relset_1(X1,X0,X2)) | k1_relset_1(X1,X0,X2) != X1) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((~r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) | k1_relset_1(sK1,sK0,sK2) != sK1) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 11.12/2.00    introduced(choice_axiom,[])).
% 11.12/2.00  
% 11.12/2.00  fof(f33,plain,(
% 11.12/2.00    (~r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) | k1_relset_1(sK1,sK0,sK2) != sK1) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.12/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f32])).
% 11.12/2.00  
% 11.12/2.00  fof(f55,plain,(
% 11.12/2.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.12/2.00    inference(cnf_transformation,[],[f33])).
% 11.12/2.00  
% 11.12/2.00  fof(f7,axiom,(
% 11.12/2.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.12/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.12/2.00  
% 11.12/2.00  fof(f46,plain,(
% 11.12/2.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 11.12/2.00    inference(cnf_transformation,[],[f7])).
% 11.12/2.00  
% 11.12/2.00  fof(f6,axiom,(
% 11.12/2.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.12/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.12/2.00  
% 11.12/2.00  fof(f20,plain,(
% 11.12/2.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.12/2.00    inference(ennf_transformation,[],[f6])).
% 11.12/2.00  
% 11.12/2.00  fof(f31,plain,(
% 11.12/2.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.12/2.00    inference(nnf_transformation,[],[f20])).
% 11.12/2.00  
% 11.12/2.00  fof(f43,plain,(
% 11.12/2.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.12/2.00    inference(cnf_transformation,[],[f31])).
% 11.12/2.00  
% 11.12/2.00  fof(f5,axiom,(
% 11.12/2.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.12/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.12/2.00  
% 11.12/2.00  fof(f19,plain,(
% 11.12/2.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.12/2.00    inference(ennf_transformation,[],[f5])).
% 11.12/2.00  
% 11.12/2.00  fof(f30,plain,(
% 11.12/2.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.12/2.00    inference(nnf_transformation,[],[f19])).
% 11.12/2.00  
% 11.12/2.00  fof(f42,plain,(
% 11.12/2.00    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.12/2.00    inference(cnf_transformation,[],[f30])).
% 11.12/2.00  
% 11.12/2.00  fof(f4,axiom,(
% 11.12/2.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v5_relat_1(X2,X0)))),
% 11.12/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.12/2.00  
% 11.12/2.00  fof(f17,plain,(
% 11.12/2.00    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.12/2.00    inference(ennf_transformation,[],[f4])).
% 11.12/2.00  
% 11.12/2.00  fof(f18,plain,(
% 11.12/2.00    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.12/2.00    inference(flattening,[],[f17])).
% 11.12/2.00  
% 11.12/2.00  fof(f40,plain,(
% 11.12/2.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.12/2.00    inference(cnf_transformation,[],[f18])).
% 11.12/2.00  
% 11.12/2.00  fof(f3,axiom,(
% 11.12/2.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v4_relat_1(X2,X0)))),
% 11.12/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.12/2.00  
% 11.12/2.00  fof(f15,plain,(
% 11.12/2.00    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.12/2.00    inference(ennf_transformation,[],[f3])).
% 11.12/2.00  
% 11.12/2.00  fof(f16,plain,(
% 11.12/2.00    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.12/2.00    inference(flattening,[],[f15])).
% 11.12/2.00  
% 11.12/2.00  fof(f39,plain,(
% 11.12/2.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.12/2.00    inference(cnf_transformation,[],[f16])).
% 11.12/2.00  
% 11.12/2.00  fof(f45,plain,(
% 11.12/2.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 11.12/2.00    inference(cnf_transformation,[],[f7])).
% 11.12/2.00  
% 11.12/2.00  fof(f1,axiom,(
% 11.12/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.12/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.12/2.00  
% 11.12/2.00  fof(f27,plain,(
% 11.12/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.12/2.00    inference(nnf_transformation,[],[f1])).
% 11.12/2.00  
% 11.12/2.00  fof(f28,plain,(
% 11.12/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.12/2.00    inference(flattening,[],[f27])).
% 11.12/2.00  
% 11.12/2.00  fof(f36,plain,(
% 11.12/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.12/2.00    inference(cnf_transformation,[],[f28])).
% 11.12/2.00  
% 11.12/2.00  fof(f57,plain,(
% 11.12/2.00    ~r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) | k1_relset_1(sK1,sK0,sK2) != sK1),
% 11.12/2.00    inference(cnf_transformation,[],[f33])).
% 11.12/2.00  
% 11.12/2.00  fof(f34,plain,(
% 11.12/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.12/2.00    inference(cnf_transformation,[],[f28])).
% 11.12/2.00  
% 11.12/2.00  fof(f59,plain,(
% 11.12/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.12/2.00    inference(equality_resolution,[],[f34])).
% 11.12/2.00  
% 11.12/2.00  fof(f9,axiom,(
% 11.12/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.12/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.12/2.00  
% 11.12/2.00  fof(f21,plain,(
% 11.12/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.12/2.00    inference(ennf_transformation,[],[f9])).
% 11.12/2.00  
% 11.12/2.00  fof(f50,plain,(
% 11.12/2.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.12/2.00    inference(cnf_transformation,[],[f21])).
% 11.12/2.00  
% 11.12/2.00  fof(f10,axiom,(
% 11.12/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.12/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.12/2.00  
% 11.12/2.00  fof(f22,plain,(
% 11.12/2.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.12/2.00    inference(ennf_transformation,[],[f10])).
% 11.12/2.00  
% 11.12/2.00  fof(f51,plain,(
% 11.12/2.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.12/2.00    inference(cnf_transformation,[],[f22])).
% 11.12/2.00  
% 11.12/2.00  fof(f11,axiom,(
% 11.12/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.12/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.12/2.00  
% 11.12/2.00  fof(f23,plain,(
% 11.12/2.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.12/2.00    inference(ennf_transformation,[],[f11])).
% 11.12/2.00  
% 11.12/2.00  fof(f53,plain,(
% 11.12/2.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.12/2.00    inference(cnf_transformation,[],[f23])).
% 11.12/2.00  
% 11.12/2.00  fof(f41,plain,(
% 11.12/2.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.12/2.00    inference(cnf_transformation,[],[f30])).
% 11.12/2.00  
% 11.12/2.00  fof(f2,axiom,(
% 11.12/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.12/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.12/2.00  
% 11.12/2.00  fof(f29,plain,(
% 11.12/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.12/2.00    inference(nnf_transformation,[],[f2])).
% 11.12/2.00  
% 11.12/2.00  fof(f38,plain,(
% 11.12/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.12/2.00    inference(cnf_transformation,[],[f29])).
% 11.12/2.00  
% 11.12/2.00  fof(f35,plain,(
% 11.12/2.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.12/2.00    inference(cnf_transformation,[],[f28])).
% 11.12/2.00  
% 11.12/2.00  fof(f58,plain,(
% 11.12/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.12/2.00    inference(equality_resolution,[],[f35])).
% 11.12/2.00  
% 11.12/2.00  fof(f44,plain,(
% 11.12/2.00    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.12/2.00    inference(cnf_transformation,[],[f31])).
% 11.12/2.00  
% 11.12/2.00  fof(f8,axiom,(
% 11.12/2.00    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 11.12/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.12/2.00  
% 11.12/2.00  fof(f47,plain,(
% 11.12/2.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 11.12/2.00    inference(cnf_transformation,[],[f8])).
% 11.12/2.00  
% 11.12/2.00  fof(f56,plain,(
% 11.12/2.00    r1_tarski(k6_relat_1(sK1),sK2)),
% 11.12/2.00    inference(cnf_transformation,[],[f33])).
% 11.12/2.00  
% 11.12/2.00  cnf(c_1349,plain,
% 11.12/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.12/2.00      theory(equality) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_20,plain,
% 11.12/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.12/2.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.12/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_4774,plain,
% 11.12/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.12/2.00      | r1_tarski(X3,k2_relset_1(X1,X2,X0))
% 11.12/2.00      | ~ r1_tarski(X4,k2_relat_1(X0))
% 11.12/2.00      | X3 != X4 ),
% 11.12/2.00      inference(resolution,[status(thm)],[c_1349,c_20]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_23,negated_conjecture,
% 11.12/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.12/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_27771,plain,
% 11.12/2.00      ( r1_tarski(X0,k2_relset_1(sK1,sK0,sK2))
% 11.12/2.00      | ~ r1_tarski(X1,k2_relat_1(sK2))
% 11.12/2.00      | X0 != X1 ),
% 11.12/2.00      inference(resolution,[status(thm)],[c_4774,c_23]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_1348,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_1347,plain,( X0 = X0 ),theory(equality) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_3478,plain,
% 11.12/2.00      ( X0 != X1 | X1 = X0 ),
% 11.12/2.00      inference(resolution,[status(thm)],[c_1348,c_1347]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_11,plain,
% 11.12/2.00      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 11.12/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_4276,plain,
% 11.12/2.00      ( X0 = k2_relat_1(k6_relat_1(X0)) ),
% 11.12/2.00      inference(resolution,[status(thm)],[c_3478,c_11]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_28499,plain,
% 11.12/2.00      ( r1_tarski(X0,k2_relset_1(sK1,sK0,sK2))
% 11.12/2.00      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),k2_relat_1(sK2)) ),
% 11.12/2.00      inference(resolution,[status(thm)],[c_27771,c_4276]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_10,plain,
% 11.12/2.00      ( ~ v5_relat_1(X0,X1)
% 11.12/2.00      | r1_tarski(k2_relat_1(X0),X1)
% 11.12/2.00      | ~ v1_relat_1(X0) ),
% 11.12/2.00      inference(cnf_transformation,[],[f43]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_29754,plain,
% 11.12/2.00      ( ~ v5_relat_1(k6_relat_1(X0),k2_relat_1(sK2))
% 11.12/2.00      | r1_tarski(X0,k2_relset_1(sK1,sK0,sK2))
% 11.12/2.00      | ~ v1_relat_1(k6_relat_1(X0)) ),
% 11.12/2.00      inference(resolution,[status(thm)],[c_28499,c_10]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_29756,plain,
% 11.12/2.00      ( ~ v5_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))
% 11.12/2.00      | r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
% 11.12/2.00      | ~ v1_relat_1(k6_relat_1(sK1)) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_29754]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_7,plain,
% 11.12/2.00      ( v4_relat_1(X0,X1)
% 11.12/2.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 11.12/2.00      | ~ v1_relat_1(X0) ),
% 11.12/2.00      inference(cnf_transformation,[],[f42]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2191,plain,
% 11.12/2.00      ( v4_relat_1(sK2,X0)
% 11.12/2.00      | ~ r1_tarski(k1_relat_1(sK2),X0)
% 11.12/2.00      | ~ v1_relat_1(sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_7]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_16473,plain,
% 11.12/2.00      ( v4_relat_1(sK2,k1_relat_1(sK2))
% 11.12/2.00      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
% 11.12/2.00      | ~ v1_relat_1(sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_2191]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_6,plain,
% 11.12/2.00      ( ~ v5_relat_1(X0,X1)
% 11.12/2.00      | v5_relat_1(X2,X1)
% 11.12/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 11.12/2.00      | ~ v1_relat_1(X0) ),
% 11.12/2.00      inference(cnf_transformation,[],[f40]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2185,plain,
% 11.12/2.00      ( v5_relat_1(X0,X1)
% 11.12/2.00      | ~ v5_relat_1(sK2,X1)
% 11.12/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
% 11.12/2.00      | ~ v1_relat_1(sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_6]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_4080,plain,
% 11.12/2.00      ( v5_relat_1(k6_relat_1(sK1),X0)
% 11.12/2.00      | ~ v5_relat_1(sK2,X0)
% 11.12/2.00      | ~ m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2))
% 11.12/2.00      | ~ v1_relat_1(sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_2185]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_7641,plain,
% 11.12/2.00      ( v5_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))
% 11.12/2.00      | ~ v5_relat_1(sK2,k2_relat_1(sK2))
% 11.12/2.00      | ~ m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2))
% 11.12/2.00      | ~ v1_relat_1(sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_4080]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_5,plain,
% 11.12/2.00      ( ~ v4_relat_1(X0,X1)
% 11.12/2.00      | v4_relat_1(X2,X1)
% 11.12/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 11.12/2.00      | ~ v1_relat_1(X0) ),
% 11.12/2.00      inference(cnf_transformation,[],[f39]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2186,plain,
% 11.12/2.00      ( v4_relat_1(X0,X1)
% 11.12/2.00      | ~ v4_relat_1(sK2,X1)
% 11.12/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
% 11.12/2.00      | ~ v1_relat_1(sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_5]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_4079,plain,
% 11.12/2.00      ( v4_relat_1(k6_relat_1(sK1),X0)
% 11.12/2.00      | ~ v4_relat_1(sK2,X0)
% 11.12/2.00      | ~ m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2))
% 11.12/2.00      | ~ v1_relat_1(sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_2186]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_7612,plain,
% 11.12/2.00      ( v4_relat_1(k6_relat_1(sK1),k1_relat_1(sK2))
% 11.12/2.00      | ~ v4_relat_1(sK2,k1_relat_1(sK2))
% 11.12/2.00      | ~ m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2))
% 11.12/2.00      | ~ v1_relat_1(sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_4079]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_12,plain,
% 11.12/2.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 11.12/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_4278,plain,
% 11.12/2.00      ( X0 = k1_relat_1(k6_relat_1(X0)) ),
% 11.12/2.00      inference(resolution,[status(thm)],[c_3478,c_12]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_4279,plain,
% 11.12/2.00      ( sK1 = k1_relat_1(k6_relat_1(sK1)) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_4278]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_0,plain,
% 11.12/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.12/2.00      inference(cnf_transformation,[],[f36]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_21,negated_conjecture,
% 11.12/2.00      ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
% 11.12/2.00      | k1_relset_1(sK1,sK0,sK2) != sK1 ),
% 11.12/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_3290,plain,
% 11.12/2.00      ( ~ r1_tarski(k1_relset_1(sK1,sK0,sK2),sK1)
% 11.12/2.00      | ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
% 11.12/2.00      | ~ r1_tarski(sK1,k1_relset_1(sK1,sK0,sK2)) ),
% 11.12/2.00      inference(resolution,[status(thm)],[c_0,c_21]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2,plain,
% 11.12/2.00      ( r1_tarski(X0,X0) ),
% 11.12/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_74,plain,
% 11.12/2.00      ( r1_tarski(sK1,sK1) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_2]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_78,plain,
% 11.12/2.00      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_0]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_16,plain,
% 11.12/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.12/2.00      | v1_relat_1(X0) ),
% 11.12/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2093,plain,
% 11.12/2.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.12/2.00      | v1_relat_1(sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_16]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_18,plain,
% 11.12/2.00      ( v4_relat_1(X0,X1)
% 11.12/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.12/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2127,plain,
% 11.12/2.00      ( v4_relat_1(sK2,sK1)
% 11.12/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_18]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_19,plain,
% 11.12/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.12/2.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.12/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2172,plain,
% 11.12/2.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.12/2.00      | k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_19]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_8,plain,
% 11.12/2.00      ( ~ v4_relat_1(X0,X1)
% 11.12/2.00      | r1_tarski(k1_relat_1(X0),X1)
% 11.12/2.00      | ~ v1_relat_1(X0) ),
% 11.12/2.00      inference(cnf_transformation,[],[f41]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2190,plain,
% 11.12/2.00      ( ~ v4_relat_1(sK2,X0)
% 11.12/2.00      | r1_tarski(k1_relat_1(sK2),X0)
% 11.12/2.00      | ~ v1_relat_1(sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2197,plain,
% 11.12/2.00      ( ~ v4_relat_1(sK2,sK1)
% 11.12/2.00      | r1_tarski(k1_relat_1(sK2),sK1)
% 11.12/2.00      | ~ v1_relat_1(sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_2190]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2461,plain,
% 11.12/2.00      ( ~ r1_tarski(X0,X1)
% 11.12/2.00      | r1_tarski(k1_relset_1(sK1,sK0,sK2),X2)
% 11.12/2.00      | X2 != X1
% 11.12/2.00      | k1_relset_1(sK1,sK0,sK2) != X0 ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_1349]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_3378,plain,
% 11.12/2.00      ( r1_tarski(k1_relset_1(sK1,sK0,sK2),X0)
% 11.12/2.00      | ~ r1_tarski(k1_relat_1(sK2),X1)
% 11.12/2.00      | X0 != X1
% 11.12/2.00      | k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_2461]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_3380,plain,
% 11.12/2.00      ( r1_tarski(k1_relset_1(sK1,sK0,sK2),sK1)
% 11.12/2.00      | ~ r1_tarski(k1_relat_1(sK2),sK1)
% 11.12/2.00      | k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
% 11.12/2.00      | sK1 != sK1 ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_3378]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_3745,plain,
% 11.12/2.00      ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
% 11.12/2.00      | ~ r1_tarski(sK1,k1_relset_1(sK1,sK0,sK2)) ),
% 11.12/2.00      inference(global_propositional_subsumption,
% 11.12/2.00                [status(thm)],
% 11.12/2.00                [c_3290,c_23,c_74,c_78,c_2093,c_2127,c_2172,c_2197,
% 11.12/2.00                 c_3380]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_3,plain,
% 11.12/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.12/2.00      inference(cnf_transformation,[],[f38]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2514,plain,
% 11.12/2.00      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) | ~ r1_tarski(X0,sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_3141,plain,
% 11.12/2.00      ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(sK2))
% 11.12/2.00      | ~ r1_tarski(k6_relat_1(sK1),sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_2514]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2099,plain,
% 11.12/2.00      ( ~ v4_relat_1(k6_relat_1(X0),X1)
% 11.12/2.00      | r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
% 11.12/2.00      | ~ v1_relat_1(k6_relat_1(X0)) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2883,plain,
% 11.12/2.00      ( ~ v4_relat_1(k6_relat_1(X0),k1_relat_1(sK2))
% 11.12/2.00      | r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(sK2))
% 11.12/2.00      | ~ v1_relat_1(k6_relat_1(X0)) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_2099]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2889,plain,
% 11.12/2.00      ( ~ v4_relat_1(k6_relat_1(sK1),k1_relat_1(sK2))
% 11.12/2.00      | r1_tarski(k1_relat_1(k6_relat_1(sK1)),k1_relat_1(sK2))
% 11.12/2.00      | ~ v1_relat_1(k6_relat_1(sK1)) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_2883]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2256,plain,
% 11.12/2.00      ( ~ r1_tarski(X0,X1)
% 11.12/2.00      | r1_tarski(sK1,k1_relset_1(sK1,sK0,sK2))
% 11.12/2.00      | k1_relset_1(sK1,sK0,sK2) != X1
% 11.12/2.00      | sK1 != X0 ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_1349]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2526,plain,
% 11.12/2.00      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 11.12/2.00      | r1_tarski(sK1,k1_relset_1(sK1,sK0,sK2))
% 11.12/2.00      | k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
% 11.12/2.00      | sK1 != X0 ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_2256]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2882,plain,
% 11.12/2.00      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(sK2))
% 11.12/2.00      | r1_tarski(sK1,k1_relset_1(sK1,sK0,sK2))
% 11.12/2.00      | k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
% 11.12/2.00      | sK1 != k1_relat_1(k6_relat_1(X0)) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_2526]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2885,plain,
% 11.12/2.00      ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK1)),k1_relat_1(sK2))
% 11.12/2.00      | r1_tarski(sK1,k1_relset_1(sK1,sK0,sK2))
% 11.12/2.00      | k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
% 11.12/2.00      | sK1 != k1_relat_1(k6_relat_1(sK1)) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_2882]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_1,plain,
% 11.12/2.00      ( r1_tarski(X0,X0) ),
% 11.12/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2862,plain,
% 11.12/2.00      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2395,plain,
% 11.12/2.00      ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_9,plain,
% 11.12/2.00      ( v5_relat_1(X0,X1)
% 11.12/2.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 11.12/2.00      | ~ v1_relat_1(X0) ),
% 11.12/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2189,plain,
% 11.12/2.00      ( v5_relat_1(sK2,X0)
% 11.12/2.00      | ~ r1_tarski(k2_relat_1(sK2),X0)
% 11.12/2.00      | ~ v1_relat_1(sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_9]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_2394,plain,
% 11.12/2.00      ( v5_relat_1(sK2,k2_relat_1(sK2))
% 11.12/2.00      | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
% 11.12/2.00      | ~ v1_relat_1(sK2) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_2189]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_15,plain,
% 11.12/2.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 11.12/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_43,plain,
% 11.12/2.00      ( v1_relat_1(k6_relat_1(sK1)) ),
% 11.12/2.00      inference(instantiation,[status(thm)],[c_15]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(c_22,negated_conjecture,
% 11.12/2.00      ( r1_tarski(k6_relat_1(sK1),sK2) ),
% 11.12/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.12/2.00  
% 11.12/2.00  cnf(contradiction,plain,
% 11.12/2.00      ( $false ),
% 11.12/2.00      inference(minisat,
% 11.12/2.00                [status(thm)],
% 11.12/2.00                [c_29756,c_16473,c_7641,c_7612,c_4279,c_3745,c_3141,
% 11.12/2.00                 c_2889,c_2885,c_2862,c_2395,c_2394,c_2172,c_2093,c_43,
% 11.12/2.00                 c_22,c_23]) ).
% 11.12/2.00  
% 11.12/2.00  
% 11.12/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.12/2.00  
% 11.12/2.00  ------                               Statistics
% 11.12/2.00  
% 11.12/2.00  ------ Selected
% 11.12/2.00  
% 11.12/2.00  total_time:                             1.09
% 11.12/2.00  
%------------------------------------------------------------------------------
