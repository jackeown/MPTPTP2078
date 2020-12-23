%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:29 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 227 expanded)
%              Number of clauses        :   71 ( 108 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  300 ( 488 expanded)
%              Number of equality atoms :   85 ( 107 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f37])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_10,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_676,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_47,X1_47)),X1_47)
    | ~ v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1000,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_47,X1_47)),X1_47) = iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_670,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | ~ r1_tarski(k1_relat_1(X0_47),X1_47)
    | ~ r1_tarski(k2_relat_1(X0_47),X2_47)
    | ~ v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1006,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) = iProver_top
    | r1_tarski(k1_relat_1(X0_47),X1_47) != iProver_top
    | r1_tarski(k2_relat_1(X0_47),X2_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_668,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1008,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_671,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k5_relset_1(X1_47,X2_47,X0_47,X3_47) = k7_relat_1(X0_47,X3_47) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1005,plain,
    ( k5_relset_1(X0_47,X1_47,X2_47,X3_47) = k7_relat_1(X2_47,X3_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_2831,plain,
    ( k5_relset_1(sK1,sK3,sK4,X0_47) = k7_relat_1(sK4,X0_47) ),
    inference(superposition,[status(thm)],[c_1008,c_1005])).

cnf(c_17,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_669,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1007,plain,
    ( m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_3488,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2831,c_1007])).

cnf(c_3492,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK4,sK2)),sK2) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1006,c_3488])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_674,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1002,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
    | v1_relat_1(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_1350,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1008,c_1002])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_675,plain,
    ( ~ v1_relat_1(X0_47)
    | k5_relat_1(k6_relat_1(X1_47),X0_47) = k7_relat_1(X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1001,plain,
    ( k5_relat_1(k6_relat_1(X0_47),X1_47) = k7_relat_1(X1_47,X0_47)
    | v1_relat_1(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_1776,plain,
    ( k5_relat_1(k6_relat_1(X0_47),sK4) = k7_relat_1(sK4,X0_47) ),
    inference(superposition,[status(thm)],[c_1350,c_1001])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_679,plain,
    ( ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(X1_47)
    | v1_relat_1(k5_relat_1(X1_47,X0_47)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_997,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(X1_47) != iProver_top
    | v1_relat_1(k5_relat_1(X1_47,X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(c_2006,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0_47)) = iProver_top
    | v1_relat_1(k6_relat_1(X0_47)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_997])).

cnf(c_19,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_678,plain,
    ( v1_relat_1(k6_relat_1(X0_47)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_711,plain,
    ( v1_relat_1(k6_relat_1(X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_1122,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_1123,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1122])).

cnf(c_2566,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0_47)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2006,c_19,c_711,c_1123])).

cnf(c_3883,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK4,sK2)),sK2) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3492,c_2566])).

cnf(c_3885,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1000,c_3883])).

cnf(c_5129,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3885,c_19,c_1123])).

cnf(c_9,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_677,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0_47,X1_47)),k2_relat_1(X1_47))
    | ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(X1_47) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_999,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0_47,X1_47)),k2_relat_1(X1_47)) = iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_3242,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0_47)),k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(k6_relat_1(X0_47)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_999])).

cnf(c_3888,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0_47)),k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3242,c_19,c_711,c_1123])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_672,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k2_relset_1(X1_47,X2_47,X0_47) = k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1004,plain,
    ( k2_relset_1(X0_47,X1_47,X2_47) = k2_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_672])).

cnf(c_1355,plain,
    ( k2_relset_1(sK1,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1008,c_1004])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | m1_subset_1(k2_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X2_47)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1003,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X2_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_2003,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1355,c_1003])).

cnf(c_2172,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2003,c_19])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_263,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_6])).

cnf(c_264,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_410,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_411,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_410])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_264,c_411])).

cnf(c_667,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
    | r1_tarski(X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_445])).

cnf(c_1009,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47)) != iProver_top
    | r1_tarski(X0_47,X1_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_2177,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2172,c_1009])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_680,plain,
    ( ~ r1_tarski(X0_47,X1_47)
    | ~ r1_tarski(X2_47,X0_47)
    | r1_tarski(X2_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_996,plain,
    ( r1_tarski(X0_47,X1_47) != iProver_top
    | r1_tarski(X2_47,X0_47) != iProver_top
    | r1_tarski(X2_47,X1_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_2561,plain,
    ( r1_tarski(X0_47,k2_relat_1(sK4)) != iProver_top
    | r1_tarski(X0_47,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2177,c_996])).

cnf(c_4370,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0_47)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3888,c_2561])).

cnf(c_5134,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5129,c_4370])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:37:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.15/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.01  
% 3.15/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.15/1.01  
% 3.15/1.01  ------  iProver source info
% 3.15/1.01  
% 3.15/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.15/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.15/1.01  git: non_committed_changes: false
% 3.15/1.01  git: last_make_outside_of_git: false
% 3.15/1.01  
% 3.15/1.01  ------ 
% 3.15/1.01  
% 3.15/1.01  ------ Input Options
% 3.15/1.01  
% 3.15/1.01  --out_options                           all
% 3.15/1.01  --tptp_safe_out                         true
% 3.15/1.01  --problem_path                          ""
% 3.15/1.01  --include_path                          ""
% 3.15/1.01  --clausifier                            res/vclausify_rel
% 3.15/1.01  --clausifier_options                    --mode clausify
% 3.15/1.01  --stdin                                 false
% 3.15/1.01  --stats_out                             all
% 3.15/1.01  
% 3.15/1.01  ------ General Options
% 3.15/1.01  
% 3.15/1.01  --fof                                   false
% 3.15/1.01  --time_out_real                         305.
% 3.15/1.01  --time_out_virtual                      -1.
% 3.15/1.01  --symbol_type_check                     false
% 3.15/1.01  --clausify_out                          false
% 3.15/1.01  --sig_cnt_out                           false
% 3.15/1.01  --trig_cnt_out                          false
% 3.15/1.01  --trig_cnt_out_tolerance                1.
% 3.15/1.01  --trig_cnt_out_sk_spl                   false
% 3.15/1.01  --abstr_cl_out                          false
% 3.15/1.01  
% 3.15/1.01  ------ Global Options
% 3.15/1.01  
% 3.15/1.01  --schedule                              default
% 3.15/1.01  --add_important_lit                     false
% 3.15/1.01  --prop_solver_per_cl                    1000
% 3.15/1.01  --min_unsat_core                        false
% 3.15/1.01  --soft_assumptions                      false
% 3.15/1.01  --soft_lemma_size                       3
% 3.15/1.01  --prop_impl_unit_size                   0
% 3.15/1.01  --prop_impl_unit                        []
% 3.15/1.01  --share_sel_clauses                     true
% 3.15/1.01  --reset_solvers                         false
% 3.15/1.01  --bc_imp_inh                            [conj_cone]
% 3.15/1.01  --conj_cone_tolerance                   3.
% 3.15/1.01  --extra_neg_conj                        none
% 3.15/1.01  --large_theory_mode                     true
% 3.15/1.01  --prolific_symb_bound                   200
% 3.15/1.01  --lt_threshold                          2000
% 3.15/1.01  --clause_weak_htbl                      true
% 3.15/1.01  --gc_record_bc_elim                     false
% 3.15/1.01  
% 3.15/1.01  ------ Preprocessing Options
% 3.15/1.01  
% 3.15/1.01  --preprocessing_flag                    true
% 3.15/1.01  --time_out_prep_mult                    0.1
% 3.15/1.01  --splitting_mode                        input
% 3.15/1.01  --splitting_grd                         true
% 3.15/1.01  --splitting_cvd                         false
% 3.15/1.01  --splitting_cvd_svl                     false
% 3.15/1.01  --splitting_nvd                         32
% 3.15/1.01  --sub_typing                            true
% 3.15/1.01  --prep_gs_sim                           true
% 3.15/1.01  --prep_unflatten                        true
% 3.15/1.01  --prep_res_sim                          true
% 3.15/1.01  --prep_upred                            true
% 3.15/1.01  --prep_sem_filter                       exhaustive
% 3.15/1.01  --prep_sem_filter_out                   false
% 3.15/1.01  --pred_elim                             true
% 3.15/1.01  --res_sim_input                         true
% 3.15/1.01  --eq_ax_congr_red                       true
% 3.15/1.01  --pure_diseq_elim                       true
% 3.15/1.01  --brand_transform                       false
% 3.15/1.01  --non_eq_to_eq                          false
% 3.15/1.01  --prep_def_merge                        true
% 3.15/1.01  --prep_def_merge_prop_impl              false
% 3.15/1.01  --prep_def_merge_mbd                    true
% 3.15/1.01  --prep_def_merge_tr_red                 false
% 3.15/1.01  --prep_def_merge_tr_cl                  false
% 3.15/1.01  --smt_preprocessing                     true
% 3.15/1.01  --smt_ac_axioms                         fast
% 3.15/1.01  --preprocessed_out                      false
% 3.15/1.01  --preprocessed_stats                    false
% 3.15/1.01  
% 3.15/1.01  ------ Abstraction refinement Options
% 3.15/1.01  
% 3.15/1.01  --abstr_ref                             []
% 3.15/1.01  --abstr_ref_prep                        false
% 3.15/1.01  --abstr_ref_until_sat                   false
% 3.15/1.01  --abstr_ref_sig_restrict                funpre
% 3.15/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.15/1.01  --abstr_ref_under                       []
% 3.15/1.01  
% 3.15/1.01  ------ SAT Options
% 3.15/1.01  
% 3.15/1.01  --sat_mode                              false
% 3.15/1.01  --sat_fm_restart_options                ""
% 3.15/1.01  --sat_gr_def                            false
% 3.15/1.01  --sat_epr_types                         true
% 3.15/1.01  --sat_non_cyclic_types                  false
% 3.15/1.01  --sat_finite_models                     false
% 3.15/1.01  --sat_fm_lemmas                         false
% 3.15/1.01  --sat_fm_prep                           false
% 3.15/1.01  --sat_fm_uc_incr                        true
% 3.15/1.01  --sat_out_model                         small
% 3.15/1.01  --sat_out_clauses                       false
% 3.15/1.01  
% 3.15/1.01  ------ QBF Options
% 3.15/1.01  
% 3.15/1.01  --qbf_mode                              false
% 3.15/1.01  --qbf_elim_univ                         false
% 3.15/1.01  --qbf_dom_inst                          none
% 3.15/1.01  --qbf_dom_pre_inst                      false
% 3.15/1.01  --qbf_sk_in                             false
% 3.15/1.01  --qbf_pred_elim                         true
% 3.15/1.01  --qbf_split                             512
% 3.15/1.01  
% 3.15/1.01  ------ BMC1 Options
% 3.15/1.01  
% 3.15/1.01  --bmc1_incremental                      false
% 3.15/1.01  --bmc1_axioms                           reachable_all
% 3.15/1.01  --bmc1_min_bound                        0
% 3.15/1.01  --bmc1_max_bound                        -1
% 3.15/1.01  --bmc1_max_bound_default                -1
% 3.15/1.01  --bmc1_symbol_reachability              true
% 3.15/1.01  --bmc1_property_lemmas                  false
% 3.15/1.01  --bmc1_k_induction                      false
% 3.15/1.01  --bmc1_non_equiv_states                 false
% 3.15/1.01  --bmc1_deadlock                         false
% 3.15/1.01  --bmc1_ucm                              false
% 3.15/1.01  --bmc1_add_unsat_core                   none
% 3.15/1.01  --bmc1_unsat_core_children              false
% 3.15/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.15/1.01  --bmc1_out_stat                         full
% 3.15/1.01  --bmc1_ground_init                      false
% 3.15/1.01  --bmc1_pre_inst_next_state              false
% 3.15/1.01  --bmc1_pre_inst_state                   false
% 3.15/1.01  --bmc1_pre_inst_reach_state             false
% 3.15/1.01  --bmc1_out_unsat_core                   false
% 3.15/1.01  --bmc1_aig_witness_out                  false
% 3.15/1.01  --bmc1_verbose                          false
% 3.15/1.01  --bmc1_dump_clauses_tptp                false
% 3.15/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.15/1.01  --bmc1_dump_file                        -
% 3.15/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.15/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.15/1.01  --bmc1_ucm_extend_mode                  1
% 3.15/1.01  --bmc1_ucm_init_mode                    2
% 3.15/1.01  --bmc1_ucm_cone_mode                    none
% 3.15/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.15/1.01  --bmc1_ucm_relax_model                  4
% 3.15/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.15/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.15/1.01  --bmc1_ucm_layered_model                none
% 3.15/1.01  --bmc1_ucm_max_lemma_size               10
% 3.15/1.01  
% 3.15/1.01  ------ AIG Options
% 3.15/1.01  
% 3.15/1.01  --aig_mode                              false
% 3.15/1.01  
% 3.15/1.01  ------ Instantiation Options
% 3.15/1.01  
% 3.15/1.01  --instantiation_flag                    true
% 3.15/1.01  --inst_sos_flag                         false
% 3.15/1.01  --inst_sos_phase                        true
% 3.15/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.15/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.15/1.01  --inst_lit_sel_side                     num_symb
% 3.15/1.01  --inst_solver_per_active                1400
% 3.15/1.01  --inst_solver_calls_frac                1.
% 3.15/1.01  --inst_passive_queue_type               priority_queues
% 3.15/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.15/1.01  --inst_passive_queues_freq              [25;2]
% 3.15/1.01  --inst_dismatching                      true
% 3.15/1.01  --inst_eager_unprocessed_to_passive     true
% 3.15/1.01  --inst_prop_sim_given                   true
% 3.15/1.01  --inst_prop_sim_new                     false
% 3.15/1.01  --inst_subs_new                         false
% 3.15/1.01  --inst_eq_res_simp                      false
% 3.15/1.01  --inst_subs_given                       false
% 3.15/1.01  --inst_orphan_elimination               true
% 3.15/1.01  --inst_learning_loop_flag               true
% 3.15/1.01  --inst_learning_start                   3000
% 3.15/1.01  --inst_learning_factor                  2
% 3.15/1.01  --inst_start_prop_sim_after_learn       3
% 3.15/1.01  --inst_sel_renew                        solver
% 3.15/1.01  --inst_lit_activity_flag                true
% 3.15/1.01  --inst_restr_to_given                   false
% 3.15/1.01  --inst_activity_threshold               500
% 3.15/1.01  --inst_out_proof                        true
% 3.15/1.01  
% 3.15/1.01  ------ Resolution Options
% 3.15/1.01  
% 3.15/1.01  --resolution_flag                       true
% 3.15/1.01  --res_lit_sel                           adaptive
% 3.15/1.01  --res_lit_sel_side                      none
% 3.15/1.01  --res_ordering                          kbo
% 3.15/1.01  --res_to_prop_solver                    active
% 3.15/1.01  --res_prop_simpl_new                    false
% 3.15/1.01  --res_prop_simpl_given                  true
% 3.15/1.01  --res_passive_queue_type                priority_queues
% 3.15/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.15/1.01  --res_passive_queues_freq               [15;5]
% 3.15/1.01  --res_forward_subs                      full
% 3.15/1.01  --res_backward_subs                     full
% 3.15/1.01  --res_forward_subs_resolution           true
% 3.15/1.01  --res_backward_subs_resolution          true
% 3.15/1.01  --res_orphan_elimination                true
% 3.15/1.01  --res_time_limit                        2.
% 3.15/1.01  --res_out_proof                         true
% 3.15/1.01  
% 3.15/1.01  ------ Superposition Options
% 3.15/1.01  
% 3.15/1.01  --superposition_flag                    true
% 3.15/1.01  --sup_passive_queue_type                priority_queues
% 3.15/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.15/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.15/1.01  --demod_completeness_check              fast
% 3.15/1.01  --demod_use_ground                      true
% 3.15/1.01  --sup_to_prop_solver                    passive
% 3.15/1.01  --sup_prop_simpl_new                    true
% 3.15/1.01  --sup_prop_simpl_given                  true
% 3.15/1.01  --sup_fun_splitting                     false
% 3.15/1.01  --sup_smt_interval                      50000
% 3.15/1.01  
% 3.15/1.01  ------ Superposition Simplification Setup
% 3.15/1.01  
% 3.15/1.01  --sup_indices_passive                   []
% 3.15/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.15/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/1.01  --sup_full_bw                           [BwDemod]
% 3.15/1.01  --sup_immed_triv                        [TrivRules]
% 3.15/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.15/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/1.01  --sup_immed_bw_main                     []
% 3.15/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.15/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.15/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.15/1.01  
% 3.15/1.01  ------ Combination Options
% 3.15/1.01  
% 3.15/1.01  --comb_res_mult                         3
% 3.15/1.01  --comb_sup_mult                         2
% 3.15/1.01  --comb_inst_mult                        10
% 3.15/1.01  
% 3.15/1.01  ------ Debug Options
% 3.15/1.01  
% 3.15/1.01  --dbg_backtrace                         false
% 3.15/1.01  --dbg_dump_prop_clauses                 false
% 3.15/1.01  --dbg_dump_prop_clauses_file            -
% 3.15/1.01  --dbg_out_stat                          false
% 3.15/1.01  ------ Parsing...
% 3.15/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.15/1.01  
% 3.15/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.15/1.01  
% 3.15/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.15/1.01  
% 3.15/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.15/1.01  ------ Proving...
% 3.15/1.01  ------ Problem Properties 
% 3.15/1.01  
% 3.15/1.01  
% 3.15/1.01  clauses                                 16
% 3.15/1.01  conjectures                             2
% 3.15/1.01  EPR                                     1
% 3.15/1.01  Horn                                    15
% 3.15/1.01  unary                                   3
% 3.15/1.01  binary                                  7
% 3.15/1.01  lits                                    36
% 3.15/1.01  lits eq                                 5
% 3.15/1.01  fd_pure                                 0
% 3.15/1.01  fd_pseudo                               0
% 3.15/1.01  fd_cond                                 0
% 3.15/1.01  fd_pseudo_cond                          0
% 3.15/1.01  AC symbols                              0
% 3.15/1.01  
% 3.15/1.01  ------ Schedule dynamic 5 is on 
% 3.15/1.01  
% 3.15/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.15/1.01  
% 3.15/1.01  
% 3.15/1.01  ------ 
% 3.15/1.01  Current options:
% 3.15/1.01  ------ 
% 3.15/1.01  
% 3.15/1.01  ------ Input Options
% 3.15/1.01  
% 3.15/1.01  --out_options                           all
% 3.15/1.01  --tptp_safe_out                         true
% 3.15/1.01  --problem_path                          ""
% 3.15/1.01  --include_path                          ""
% 3.15/1.01  --clausifier                            res/vclausify_rel
% 3.15/1.01  --clausifier_options                    --mode clausify
% 3.15/1.01  --stdin                                 false
% 3.15/1.01  --stats_out                             all
% 3.15/1.01  
% 3.15/1.01  ------ General Options
% 3.15/1.01  
% 3.15/1.01  --fof                                   false
% 3.15/1.01  --time_out_real                         305.
% 3.15/1.01  --time_out_virtual                      -1.
% 3.15/1.01  --symbol_type_check                     false
% 3.15/1.01  --clausify_out                          false
% 3.15/1.01  --sig_cnt_out                           false
% 3.15/1.01  --trig_cnt_out                          false
% 3.15/1.01  --trig_cnt_out_tolerance                1.
% 3.15/1.01  --trig_cnt_out_sk_spl                   false
% 3.15/1.01  --abstr_cl_out                          false
% 3.15/1.01  
% 3.15/1.01  ------ Global Options
% 3.15/1.01  
% 3.15/1.01  --schedule                              default
% 3.15/1.01  --add_important_lit                     false
% 3.15/1.01  --prop_solver_per_cl                    1000
% 3.15/1.01  --min_unsat_core                        false
% 3.15/1.01  --soft_assumptions                      false
% 3.15/1.01  --soft_lemma_size                       3
% 3.15/1.01  --prop_impl_unit_size                   0
% 3.15/1.01  --prop_impl_unit                        []
% 3.15/1.01  --share_sel_clauses                     true
% 3.15/1.01  --reset_solvers                         false
% 3.15/1.01  --bc_imp_inh                            [conj_cone]
% 3.15/1.01  --conj_cone_tolerance                   3.
% 3.15/1.01  --extra_neg_conj                        none
% 3.15/1.01  --large_theory_mode                     true
% 3.15/1.01  --prolific_symb_bound                   200
% 3.15/1.01  --lt_threshold                          2000
% 3.15/1.01  --clause_weak_htbl                      true
% 3.15/1.01  --gc_record_bc_elim                     false
% 3.15/1.01  
% 3.15/1.01  ------ Preprocessing Options
% 3.15/1.01  
% 3.15/1.01  --preprocessing_flag                    true
% 3.15/1.01  --time_out_prep_mult                    0.1
% 3.15/1.01  --splitting_mode                        input
% 3.15/1.01  --splitting_grd                         true
% 3.15/1.01  --splitting_cvd                         false
% 3.15/1.01  --splitting_cvd_svl                     false
% 3.15/1.01  --splitting_nvd                         32
% 3.15/1.01  --sub_typing                            true
% 3.15/1.01  --prep_gs_sim                           true
% 3.15/1.01  --prep_unflatten                        true
% 3.15/1.01  --prep_res_sim                          true
% 3.15/1.01  --prep_upred                            true
% 3.15/1.01  --prep_sem_filter                       exhaustive
% 3.15/1.01  --prep_sem_filter_out                   false
% 3.15/1.01  --pred_elim                             true
% 3.15/1.01  --res_sim_input                         true
% 3.15/1.01  --eq_ax_congr_red                       true
% 3.15/1.01  --pure_diseq_elim                       true
% 3.15/1.01  --brand_transform                       false
% 3.15/1.01  --non_eq_to_eq                          false
% 3.15/1.01  --prep_def_merge                        true
% 3.15/1.01  --prep_def_merge_prop_impl              false
% 3.15/1.01  --prep_def_merge_mbd                    true
% 3.15/1.01  --prep_def_merge_tr_red                 false
% 3.15/1.01  --prep_def_merge_tr_cl                  false
% 3.15/1.01  --smt_preprocessing                     true
% 3.15/1.01  --smt_ac_axioms                         fast
% 3.15/1.01  --preprocessed_out                      false
% 3.15/1.01  --preprocessed_stats                    false
% 3.15/1.01  
% 3.15/1.01  ------ Abstraction refinement Options
% 3.15/1.01  
% 3.15/1.01  --abstr_ref                             []
% 3.15/1.01  --abstr_ref_prep                        false
% 3.15/1.01  --abstr_ref_until_sat                   false
% 3.15/1.01  --abstr_ref_sig_restrict                funpre
% 3.15/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.15/1.01  --abstr_ref_under                       []
% 3.15/1.01  
% 3.15/1.01  ------ SAT Options
% 3.15/1.01  
% 3.15/1.01  --sat_mode                              false
% 3.15/1.01  --sat_fm_restart_options                ""
% 3.15/1.01  --sat_gr_def                            false
% 3.15/1.01  --sat_epr_types                         true
% 3.15/1.01  --sat_non_cyclic_types                  false
% 3.15/1.01  --sat_finite_models                     false
% 3.15/1.01  --sat_fm_lemmas                         false
% 3.15/1.01  --sat_fm_prep                           false
% 3.15/1.01  --sat_fm_uc_incr                        true
% 3.15/1.01  --sat_out_model                         small
% 3.15/1.01  --sat_out_clauses                       false
% 3.15/1.01  
% 3.15/1.01  ------ QBF Options
% 3.15/1.01  
% 3.15/1.01  --qbf_mode                              false
% 3.15/1.01  --qbf_elim_univ                         false
% 3.15/1.01  --qbf_dom_inst                          none
% 3.15/1.01  --qbf_dom_pre_inst                      false
% 3.15/1.01  --qbf_sk_in                             false
% 3.15/1.01  --qbf_pred_elim                         true
% 3.15/1.01  --qbf_split                             512
% 3.15/1.01  
% 3.15/1.01  ------ BMC1 Options
% 3.15/1.01  
% 3.15/1.01  --bmc1_incremental                      false
% 3.15/1.01  --bmc1_axioms                           reachable_all
% 3.15/1.01  --bmc1_min_bound                        0
% 3.15/1.01  --bmc1_max_bound                        -1
% 3.15/1.01  --bmc1_max_bound_default                -1
% 3.15/1.01  --bmc1_symbol_reachability              true
% 3.15/1.01  --bmc1_property_lemmas                  false
% 3.15/1.01  --bmc1_k_induction                      false
% 3.15/1.01  --bmc1_non_equiv_states                 false
% 3.15/1.01  --bmc1_deadlock                         false
% 3.15/1.01  --bmc1_ucm                              false
% 3.15/1.01  --bmc1_add_unsat_core                   none
% 3.15/1.01  --bmc1_unsat_core_children              false
% 3.15/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.15/1.01  --bmc1_out_stat                         full
% 3.15/1.01  --bmc1_ground_init                      false
% 3.15/1.01  --bmc1_pre_inst_next_state              false
% 3.15/1.01  --bmc1_pre_inst_state                   false
% 3.15/1.01  --bmc1_pre_inst_reach_state             false
% 3.15/1.01  --bmc1_out_unsat_core                   false
% 3.15/1.01  --bmc1_aig_witness_out                  false
% 3.15/1.01  --bmc1_verbose                          false
% 3.15/1.01  --bmc1_dump_clauses_tptp                false
% 3.15/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.15/1.01  --bmc1_dump_file                        -
% 3.15/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.15/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.15/1.01  --bmc1_ucm_extend_mode                  1
% 3.15/1.01  --bmc1_ucm_init_mode                    2
% 3.15/1.01  --bmc1_ucm_cone_mode                    none
% 3.15/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.15/1.01  --bmc1_ucm_relax_model                  4
% 3.15/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.15/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.15/1.01  --bmc1_ucm_layered_model                none
% 3.15/1.01  --bmc1_ucm_max_lemma_size               10
% 3.15/1.01  
% 3.15/1.01  ------ AIG Options
% 3.15/1.01  
% 3.15/1.01  --aig_mode                              false
% 3.15/1.01  
% 3.15/1.01  ------ Instantiation Options
% 3.15/1.01  
% 3.15/1.01  --instantiation_flag                    true
% 3.15/1.01  --inst_sos_flag                         false
% 3.15/1.01  --inst_sos_phase                        true
% 3.15/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.15/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.15/1.01  --inst_lit_sel_side                     none
% 3.15/1.01  --inst_solver_per_active                1400
% 3.15/1.01  --inst_solver_calls_frac                1.
% 3.15/1.01  --inst_passive_queue_type               priority_queues
% 3.15/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.15/1.01  --inst_passive_queues_freq              [25;2]
% 3.15/1.01  --inst_dismatching                      true
% 3.15/1.01  --inst_eager_unprocessed_to_passive     true
% 3.15/1.01  --inst_prop_sim_given                   true
% 3.15/1.01  --inst_prop_sim_new                     false
% 3.15/1.01  --inst_subs_new                         false
% 3.15/1.01  --inst_eq_res_simp                      false
% 3.15/1.01  --inst_subs_given                       false
% 3.15/1.01  --inst_orphan_elimination               true
% 3.15/1.01  --inst_learning_loop_flag               true
% 3.15/1.01  --inst_learning_start                   3000
% 3.15/1.01  --inst_learning_factor                  2
% 3.15/1.01  --inst_start_prop_sim_after_learn       3
% 3.15/1.01  --inst_sel_renew                        solver
% 3.15/1.01  --inst_lit_activity_flag                true
% 3.15/1.01  --inst_restr_to_given                   false
% 3.15/1.01  --inst_activity_threshold               500
% 3.15/1.01  --inst_out_proof                        true
% 3.15/1.01  
% 3.15/1.01  ------ Resolution Options
% 3.15/1.01  
% 3.15/1.01  --resolution_flag                       false
% 3.15/1.01  --res_lit_sel                           adaptive
% 3.15/1.01  --res_lit_sel_side                      none
% 3.15/1.01  --res_ordering                          kbo
% 3.15/1.01  --res_to_prop_solver                    active
% 3.15/1.01  --res_prop_simpl_new                    false
% 3.15/1.01  --res_prop_simpl_given                  true
% 3.15/1.01  --res_passive_queue_type                priority_queues
% 3.15/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.15/1.01  --res_passive_queues_freq               [15;5]
% 3.15/1.01  --res_forward_subs                      full
% 3.15/1.01  --res_backward_subs                     full
% 3.15/1.01  --res_forward_subs_resolution           true
% 3.15/1.01  --res_backward_subs_resolution          true
% 3.15/1.01  --res_orphan_elimination                true
% 3.15/1.01  --res_time_limit                        2.
% 3.15/1.01  --res_out_proof                         true
% 3.15/1.01  
% 3.15/1.01  ------ Superposition Options
% 3.15/1.01  
% 3.15/1.01  --superposition_flag                    true
% 3.15/1.01  --sup_passive_queue_type                priority_queues
% 3.15/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.15/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.15/1.01  --demod_completeness_check              fast
% 3.15/1.01  --demod_use_ground                      true
% 3.15/1.01  --sup_to_prop_solver                    passive
% 3.15/1.01  --sup_prop_simpl_new                    true
% 3.15/1.01  --sup_prop_simpl_given                  true
% 3.15/1.01  --sup_fun_splitting                     false
% 3.15/1.01  --sup_smt_interval                      50000
% 3.15/1.01  
% 3.15/1.01  ------ Superposition Simplification Setup
% 3.15/1.01  
% 3.15/1.01  --sup_indices_passive                   []
% 3.15/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.15/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/1.01  --sup_full_bw                           [BwDemod]
% 3.15/1.01  --sup_immed_triv                        [TrivRules]
% 3.15/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.15/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/1.01  --sup_immed_bw_main                     []
% 3.15/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.15/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.15/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.15/1.01  
% 3.15/1.01  ------ Combination Options
% 3.15/1.01  
% 3.15/1.01  --comb_res_mult                         3
% 3.15/1.01  --comb_sup_mult                         2
% 3.15/1.01  --comb_inst_mult                        10
% 3.15/1.01  
% 3.15/1.01  ------ Debug Options
% 3.15/1.01  
% 3.15/1.01  --dbg_backtrace                         false
% 3.15/1.01  --dbg_dump_prop_clauses                 false
% 3.15/1.01  --dbg_dump_prop_clauses_file            -
% 3.15/1.01  --dbg_out_stat                          false
% 3.15/1.01  
% 3.15/1.01  
% 3.15/1.01  
% 3.15/1.01  
% 3.15/1.01  ------ Proving...
% 3.15/1.01  
% 3.15/1.01  
% 3.15/1.01  % SZS status Theorem for theBenchmark.p
% 3.15/1.01  
% 3.15/1.01   Resolution empty clause
% 3.15/1.01  
% 3.15/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.15/1.01  
% 3.15/1.01  fof(f8,axiom,(
% 3.15/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 3.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.01  
% 3.15/1.01  fof(f24,plain,(
% 3.15/1.01    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 3.15/1.01    inference(ennf_transformation,[],[f8])).
% 3.15/1.01  
% 3.15/1.01  fof(f49,plain,(
% 3.15/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 3.15/1.01    inference(cnf_transformation,[],[f24])).
% 3.15/1.01  
% 3.15/1.01  fof(f14,axiom,(
% 3.15/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.01  
% 3.15/1.01  fof(f30,plain,(
% 3.15/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.15/1.01    inference(ennf_transformation,[],[f14])).
% 3.15/1.01  
% 3.15/1.01  fof(f31,plain,(
% 3.15/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.15/1.01    inference(flattening,[],[f30])).
% 3.15/1.01  
% 3.15/1.01  fof(f55,plain,(
% 3.15/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.15/1.01    inference(cnf_transformation,[],[f31])).
% 3.15/1.01  
% 3.15/1.01  fof(f15,conjecture,(
% 3.15/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.01  
% 3.15/1.01  fof(f16,negated_conjecture,(
% 3.15/1.01    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.15/1.01    inference(negated_conjecture,[],[f15])).
% 3.15/1.01  
% 3.15/1.01  fof(f32,plain,(
% 3.15/1.01    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.15/1.01    inference(ennf_transformation,[],[f16])).
% 3.15/1.01  
% 3.15/1.01  fof(f37,plain,(
% 3.15/1.01    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))))),
% 3.15/1.01    introduced(choice_axiom,[])).
% 3.15/1.01  
% 3.15/1.01  fof(f38,plain,(
% 3.15/1.01    ~m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 3.15/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f37])).
% 3.15/1.01  
% 3.15/1.01  fof(f56,plain,(
% 3.15/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 3.15/1.01    inference(cnf_transformation,[],[f38])).
% 3.15/1.01  
% 3.15/1.01  fof(f13,axiom,(
% 3.15/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3))),
% 3.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.01  
% 3.15/1.01  fof(f29,plain,(
% 3.15/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/1.01    inference(ennf_transformation,[],[f13])).
% 3.15/1.01  
% 3.15/1.01  fof(f54,plain,(
% 3.15/1.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/1.01    inference(cnf_transformation,[],[f29])).
% 3.15/1.01  
% 3.15/1.01  fof(f57,plain,(
% 3.15/1.01    ~m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.15/1.01    inference(cnf_transformation,[],[f38])).
% 3.15/1.01  
% 3.15/1.01  fof(f10,axiom,(
% 3.15/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.01  
% 3.15/1.01  fof(f26,plain,(
% 3.15/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/1.01    inference(ennf_transformation,[],[f10])).
% 3.15/1.01  
% 3.15/1.01  fof(f51,plain,(
% 3.15/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/1.01    inference(cnf_transformation,[],[f26])).
% 3.15/1.01  
% 3.15/1.01  fof(f9,axiom,(
% 3.15/1.01    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.01  
% 3.15/1.01  fof(f25,plain,(
% 3.15/1.01    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.15/1.01    inference(ennf_transformation,[],[f9])).
% 3.15/1.01  
% 3.15/1.01  fof(f50,plain,(
% 3.15/1.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.15/1.01    inference(cnf_transformation,[],[f25])).
% 3.15/1.01  
% 3.15/1.01  fof(f5,axiom,(
% 3.15/1.01    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.01  
% 3.15/1.01  fof(f21,plain,(
% 3.15/1.01    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.15/1.01    inference(ennf_transformation,[],[f5])).
% 3.15/1.01  
% 3.15/1.01  fof(f22,plain,(
% 3.15/1.01    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.15/1.01    inference(flattening,[],[f21])).
% 3.15/1.01  
% 3.15/1.01  fof(f46,plain,(
% 3.15/1.01    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.15/1.01    inference(cnf_transformation,[],[f22])).
% 3.15/1.01  
% 3.15/1.01  fof(f6,axiom,(
% 3.15/1.01    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.01  
% 3.15/1.01  fof(f47,plain,(
% 3.15/1.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.15/1.01    inference(cnf_transformation,[],[f6])).
% 3.15/1.01  
% 3.15/1.01  fof(f7,axiom,(
% 3.15/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.01  
% 3.15/1.01  fof(f23,plain,(
% 3.15/1.01    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.15/1.01    inference(ennf_transformation,[],[f7])).
% 3.15/1.01  
% 3.15/1.01  fof(f48,plain,(
% 3.15/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.15/1.01    inference(cnf_transformation,[],[f23])).
% 3.15/1.01  
% 3.15/1.01  fof(f12,axiom,(
% 3.15/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.01  
% 3.15/1.01  fof(f28,plain,(
% 3.15/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/1.01    inference(ennf_transformation,[],[f12])).
% 3.15/1.01  
% 3.15/1.01  fof(f53,plain,(
% 3.15/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/1.01    inference(cnf_transformation,[],[f28])).
% 3.15/1.01  
% 3.15/1.01  fof(f11,axiom,(
% 3.15/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.01  
% 3.15/1.01  fof(f27,plain,(
% 3.15/1.01    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/1.01    inference(ennf_transformation,[],[f11])).
% 3.15/1.01  
% 3.15/1.01  fof(f52,plain,(
% 3.15/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/1.01    inference(cnf_transformation,[],[f27])).
% 3.15/1.01  
% 3.15/1.01  fof(f3,axiom,(
% 3.15/1.01    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.01  
% 3.15/1.01  fof(f44,plain,(
% 3.15/1.01    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.15/1.01    inference(cnf_transformation,[],[f3])).
% 3.15/1.01  
% 3.15/1.01  fof(f4,axiom,(
% 3.15/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.01  
% 3.15/1.01  fof(f19,plain,(
% 3.15/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.15/1.01    inference(ennf_transformation,[],[f4])).
% 3.15/1.01  
% 3.15/1.01  fof(f20,plain,(
% 3.15/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.15/1.01    inference(flattening,[],[f19])).
% 3.15/1.01  
% 3.15/1.01  fof(f45,plain,(
% 3.15/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.15/1.01    inference(cnf_transformation,[],[f20])).
% 3.15/1.01  
% 3.15/1.01  fof(f2,axiom,(
% 3.15/1.01    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.01  
% 3.15/1.01  fof(f33,plain,(
% 3.15/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.15/1.01    inference(nnf_transformation,[],[f2])).
% 3.15/1.01  
% 3.15/1.01  fof(f34,plain,(
% 3.15/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.15/1.01    inference(rectify,[],[f33])).
% 3.15/1.01  
% 3.15/1.01  fof(f35,plain,(
% 3.15/1.01    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.15/1.01    introduced(choice_axiom,[])).
% 3.15/1.01  
% 3.15/1.01  fof(f36,plain,(
% 3.15/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.15/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 3.15/1.01  
% 3.15/1.01  fof(f40,plain,(
% 3.15/1.01    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.15/1.01    inference(cnf_transformation,[],[f36])).
% 3.15/1.01  
% 3.15/1.01  fof(f59,plain,(
% 3.15/1.01    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.15/1.01    inference(equality_resolution,[],[f40])).
% 3.15/1.01  
% 3.15/1.01  fof(f1,axiom,(
% 3.15/1.01    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.15/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.01  
% 3.15/1.01  fof(f17,plain,(
% 3.15/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.15/1.01    inference(ennf_transformation,[],[f1])).
% 3.15/1.01  
% 3.15/1.01  fof(f18,plain,(
% 3.15/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.15/1.01    inference(flattening,[],[f17])).
% 3.15/1.01  
% 3.15/1.01  fof(f39,plain,(
% 3.15/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.15/1.01    inference(cnf_transformation,[],[f18])).
% 3.15/1.01  
% 3.15/1.01  cnf(c_10,plain,
% 3.15/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 3.15/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_676,plain,
% 3.15/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0_47,X1_47)),X1_47)
% 3.15/1.01      | ~ v1_relat_1(X0_47) ),
% 3.15/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1000,plain,
% 3.15/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0_47,X1_47)),X1_47) = iProver_top
% 3.15/1.01      | v1_relat_1(X0_47) != iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_16,plain,
% 3.15/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.01      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.15/1.01      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.15/1.01      | ~ v1_relat_1(X0) ),
% 3.15/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_670,plain,
% 3.15/1.01      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 3.15/1.01      | ~ r1_tarski(k1_relat_1(X0_47),X1_47)
% 3.15/1.01      | ~ r1_tarski(k2_relat_1(X0_47),X2_47)
% 3.15/1.01      | ~ v1_relat_1(X0_47) ),
% 3.15/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1006,plain,
% 3.15/1.01      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) = iProver_top
% 3.15/1.01      | r1_tarski(k1_relat_1(X0_47),X1_47) != iProver_top
% 3.15/1.01      | r1_tarski(k2_relat_1(X0_47),X2_47) != iProver_top
% 3.15/1.01      | v1_relat_1(X0_47) != iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_670]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_18,negated_conjecture,
% 3.15/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 3.15/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_668,negated_conjecture,
% 3.15/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 3.15/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1008,plain,
% 3.15/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_15,plain,
% 3.15/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.01      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.15/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_671,plain,
% 3.15/1.01      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 3.15/1.01      | k5_relset_1(X1_47,X2_47,X0_47,X3_47) = k7_relat_1(X0_47,X3_47) ),
% 3.15/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1005,plain,
% 3.15/1.01      ( k5_relset_1(X0_47,X1_47,X2_47,X3_47) = k7_relat_1(X2_47,X3_47)
% 3.15/1.01      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_2831,plain,
% 3.15/1.01      ( k5_relset_1(sK1,sK3,sK4,X0_47) = k7_relat_1(sK4,X0_47) ),
% 3.15/1.01      inference(superposition,[status(thm)],[c_1008,c_1005]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_17,negated_conjecture,
% 3.15/1.01      ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.15/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_669,negated_conjecture,
% 3.15/1.01      ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.15/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1007,plain,
% 3.15/1.01      ( m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_3488,plain,
% 3.15/1.01      ( m1_subset_1(k7_relat_1(sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.15/1.01      inference(demodulation,[status(thm)],[c_2831,c_1007]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_3492,plain,
% 3.15/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(sK4,sK2)),sK2) != iProver_top
% 3.15/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top
% 3.15/1.01      | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
% 3.15/1.01      inference(superposition,[status(thm)],[c_1006,c_3488]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_12,plain,
% 3.15/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.15/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_674,plain,
% 3.15/1.01      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 3.15/1.01      | v1_relat_1(X0_47) ),
% 3.15/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1002,plain,
% 3.15/1.01      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
% 3.15/1.01      | v1_relat_1(X0_47) = iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1350,plain,
% 3.15/1.01      ( v1_relat_1(sK4) = iProver_top ),
% 3.15/1.01      inference(superposition,[status(thm)],[c_1008,c_1002]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_11,plain,
% 3.15/1.01      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.15/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_675,plain,
% 3.15/1.01      ( ~ v1_relat_1(X0_47)
% 3.15/1.01      | k5_relat_1(k6_relat_1(X1_47),X0_47) = k7_relat_1(X0_47,X1_47) ),
% 3.15/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1001,plain,
% 3.15/1.01      ( k5_relat_1(k6_relat_1(X0_47),X1_47) = k7_relat_1(X1_47,X0_47)
% 3.15/1.01      | v1_relat_1(X1_47) != iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1776,plain,
% 3.15/1.01      ( k5_relat_1(k6_relat_1(X0_47),sK4) = k7_relat_1(sK4,X0_47) ),
% 3.15/1.01      inference(superposition,[status(thm)],[c_1350,c_1001]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_7,plain,
% 3.15/1.01      ( ~ v1_relat_1(X0) | ~ v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.15/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_679,plain,
% 3.15/1.01      ( ~ v1_relat_1(X0_47)
% 3.15/1.01      | ~ v1_relat_1(X1_47)
% 3.15/1.01      | v1_relat_1(k5_relat_1(X1_47,X0_47)) ),
% 3.15/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_997,plain,
% 3.15/1.01      ( v1_relat_1(X0_47) != iProver_top
% 3.15/1.01      | v1_relat_1(X1_47) != iProver_top
% 3.15/1.01      | v1_relat_1(k5_relat_1(X1_47,X0_47)) = iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_2006,plain,
% 3.15/1.01      ( v1_relat_1(k7_relat_1(sK4,X0_47)) = iProver_top
% 3.15/1.01      | v1_relat_1(k6_relat_1(X0_47)) != iProver_top
% 3.15/1.01      | v1_relat_1(sK4) != iProver_top ),
% 3.15/1.01      inference(superposition,[status(thm)],[c_1776,c_997]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_19,plain,
% 3.15/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_8,plain,
% 3.15/1.01      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.15/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_678,plain,
% 3.15/1.01      ( v1_relat_1(k6_relat_1(X0_47)) ),
% 3.15/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_711,plain,
% 3.15/1.01      ( v1_relat_1(k6_relat_1(X0_47)) = iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1122,plain,
% 3.15/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.15/1.01      | v1_relat_1(sK4) ),
% 3.15/1.01      inference(instantiation,[status(thm)],[c_674]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1123,plain,
% 3.15/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.15/1.01      | v1_relat_1(sK4) = iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_1122]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_2566,plain,
% 3.15/1.01      ( v1_relat_1(k7_relat_1(sK4,X0_47)) = iProver_top ),
% 3.15/1.01      inference(global_propositional_subsumption,
% 3.15/1.01                [status(thm)],
% 3.15/1.01                [c_2006,c_19,c_711,c_1123]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_3883,plain,
% 3.15/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(sK4,sK2)),sK2) != iProver_top
% 3.15/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top ),
% 3.15/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_3492,c_2566]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_3885,plain,
% 3.15/1.01      ( r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top
% 3.15/1.01      | v1_relat_1(sK4) != iProver_top ),
% 3.15/1.01      inference(superposition,[status(thm)],[c_1000,c_3883]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_5129,plain,
% 3.15/1.01      ( r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top ),
% 3.15/1.01      inference(global_propositional_subsumption,
% 3.15/1.01                [status(thm)],
% 3.15/1.01                [c_3885,c_19,c_1123]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_9,plain,
% 3.15/1.01      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.15/1.01      | ~ v1_relat_1(X1)
% 3.15/1.01      | ~ v1_relat_1(X0) ),
% 3.15/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_677,plain,
% 3.15/1.01      ( r1_tarski(k2_relat_1(k5_relat_1(X0_47,X1_47)),k2_relat_1(X1_47))
% 3.15/1.01      | ~ v1_relat_1(X0_47)
% 3.15/1.01      | ~ v1_relat_1(X1_47) ),
% 3.15/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_999,plain,
% 3.15/1.01      ( r1_tarski(k2_relat_1(k5_relat_1(X0_47,X1_47)),k2_relat_1(X1_47)) = iProver_top
% 3.15/1.01      | v1_relat_1(X0_47) != iProver_top
% 3.15/1.01      | v1_relat_1(X1_47) != iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_3242,plain,
% 3.15/1.01      ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0_47)),k2_relat_1(sK4)) = iProver_top
% 3.15/1.01      | v1_relat_1(k6_relat_1(X0_47)) != iProver_top
% 3.15/1.01      | v1_relat_1(sK4) != iProver_top ),
% 3.15/1.01      inference(superposition,[status(thm)],[c_1776,c_999]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_3888,plain,
% 3.15/1.01      ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0_47)),k2_relat_1(sK4)) = iProver_top ),
% 3.15/1.01      inference(global_propositional_subsumption,
% 3.15/1.01                [status(thm)],
% 3.15/1.01                [c_3242,c_19,c_711,c_1123]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_14,plain,
% 3.15/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.15/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_672,plain,
% 3.15/1.01      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 3.15/1.01      | k2_relset_1(X1_47,X2_47,X0_47) = k2_relat_1(X0_47) ),
% 3.15/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1004,plain,
% 3.15/1.01      ( k2_relset_1(X0_47,X1_47,X2_47) = k2_relat_1(X2_47)
% 3.15/1.01      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_672]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1355,plain,
% 3.15/1.01      ( k2_relset_1(sK1,sK3,sK4) = k2_relat_1(sK4) ),
% 3.15/1.01      inference(superposition,[status(thm)],[c_1008,c_1004]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_13,plain,
% 3.15/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.01      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.15/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_673,plain,
% 3.15/1.01      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 3.15/1.01      | m1_subset_1(k2_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X2_47)) ),
% 3.15/1.01      inference(subtyping,[status(esa)],[c_13]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1003,plain,
% 3.15/1.01      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
% 3.15/1.01      | m1_subset_1(k2_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X2_47)) = iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_673]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_2003,plain,
% 3.15/1.01      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
% 3.15/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.15/1.01      inference(superposition,[status(thm)],[c_1355,c_1003]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_2172,plain,
% 3.15/1.01      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
% 3.15/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2003,c_19]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_5,plain,
% 3.15/1.01      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.15/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_6,plain,
% 3.15/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.15/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_263,plain,
% 3.15/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 3.15/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_6]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_264,plain,
% 3.15/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.15/1.01      inference(unflattening,[status(thm)],[c_263]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_4,plain,
% 3.15/1.01      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.15/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_410,plain,
% 3.15/1.01      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.15/1.01      inference(prop_impl,[status(thm)],[c_4]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_411,plain,
% 3.15/1.01      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.15/1.01      inference(renaming,[status(thm)],[c_410]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_445,plain,
% 3.15/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.15/1.01      inference(bin_hyper_res,[status(thm)],[c_264,c_411]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_667,plain,
% 3.15/1.01      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47)) | r1_tarski(X0_47,X1_47) ),
% 3.15/1.01      inference(subtyping,[status(esa)],[c_445]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1009,plain,
% 3.15/1.01      ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47)) != iProver_top
% 3.15/1.01      | r1_tarski(X0_47,X1_47) = iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_2177,plain,
% 3.15/1.01      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 3.15/1.01      inference(superposition,[status(thm)],[c_2172,c_1009]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_0,plain,
% 3.15/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.15/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_680,plain,
% 3.15/1.01      ( ~ r1_tarski(X0_47,X1_47)
% 3.15/1.01      | ~ r1_tarski(X2_47,X0_47)
% 3.15/1.01      | r1_tarski(X2_47,X1_47) ),
% 3.15/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_996,plain,
% 3.15/1.01      ( r1_tarski(X0_47,X1_47) != iProver_top
% 3.15/1.01      | r1_tarski(X2_47,X0_47) != iProver_top
% 3.15/1.01      | r1_tarski(X2_47,X1_47) = iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_2561,plain,
% 3.15/1.01      ( r1_tarski(X0_47,k2_relat_1(sK4)) != iProver_top
% 3.15/1.01      | r1_tarski(X0_47,sK3) = iProver_top ),
% 3.15/1.01      inference(superposition,[status(thm)],[c_2177,c_996]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_4370,plain,
% 3.15/1.01      ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0_47)),sK3) = iProver_top ),
% 3.15/1.01      inference(superposition,[status(thm)],[c_3888,c_2561]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_5134,plain,
% 3.15/1.01      ( $false ),
% 3.15/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_5129,c_4370]) ).
% 3.15/1.01  
% 3.15/1.01  
% 3.15/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.15/1.01  
% 3.15/1.01  ------                               Statistics
% 3.15/1.01  
% 3.15/1.01  ------ General
% 3.15/1.01  
% 3.15/1.01  abstr_ref_over_cycles:                  0
% 3.15/1.01  abstr_ref_under_cycles:                 0
% 3.15/1.01  gc_basic_clause_elim:                   0
% 3.15/1.01  forced_gc_time:                         0
% 3.15/1.01  parsing_time:                           0.009
% 3.15/1.01  unif_index_cands_time:                  0.
% 3.15/1.01  unif_index_add_time:                    0.
% 3.15/1.01  orderings_time:                         0.
% 3.15/1.01  out_proof_time:                         0.014
% 3.15/1.01  total_time:                             0.229
% 3.15/1.01  num_of_symbols:                         52
% 3.15/1.01  num_of_terms:                           8196
% 3.15/1.01  
% 3.15/1.01  ------ Preprocessing
% 3.15/1.01  
% 3.15/1.01  num_of_splits:                          0
% 3.15/1.01  num_of_split_atoms:                     0
% 3.15/1.01  num_of_reused_defs:                     0
% 3.15/1.01  num_eq_ax_congr_red:                    34
% 3.15/1.01  num_of_sem_filtered_clauses:            1
% 3.15/1.01  num_of_subtypes:                        2
% 3.15/1.01  monotx_restored_types:                  0
% 3.15/1.01  sat_num_of_epr_types:                   0
% 3.15/1.01  sat_num_of_non_cyclic_types:            0
% 3.15/1.01  sat_guarded_non_collapsed_types:        0
% 3.15/1.01  num_pure_diseq_elim:                    0
% 3.15/1.01  simp_replaced_by:                       0
% 3.15/1.01  res_preprocessed:                       114
% 3.15/1.01  prep_upred:                             0
% 3.15/1.01  prep_unflattend:                        11
% 3.15/1.01  smt_new_axioms:                         0
% 3.15/1.01  pred_elim_cands:                        3
% 3.15/1.01  pred_elim:                              2
% 3.15/1.01  pred_elim_cl:                           3
% 3.15/1.01  pred_elim_cycles:                       5
% 3.15/1.01  merged_defs:                            4
% 3.15/1.01  merged_defs_ncl:                        0
% 3.15/1.01  bin_hyper_res:                          5
% 3.15/1.01  prep_cycles:                            5
% 3.15/1.01  pred_elim_time:                         0.004
% 3.15/1.01  splitting_time:                         0.
% 3.15/1.01  sem_filter_time:                        0.
% 3.15/1.01  monotx_time:                            0.
% 3.15/1.01  subtype_inf_time:                       0.
% 3.15/1.01  
% 3.15/1.01  ------ Problem properties
% 3.15/1.01  
% 3.15/1.01  clauses:                                16
% 3.15/1.01  conjectures:                            2
% 3.15/1.01  epr:                                    1
% 3.15/1.01  horn:                                   15
% 3.15/1.01  ground:                                 2
% 3.15/1.01  unary:                                  3
% 3.15/1.01  binary:                                 7
% 3.15/1.01  lits:                                   36
% 3.15/1.01  lits_eq:                                5
% 3.15/1.01  fd_pure:                                0
% 3.15/1.01  fd_pseudo:                              0
% 3.15/1.01  fd_cond:                                0
% 3.15/1.01  fd_pseudo_cond:                         0
% 3.15/1.01  ac_symbols:                             0
% 3.15/1.01  
% 3.15/1.01  ------ Propositional Solver
% 3.15/1.01  
% 3.15/1.01  prop_solver_calls:                      31
% 3.15/1.01  prop_fast_solver_calls:                 620
% 3.15/1.01  smt_solver_calls:                       0
% 3.15/1.01  smt_fast_solver_calls:                  0
% 3.15/1.01  prop_num_of_clauses:                    2772
% 3.15/1.01  prop_preprocess_simplified:             7203
% 3.15/1.01  prop_fo_subsumed:                       6
% 3.15/1.01  prop_solver_time:                       0.
% 3.15/1.01  smt_solver_time:                        0.
% 3.15/1.01  smt_fast_solver_time:                   0.
% 3.15/1.01  prop_fast_solver_time:                  0.
% 3.15/1.01  prop_unsat_core_time:                   0.
% 3.15/1.01  
% 3.15/1.01  ------ QBF
% 3.15/1.01  
% 3.15/1.01  qbf_q_res:                              0
% 3.15/1.01  qbf_num_tautologies:                    0
% 3.15/1.01  qbf_prep_cycles:                        0
% 3.15/1.01  
% 3.15/1.01  ------ BMC1
% 3.15/1.01  
% 3.15/1.01  bmc1_current_bound:                     -1
% 3.15/1.01  bmc1_last_solved_bound:                 -1
% 3.15/1.01  bmc1_unsat_core_size:                   -1
% 3.15/1.01  bmc1_unsat_core_parents_size:           -1
% 3.15/1.01  bmc1_merge_next_fun:                    0
% 3.15/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.15/1.01  
% 3.15/1.01  ------ Instantiation
% 3.15/1.01  
% 3.15/1.01  inst_num_of_clauses:                    719
% 3.15/1.01  inst_num_in_passive:                    387
% 3.15/1.01  inst_num_in_active:                     165
% 3.15/1.01  inst_num_in_unprocessed:                167
% 3.15/1.01  inst_num_of_loops:                      170
% 3.15/1.01  inst_num_of_learning_restarts:          0
% 3.15/1.01  inst_num_moves_active_passive:          3
% 3.15/1.01  inst_lit_activity:                      0
% 3.15/1.01  inst_lit_activity_moves:                0
% 3.15/1.01  inst_num_tautologies:                   0
% 3.15/1.01  inst_num_prop_implied:                  0
% 3.15/1.01  inst_num_existing_simplified:           0
% 3.15/1.01  inst_num_eq_res_simplified:             0
% 3.15/1.01  inst_num_child_elim:                    0
% 3.15/1.01  inst_num_of_dismatching_blockings:      19
% 3.15/1.01  inst_num_of_non_proper_insts:           254
% 3.15/1.01  inst_num_of_duplicates:                 0
% 3.15/1.01  inst_inst_num_from_inst_to_res:         0
% 3.15/1.01  inst_dismatching_checking_time:         0.
% 3.15/1.01  
% 3.15/1.01  ------ Resolution
% 3.15/1.01  
% 3.15/1.01  res_num_of_clauses:                     0
% 3.15/1.01  res_num_in_passive:                     0
% 3.15/1.01  res_num_in_active:                      0
% 3.15/1.01  res_num_of_loops:                       119
% 3.15/1.01  res_forward_subset_subsumed:            5
% 3.15/1.01  res_backward_subset_subsumed:           0
% 3.15/1.01  res_forward_subsumed:                   0
% 3.15/1.01  res_backward_subsumed:                  0
% 3.15/1.01  res_forward_subsumption_resolution:     0
% 3.15/1.01  res_backward_subsumption_resolution:    0
% 3.15/1.01  res_clause_to_clause_subsumption:       86
% 3.15/1.01  res_orphan_elimination:                 0
% 3.15/1.01  res_tautology_del:                      27
% 3.15/1.01  res_num_eq_res_simplified:              0
% 3.15/1.01  res_num_sel_changes:                    0
% 3.15/1.01  res_moves_from_active_to_pass:          0
% 3.15/1.01  
% 3.15/1.01  ------ Superposition
% 3.15/1.01  
% 3.15/1.01  sup_time_total:                         0.
% 3.15/1.01  sup_time_generating:                    0.
% 3.15/1.01  sup_time_sim_full:                      0.
% 3.15/1.01  sup_time_sim_immed:                     0.
% 3.15/1.01  
% 3.15/1.01  sup_num_of_clauses:                     57
% 3.15/1.01  sup_num_in_active:                      31
% 3.15/1.01  sup_num_in_passive:                     26
% 3.15/1.01  sup_num_of_loops:                       32
% 3.15/1.01  sup_fw_superposition:                   20
% 3.15/1.01  sup_bw_superposition:                   26
% 3.15/1.01  sup_immediate_simplified:               3
% 3.15/1.01  sup_given_eliminated:                   0
% 3.15/1.01  comparisons_done:                       0
% 3.15/1.01  comparisons_avoided:                    0
% 3.15/1.01  
% 3.15/1.01  ------ Simplifications
% 3.15/1.01  
% 3.15/1.01  
% 3.15/1.01  sim_fw_subset_subsumed:                 3
% 3.15/1.01  sim_bw_subset_subsumed:                 0
% 3.15/1.01  sim_fw_subsumed:                        0
% 3.15/1.01  sim_bw_subsumed:                        0
% 3.15/1.01  sim_fw_subsumption_res:                 2
% 3.15/1.01  sim_bw_subsumption_res:                 0
% 3.15/1.01  sim_tautology_del:                      1
% 3.15/1.01  sim_eq_tautology_del:                   0
% 3.15/1.01  sim_eq_res_simp:                        0
% 3.15/1.01  sim_fw_demodulated:                     1
% 3.15/1.01  sim_bw_demodulated:                     1
% 3.15/1.01  sim_light_normalised:                   0
% 3.15/1.01  sim_joinable_taut:                      0
% 3.15/1.01  sim_joinable_simp:                      0
% 3.15/1.01  sim_ac_normalised:                      0
% 3.15/1.01  sim_smt_subsumption:                    0
% 3.15/1.01  
%------------------------------------------------------------------------------
