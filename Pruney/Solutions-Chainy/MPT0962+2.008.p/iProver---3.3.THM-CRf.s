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
% DateTime   : Thu Dec  3 12:00:10 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 460 expanded)
%              Number of clauses        :   79 ( 193 expanded)
%              Number of leaves         :   15 (  79 expanded)
%              Depth                    :   22
%              Number of atoms          :  366 (1442 expanded)
%              Number of equality atoms :  168 ( 420 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

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
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
        | ~ v1_funct_1(sK1) )
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f36])).

fof(f65,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f45])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1320,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1317,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1313,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3432,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_1313])).

cnf(c_14696,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1320,c_3432])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_14])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_353,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_349,c_16])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_353])).

cnf(c_1310,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_2452,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_1310])).

cnf(c_6055,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1320,c_2452])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1324,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4000,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1320,c_1324])).

cnf(c_6231,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6055,c_4000])).

cnf(c_14705,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14696,c_6231])).

cnf(c_14719,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14705])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1312,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1319,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1321,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3172,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,X2)
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_1321])).

cnf(c_12386,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK1)),k2_zfmisc_1(X0,sK0)) = k2_zfmisc_1(X0,sK0) ),
    inference(superposition,[status(thm)],[c_1312,c_3172])).

cnf(c_28,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1311,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_15,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1315,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2578,plain,
    ( k2_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_1321])).

cnf(c_8753,plain,
    ( k2_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) = k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_1311,c_2578])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1323,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1322,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2462,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1323,c_1322])).

cnf(c_3073,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2462,c_1322])).

cnf(c_4160,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3073,c_1322])).

cnf(c_9274,plain,
    ( r1_tarski(sK1,k2_xboole_0(k2_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),X0),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8753,c_4160])).

cnf(c_13003,plain,
    ( r1_tarski(sK1,k2_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),sK0),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12386,c_9274])).

cnf(c_9275,plain,
    ( r1_tarski(sK1,k2_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8753,c_3073])).

cnf(c_13004,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12386,c_9275])).

cnf(c_22,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_149,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_27])).

cnf(c_150,negated_conjecture,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(renaming,[status(thm)],[c_149])).

cnf(c_656,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK1) != X1
    | sK0 != X2
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_150])).

cnf(c_657,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(k1_relat_1(sK1),sK0,sK1) != k1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_665,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_xboole_0 = sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_657,c_18])).

cnf(c_1307,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_2131,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_1307])).

cnf(c_13254,plain,
    ( sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13004,c_2131])).

cnf(c_13459,plain,
    ( r1_tarski(sK1,k2_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0),X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13003,c_13254])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1921,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1320,c_1321])).

cnf(c_13460,plain,
    ( r1_tarski(sK1,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13459,c_6,c_1921])).

cnf(c_13476,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13460,c_4000])).

cnf(c_21,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_640,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_150])).

cnf(c_641,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_1308,plain,
    ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1325,plain,
    ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
    | k1_relat_1(sK1) != k1_xboole_0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1308,c_7])).

cnf(c_14533,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13476,c_1325])).

cnf(c_14538,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14533,c_6231,c_13254])).

cnf(c_14539,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14538])).

cnf(c_14540,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14539,c_7])).

cnf(c_81,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_83,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_72,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_74,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14719,c_14540,c_83,c_74])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:35:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 4.03/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/0.99  
% 4.03/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.03/0.99  
% 4.03/0.99  ------  iProver source info
% 4.03/0.99  
% 4.03/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.03/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.03/0.99  git: non_committed_changes: false
% 4.03/0.99  git: last_make_outside_of_git: false
% 4.03/0.99  
% 4.03/0.99  ------ 
% 4.03/0.99  
% 4.03/0.99  ------ Input Options
% 4.03/0.99  
% 4.03/0.99  --out_options                           all
% 4.03/0.99  --tptp_safe_out                         true
% 4.03/0.99  --problem_path                          ""
% 4.03/0.99  --include_path                          ""
% 4.03/0.99  --clausifier                            res/vclausify_rel
% 4.03/0.99  --clausifier_options                    ""
% 4.03/0.99  --stdin                                 false
% 4.03/0.99  --stats_out                             all
% 4.03/0.99  
% 4.03/0.99  ------ General Options
% 4.03/0.99  
% 4.03/0.99  --fof                                   false
% 4.03/0.99  --time_out_real                         305.
% 4.03/0.99  --time_out_virtual                      -1.
% 4.03/0.99  --symbol_type_check                     false
% 4.03/0.99  --clausify_out                          false
% 4.03/0.99  --sig_cnt_out                           false
% 4.03/0.99  --trig_cnt_out                          false
% 4.03/0.99  --trig_cnt_out_tolerance                1.
% 4.03/0.99  --trig_cnt_out_sk_spl                   false
% 4.03/0.99  --abstr_cl_out                          false
% 4.03/0.99  
% 4.03/0.99  ------ Global Options
% 4.03/0.99  
% 4.03/0.99  --schedule                              default
% 4.03/0.99  --add_important_lit                     false
% 4.03/0.99  --prop_solver_per_cl                    1000
% 4.03/0.99  --min_unsat_core                        false
% 4.03/0.99  --soft_assumptions                      false
% 4.03/0.99  --soft_lemma_size                       3
% 4.03/0.99  --prop_impl_unit_size                   0
% 4.03/0.99  --prop_impl_unit                        []
% 4.03/0.99  --share_sel_clauses                     true
% 4.03/0.99  --reset_solvers                         false
% 4.03/0.99  --bc_imp_inh                            [conj_cone]
% 4.03/0.99  --conj_cone_tolerance                   3.
% 4.03/0.99  --extra_neg_conj                        none
% 4.03/0.99  --large_theory_mode                     true
% 4.03/0.99  --prolific_symb_bound                   200
% 4.03/0.99  --lt_threshold                          2000
% 4.03/0.99  --clause_weak_htbl                      true
% 4.03/0.99  --gc_record_bc_elim                     false
% 4.03/0.99  
% 4.03/0.99  ------ Preprocessing Options
% 4.03/0.99  
% 4.03/0.99  --preprocessing_flag                    true
% 4.03/0.99  --time_out_prep_mult                    0.1
% 4.03/0.99  --splitting_mode                        input
% 4.03/0.99  --splitting_grd                         true
% 4.03/0.99  --splitting_cvd                         false
% 4.03/0.99  --splitting_cvd_svl                     false
% 4.03/0.99  --splitting_nvd                         32
% 4.03/0.99  --sub_typing                            true
% 4.03/0.99  --prep_gs_sim                           true
% 4.03/0.99  --prep_unflatten                        true
% 4.03/0.99  --prep_res_sim                          true
% 4.03/0.99  --prep_upred                            true
% 4.03/0.99  --prep_sem_filter                       exhaustive
% 4.03/0.99  --prep_sem_filter_out                   false
% 4.03/0.99  --pred_elim                             true
% 4.03/0.99  --res_sim_input                         true
% 4.03/0.99  --eq_ax_congr_red                       true
% 4.03/0.99  --pure_diseq_elim                       true
% 4.03/0.99  --brand_transform                       false
% 4.03/0.99  --non_eq_to_eq                          false
% 4.03/0.99  --prep_def_merge                        true
% 4.03/0.99  --prep_def_merge_prop_impl              false
% 4.03/0.99  --prep_def_merge_mbd                    true
% 4.03/0.99  --prep_def_merge_tr_red                 false
% 4.03/0.99  --prep_def_merge_tr_cl                  false
% 4.03/0.99  --smt_preprocessing                     true
% 4.03/0.99  --smt_ac_axioms                         fast
% 4.03/0.99  --preprocessed_out                      false
% 4.03/0.99  --preprocessed_stats                    false
% 4.03/0.99  
% 4.03/0.99  ------ Abstraction refinement Options
% 4.03/0.99  
% 4.03/0.99  --abstr_ref                             []
% 4.03/0.99  --abstr_ref_prep                        false
% 4.03/0.99  --abstr_ref_until_sat                   false
% 4.03/0.99  --abstr_ref_sig_restrict                funpre
% 4.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.03/0.99  --abstr_ref_under                       []
% 4.03/0.99  
% 4.03/0.99  ------ SAT Options
% 4.03/0.99  
% 4.03/0.99  --sat_mode                              false
% 4.03/0.99  --sat_fm_restart_options                ""
% 4.03/0.99  --sat_gr_def                            false
% 4.03/0.99  --sat_epr_types                         true
% 4.03/0.99  --sat_non_cyclic_types                  false
% 4.03/0.99  --sat_finite_models                     false
% 4.03/0.99  --sat_fm_lemmas                         false
% 4.03/0.99  --sat_fm_prep                           false
% 4.03/0.99  --sat_fm_uc_incr                        true
% 4.03/0.99  --sat_out_model                         small
% 4.03/0.99  --sat_out_clauses                       false
% 4.03/0.99  
% 4.03/0.99  ------ QBF Options
% 4.03/0.99  
% 4.03/0.99  --qbf_mode                              false
% 4.03/0.99  --qbf_elim_univ                         false
% 4.03/0.99  --qbf_dom_inst                          none
% 4.03/0.99  --qbf_dom_pre_inst                      false
% 4.03/0.99  --qbf_sk_in                             false
% 4.03/0.99  --qbf_pred_elim                         true
% 4.03/0.99  --qbf_split                             512
% 4.03/0.99  
% 4.03/0.99  ------ BMC1 Options
% 4.03/0.99  
% 4.03/0.99  --bmc1_incremental                      false
% 4.03/0.99  --bmc1_axioms                           reachable_all
% 4.03/0.99  --bmc1_min_bound                        0
% 4.03/0.99  --bmc1_max_bound                        -1
% 4.03/0.99  --bmc1_max_bound_default                -1
% 4.03/0.99  --bmc1_symbol_reachability              true
% 4.03/0.99  --bmc1_property_lemmas                  false
% 4.03/0.99  --bmc1_k_induction                      false
% 4.03/0.99  --bmc1_non_equiv_states                 false
% 4.03/0.99  --bmc1_deadlock                         false
% 4.03/0.99  --bmc1_ucm                              false
% 4.03/0.99  --bmc1_add_unsat_core                   none
% 4.03/0.99  --bmc1_unsat_core_children              false
% 4.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.03/0.99  --bmc1_out_stat                         full
% 4.03/0.99  --bmc1_ground_init                      false
% 4.03/0.99  --bmc1_pre_inst_next_state              false
% 4.03/0.99  --bmc1_pre_inst_state                   false
% 4.03/0.99  --bmc1_pre_inst_reach_state             false
% 4.03/0.99  --bmc1_out_unsat_core                   false
% 4.03/0.99  --bmc1_aig_witness_out                  false
% 4.03/0.99  --bmc1_verbose                          false
% 4.03/0.99  --bmc1_dump_clauses_tptp                false
% 4.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.03/0.99  --bmc1_dump_file                        -
% 4.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.03/0.99  --bmc1_ucm_extend_mode                  1
% 4.03/0.99  --bmc1_ucm_init_mode                    2
% 4.03/0.99  --bmc1_ucm_cone_mode                    none
% 4.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.03/0.99  --bmc1_ucm_relax_model                  4
% 4.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.03/0.99  --bmc1_ucm_layered_model                none
% 4.03/0.99  --bmc1_ucm_max_lemma_size               10
% 4.03/0.99  
% 4.03/0.99  ------ AIG Options
% 4.03/0.99  
% 4.03/0.99  --aig_mode                              false
% 4.03/0.99  
% 4.03/0.99  ------ Instantiation Options
% 4.03/0.99  
% 4.03/0.99  --instantiation_flag                    true
% 4.03/0.99  --inst_sos_flag                         true
% 4.03/0.99  --inst_sos_phase                        true
% 4.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.03/0.99  --inst_lit_sel_side                     num_symb
% 4.03/0.99  --inst_solver_per_active                1400
% 4.03/0.99  --inst_solver_calls_frac                1.
% 4.03/0.99  --inst_passive_queue_type               priority_queues
% 4.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.03/0.99  --inst_passive_queues_freq              [25;2]
% 4.03/0.99  --inst_dismatching                      true
% 4.03/0.99  --inst_eager_unprocessed_to_passive     true
% 4.03/0.99  --inst_prop_sim_given                   true
% 4.03/0.99  --inst_prop_sim_new                     false
% 4.03/0.99  --inst_subs_new                         false
% 4.03/0.99  --inst_eq_res_simp                      false
% 4.03/0.99  --inst_subs_given                       false
% 4.03/0.99  --inst_orphan_elimination               true
% 4.03/0.99  --inst_learning_loop_flag               true
% 4.03/0.99  --inst_learning_start                   3000
% 4.03/0.99  --inst_learning_factor                  2
% 4.03/0.99  --inst_start_prop_sim_after_learn       3
% 4.03/0.99  --inst_sel_renew                        solver
% 4.03/0.99  --inst_lit_activity_flag                true
% 4.03/0.99  --inst_restr_to_given                   false
% 4.03/0.99  --inst_activity_threshold               500
% 4.03/0.99  --inst_out_proof                        true
% 4.03/0.99  
% 4.03/0.99  ------ Resolution Options
% 4.03/0.99  
% 4.03/0.99  --resolution_flag                       true
% 4.03/0.99  --res_lit_sel                           adaptive
% 4.03/0.99  --res_lit_sel_side                      none
% 4.03/0.99  --res_ordering                          kbo
% 4.03/0.99  --res_to_prop_solver                    active
% 4.03/0.99  --res_prop_simpl_new                    false
% 4.03/0.99  --res_prop_simpl_given                  true
% 4.03/0.99  --res_passive_queue_type                priority_queues
% 4.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.03/0.99  --res_passive_queues_freq               [15;5]
% 4.03/0.99  --res_forward_subs                      full
% 4.03/0.99  --res_backward_subs                     full
% 4.03/0.99  --res_forward_subs_resolution           true
% 4.03/0.99  --res_backward_subs_resolution          true
% 4.03/0.99  --res_orphan_elimination                true
% 4.03/0.99  --res_time_limit                        2.
% 4.03/0.99  --res_out_proof                         true
% 4.03/0.99  
% 4.03/0.99  ------ Superposition Options
% 4.03/0.99  
% 4.03/0.99  --superposition_flag                    true
% 4.03/0.99  --sup_passive_queue_type                priority_queues
% 4.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.03/0.99  --demod_completeness_check              fast
% 4.03/0.99  --demod_use_ground                      true
% 4.03/0.99  --sup_to_prop_solver                    passive
% 4.03/0.99  --sup_prop_simpl_new                    true
% 4.03/0.99  --sup_prop_simpl_given                  true
% 4.03/0.99  --sup_fun_splitting                     true
% 4.03/0.99  --sup_smt_interval                      50000
% 4.03/0.99  
% 4.03/0.99  ------ Superposition Simplification Setup
% 4.03/0.99  
% 4.03/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.03/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.03/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.03/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.03/0.99  --sup_immed_triv                        [TrivRules]
% 4.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.03/0.99  --sup_immed_bw_main                     []
% 4.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.03/0.99  --sup_input_bw                          []
% 4.03/0.99  
% 4.03/0.99  ------ Combination Options
% 4.03/0.99  
% 4.03/0.99  --comb_res_mult                         3
% 4.03/0.99  --comb_sup_mult                         2
% 4.03/0.99  --comb_inst_mult                        10
% 4.03/0.99  
% 4.03/0.99  ------ Debug Options
% 4.03/0.99  
% 4.03/0.99  --dbg_backtrace                         false
% 4.03/0.99  --dbg_dump_prop_clauses                 false
% 4.03/0.99  --dbg_dump_prop_clauses_file            -
% 4.03/0.99  --dbg_out_stat                          false
% 4.03/0.99  ------ Parsing...
% 4.03/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.03/0.99  
% 4.03/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 4.03/0.99  
% 4.03/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.03/0.99  
% 4.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.03/0.99  ------ Proving...
% 4.03/0.99  ------ Problem Properties 
% 4.03/0.99  
% 4.03/0.99  
% 4.03/0.99  clauses                                 21
% 4.03/0.99  conjectures                             2
% 4.03/0.99  EPR                                     4
% 4.03/0.99  Horn                                    20
% 4.03/0.99  unary                                   6
% 4.03/0.99  binary                                  11
% 4.03/0.99  lits                                    43
% 4.03/0.99  lits eq                                 14
% 4.03/0.99  fd_pure                                 0
% 4.03/0.99  fd_pseudo                               0
% 4.03/0.99  fd_cond                                 1
% 4.03/0.99  fd_pseudo_cond                          1
% 4.03/0.99  AC symbols                              0
% 4.03/0.99  
% 4.03/0.99  ------ Schedule dynamic 5 is on 
% 4.03/0.99  
% 4.03/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.03/0.99  
% 4.03/0.99  
% 4.03/0.99  ------ 
% 4.03/0.99  Current options:
% 4.03/0.99  ------ 
% 4.03/0.99  
% 4.03/0.99  ------ Input Options
% 4.03/0.99  
% 4.03/0.99  --out_options                           all
% 4.03/0.99  --tptp_safe_out                         true
% 4.03/0.99  --problem_path                          ""
% 4.03/0.99  --include_path                          ""
% 4.03/0.99  --clausifier                            res/vclausify_rel
% 4.03/0.99  --clausifier_options                    ""
% 4.03/0.99  --stdin                                 false
% 4.03/0.99  --stats_out                             all
% 4.03/0.99  
% 4.03/0.99  ------ General Options
% 4.03/0.99  
% 4.03/0.99  --fof                                   false
% 4.03/0.99  --time_out_real                         305.
% 4.03/0.99  --time_out_virtual                      -1.
% 4.03/0.99  --symbol_type_check                     false
% 4.03/0.99  --clausify_out                          false
% 4.03/0.99  --sig_cnt_out                           false
% 4.03/0.99  --trig_cnt_out                          false
% 4.03/0.99  --trig_cnt_out_tolerance                1.
% 4.03/0.99  --trig_cnt_out_sk_spl                   false
% 4.03/0.99  --abstr_cl_out                          false
% 4.03/0.99  
% 4.03/0.99  ------ Global Options
% 4.03/0.99  
% 4.03/0.99  --schedule                              default
% 4.03/0.99  --add_important_lit                     false
% 4.03/0.99  --prop_solver_per_cl                    1000
% 4.03/0.99  --min_unsat_core                        false
% 4.03/0.99  --soft_assumptions                      false
% 4.03/0.99  --soft_lemma_size                       3
% 4.03/0.99  --prop_impl_unit_size                   0
% 4.03/0.99  --prop_impl_unit                        []
% 4.03/0.99  --share_sel_clauses                     true
% 4.03/0.99  --reset_solvers                         false
% 4.03/0.99  --bc_imp_inh                            [conj_cone]
% 4.03/0.99  --conj_cone_tolerance                   3.
% 4.03/0.99  --extra_neg_conj                        none
% 4.03/0.99  --large_theory_mode                     true
% 4.03/0.99  --prolific_symb_bound                   200
% 4.03/0.99  --lt_threshold                          2000
% 4.03/0.99  --clause_weak_htbl                      true
% 4.03/0.99  --gc_record_bc_elim                     false
% 4.03/0.99  
% 4.03/0.99  ------ Preprocessing Options
% 4.03/0.99  
% 4.03/0.99  --preprocessing_flag                    true
% 4.03/0.99  --time_out_prep_mult                    0.1
% 4.03/0.99  --splitting_mode                        input
% 4.03/0.99  --splitting_grd                         true
% 4.03/0.99  --splitting_cvd                         false
% 4.03/0.99  --splitting_cvd_svl                     false
% 4.03/0.99  --splitting_nvd                         32
% 4.03/0.99  --sub_typing                            true
% 4.03/0.99  --prep_gs_sim                           true
% 4.03/0.99  --prep_unflatten                        true
% 4.03/0.99  --prep_res_sim                          true
% 4.03/0.99  --prep_upred                            true
% 4.03/0.99  --prep_sem_filter                       exhaustive
% 4.03/0.99  --prep_sem_filter_out                   false
% 4.03/0.99  --pred_elim                             true
% 4.03/0.99  --res_sim_input                         true
% 4.03/0.99  --eq_ax_congr_red                       true
% 4.03/0.99  --pure_diseq_elim                       true
% 4.03/0.99  --brand_transform                       false
% 4.03/0.99  --non_eq_to_eq                          false
% 4.03/0.99  --prep_def_merge                        true
% 4.03/0.99  --prep_def_merge_prop_impl              false
% 4.03/0.99  --prep_def_merge_mbd                    true
% 4.03/0.99  --prep_def_merge_tr_red                 false
% 4.03/0.99  --prep_def_merge_tr_cl                  false
% 4.03/0.99  --smt_preprocessing                     true
% 4.03/0.99  --smt_ac_axioms                         fast
% 4.03/0.99  --preprocessed_out                      false
% 4.03/0.99  --preprocessed_stats                    false
% 4.03/0.99  
% 4.03/0.99  ------ Abstraction refinement Options
% 4.03/0.99  
% 4.03/0.99  --abstr_ref                             []
% 4.03/0.99  --abstr_ref_prep                        false
% 4.03/0.99  --abstr_ref_until_sat                   false
% 4.03/0.99  --abstr_ref_sig_restrict                funpre
% 4.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.03/0.99  --abstr_ref_under                       []
% 4.03/0.99  
% 4.03/0.99  ------ SAT Options
% 4.03/0.99  
% 4.03/0.99  --sat_mode                              false
% 4.03/0.99  --sat_fm_restart_options                ""
% 4.03/0.99  --sat_gr_def                            false
% 4.03/0.99  --sat_epr_types                         true
% 4.03/0.99  --sat_non_cyclic_types                  false
% 4.03/0.99  --sat_finite_models                     false
% 4.03/0.99  --sat_fm_lemmas                         false
% 4.03/0.99  --sat_fm_prep                           false
% 4.03/0.99  --sat_fm_uc_incr                        true
% 4.03/0.99  --sat_out_model                         small
% 4.03/0.99  --sat_out_clauses                       false
% 4.03/0.99  
% 4.03/0.99  ------ QBF Options
% 4.03/0.99  
% 4.03/0.99  --qbf_mode                              false
% 4.03/0.99  --qbf_elim_univ                         false
% 4.03/0.99  --qbf_dom_inst                          none
% 4.03/0.99  --qbf_dom_pre_inst                      false
% 4.03/0.99  --qbf_sk_in                             false
% 4.03/0.99  --qbf_pred_elim                         true
% 4.03/0.99  --qbf_split                             512
% 4.03/0.99  
% 4.03/0.99  ------ BMC1 Options
% 4.03/0.99  
% 4.03/0.99  --bmc1_incremental                      false
% 4.03/0.99  --bmc1_axioms                           reachable_all
% 4.03/0.99  --bmc1_min_bound                        0
% 4.03/0.99  --bmc1_max_bound                        -1
% 4.03/0.99  --bmc1_max_bound_default                -1
% 4.03/0.99  --bmc1_symbol_reachability              true
% 4.03/0.99  --bmc1_property_lemmas                  false
% 4.03/0.99  --bmc1_k_induction                      false
% 4.03/0.99  --bmc1_non_equiv_states                 false
% 4.03/0.99  --bmc1_deadlock                         false
% 4.03/0.99  --bmc1_ucm                              false
% 4.03/0.99  --bmc1_add_unsat_core                   none
% 4.03/0.99  --bmc1_unsat_core_children              false
% 4.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.03/0.99  --bmc1_out_stat                         full
% 4.03/0.99  --bmc1_ground_init                      false
% 4.03/0.99  --bmc1_pre_inst_next_state              false
% 4.03/0.99  --bmc1_pre_inst_state                   false
% 4.03/0.99  --bmc1_pre_inst_reach_state             false
% 4.03/0.99  --bmc1_out_unsat_core                   false
% 4.03/0.99  --bmc1_aig_witness_out                  false
% 4.03/0.99  --bmc1_verbose                          false
% 4.03/0.99  --bmc1_dump_clauses_tptp                false
% 4.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.03/0.99  --bmc1_dump_file                        -
% 4.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.03/0.99  --bmc1_ucm_extend_mode                  1
% 4.03/0.99  --bmc1_ucm_init_mode                    2
% 4.03/0.99  --bmc1_ucm_cone_mode                    none
% 4.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.03/0.99  --bmc1_ucm_relax_model                  4
% 4.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.03/0.99  --bmc1_ucm_layered_model                none
% 4.03/0.99  --bmc1_ucm_max_lemma_size               10
% 4.03/0.99  
% 4.03/0.99  ------ AIG Options
% 4.03/0.99  
% 4.03/0.99  --aig_mode                              false
% 4.03/0.99  
% 4.03/0.99  ------ Instantiation Options
% 4.03/0.99  
% 4.03/0.99  --instantiation_flag                    true
% 4.03/0.99  --inst_sos_flag                         true
% 4.03/0.99  --inst_sos_phase                        true
% 4.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.03/0.99  --inst_lit_sel_side                     none
% 4.03/0.99  --inst_solver_per_active                1400
% 4.03/0.99  --inst_solver_calls_frac                1.
% 4.03/0.99  --inst_passive_queue_type               priority_queues
% 4.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.03/0.99  --inst_passive_queues_freq              [25;2]
% 4.03/0.99  --inst_dismatching                      true
% 4.03/0.99  --inst_eager_unprocessed_to_passive     true
% 4.03/0.99  --inst_prop_sim_given                   true
% 4.03/0.99  --inst_prop_sim_new                     false
% 4.03/0.99  --inst_subs_new                         false
% 4.03/0.99  --inst_eq_res_simp                      false
% 4.03/0.99  --inst_subs_given                       false
% 4.03/0.99  --inst_orphan_elimination               true
% 4.03/0.99  --inst_learning_loop_flag               true
% 4.03/0.99  --inst_learning_start                   3000
% 4.03/0.99  --inst_learning_factor                  2
% 4.03/0.99  --inst_start_prop_sim_after_learn       3
% 4.03/0.99  --inst_sel_renew                        solver
% 4.03/0.99  --inst_lit_activity_flag                true
% 4.03/0.99  --inst_restr_to_given                   false
% 4.03/0.99  --inst_activity_threshold               500
% 4.03/0.99  --inst_out_proof                        true
% 4.03/0.99  
% 4.03/0.99  ------ Resolution Options
% 4.03/0.99  
% 4.03/0.99  --resolution_flag                       false
% 4.03/0.99  --res_lit_sel                           adaptive
% 4.03/0.99  --res_lit_sel_side                      none
% 4.03/0.99  --res_ordering                          kbo
% 4.03/0.99  --res_to_prop_solver                    active
% 4.03/0.99  --res_prop_simpl_new                    false
% 4.03/0.99  --res_prop_simpl_given                  true
% 4.03/0.99  --res_passive_queue_type                priority_queues
% 4.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.03/0.99  --res_passive_queues_freq               [15;5]
% 4.03/0.99  --res_forward_subs                      full
% 4.03/0.99  --res_backward_subs                     full
% 4.03/0.99  --res_forward_subs_resolution           true
% 4.03/0.99  --res_backward_subs_resolution          true
% 4.03/0.99  --res_orphan_elimination                true
% 4.03/0.99  --res_time_limit                        2.
% 4.03/0.99  --res_out_proof                         true
% 4.03/0.99  
% 4.03/0.99  ------ Superposition Options
% 4.03/0.99  
% 4.03/0.99  --superposition_flag                    true
% 4.03/0.99  --sup_passive_queue_type                priority_queues
% 4.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.03/0.99  --demod_completeness_check              fast
% 4.03/0.99  --demod_use_ground                      true
% 4.03/0.99  --sup_to_prop_solver                    passive
% 4.03/0.99  --sup_prop_simpl_new                    true
% 4.03/0.99  --sup_prop_simpl_given                  true
% 4.03/0.99  --sup_fun_splitting                     true
% 4.03/0.99  --sup_smt_interval                      50000
% 4.03/0.99  
% 4.03/0.99  ------ Superposition Simplification Setup
% 4.03/0.99  
% 4.03/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.03/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.03/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.03/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.03/0.99  --sup_immed_triv                        [TrivRules]
% 4.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.03/0.99  --sup_immed_bw_main                     []
% 4.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.03/0.99  --sup_input_bw                          []
% 4.03/0.99  
% 4.03/0.99  ------ Combination Options
% 4.03/0.99  
% 4.03/0.99  --comb_res_mult                         3
% 4.03/0.99  --comb_sup_mult                         2
% 4.03/0.99  --comb_inst_mult                        10
% 4.03/0.99  
% 4.03/0.99  ------ Debug Options
% 4.03/0.99  
% 4.03/0.99  --dbg_backtrace                         false
% 4.03/0.99  --dbg_dump_prop_clauses                 false
% 4.03/0.99  --dbg_dump_prop_clauses_file            -
% 4.03/0.99  --dbg_out_stat                          false
% 4.03/0.99  
% 4.03/0.99  
% 4.03/0.99  
% 4.03/0.99  
% 4.03/0.99  ------ Proving...
% 4.03/0.99  
% 4.03/0.99  
% 4.03/0.99  % SZS status Theorem for theBenchmark.p
% 4.03/0.99  
% 4.03/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.03/0.99  
% 4.03/0.99  fof(f4,axiom,(
% 4.03/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f43,plain,(
% 4.03/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.03/0.99    inference(cnf_transformation,[],[f4])).
% 4.03/0.99  
% 4.03/0.99  fof(f7,axiom,(
% 4.03/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f33,plain,(
% 4.03/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.03/0.99    inference(nnf_transformation,[],[f7])).
% 4.03/0.99  
% 4.03/0.99  fof(f50,plain,(
% 4.03/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.03/0.99    inference(cnf_transformation,[],[f33])).
% 4.03/0.99  
% 4.03/0.99  fof(f12,axiom,(
% 4.03/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f24,plain,(
% 4.03/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.03/0.99    inference(ennf_transformation,[],[f12])).
% 4.03/0.99  
% 4.03/0.99  fof(f56,plain,(
% 4.03/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.03/0.99    inference(cnf_transformation,[],[f24])).
% 4.03/0.99  
% 4.03/0.99  fof(f11,axiom,(
% 4.03/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f16,plain,(
% 4.03/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 4.03/0.99    inference(pure_predicate_removal,[],[f11])).
% 4.03/0.99  
% 4.03/0.99  fof(f23,plain,(
% 4.03/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.03/0.99    inference(ennf_transformation,[],[f16])).
% 4.03/0.99  
% 4.03/0.99  fof(f55,plain,(
% 4.03/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.03/0.99    inference(cnf_transformation,[],[f23])).
% 4.03/0.99  
% 4.03/0.99  fof(f8,axiom,(
% 4.03/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f20,plain,(
% 4.03/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.03/0.99    inference(ennf_transformation,[],[f8])).
% 4.03/0.99  
% 4.03/0.99  fof(f34,plain,(
% 4.03/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.03/0.99    inference(nnf_transformation,[],[f20])).
% 4.03/0.99  
% 4.03/0.99  fof(f51,plain,(
% 4.03/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.03/0.99    inference(cnf_transformation,[],[f34])).
% 4.03/0.99  
% 4.03/0.99  fof(f10,axiom,(
% 4.03/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f22,plain,(
% 4.03/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.03/0.99    inference(ennf_transformation,[],[f10])).
% 4.03/0.99  
% 4.03/0.99  fof(f54,plain,(
% 4.03/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.03/0.99    inference(cnf_transformation,[],[f22])).
% 4.03/0.99  
% 4.03/0.99  fof(f1,axiom,(
% 4.03/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f29,plain,(
% 4.03/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.03/0.99    inference(nnf_transformation,[],[f1])).
% 4.03/0.99  
% 4.03/0.99  fof(f30,plain,(
% 4.03/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.03/0.99    inference(flattening,[],[f29])).
% 4.03/0.99  
% 4.03/0.99  fof(f40,plain,(
% 4.03/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.03/0.99    inference(cnf_transformation,[],[f30])).
% 4.03/0.99  
% 4.03/0.99  fof(f14,conjecture,(
% 4.03/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f15,negated_conjecture,(
% 4.03/0.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 4.03/0.99    inference(negated_conjecture,[],[f14])).
% 4.03/0.99  
% 4.03/0.99  fof(f27,plain,(
% 4.03/0.99    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 4.03/0.99    inference(ennf_transformation,[],[f15])).
% 4.03/0.99  
% 4.03/0.99  fof(f28,plain,(
% 4.03/0.99    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.03/0.99    inference(flattening,[],[f27])).
% 4.03/0.99  
% 4.03/0.99  fof(f36,plain,(
% 4.03/0.99    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 4.03/0.99    introduced(choice_axiom,[])).
% 4.03/0.99  
% 4.03/0.99  fof(f37,plain,(
% 4.03/0.99    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 4.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f36])).
% 4.03/0.99  
% 4.03/0.99  fof(f65,plain,(
% 4.03/0.99    r1_tarski(k2_relat_1(sK1),sK0)),
% 4.03/0.99    inference(cnf_transformation,[],[f37])).
% 4.03/0.99  
% 4.03/0.99  fof(f6,axiom,(
% 4.03/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f19,plain,(
% 4.03/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 4.03/0.99    inference(ennf_transformation,[],[f6])).
% 4.03/0.99  
% 4.03/0.99  fof(f48,plain,(
% 4.03/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 4.03/0.99    inference(cnf_transformation,[],[f19])).
% 4.03/0.99  
% 4.03/0.99  fof(f3,axiom,(
% 4.03/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f18,plain,(
% 4.03/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.03/0.99    inference(ennf_transformation,[],[f3])).
% 4.03/0.99  
% 4.03/0.99  fof(f42,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 4.03/0.99    inference(cnf_transformation,[],[f18])).
% 4.03/0.99  
% 4.03/0.99  fof(f63,plain,(
% 4.03/0.99    v1_relat_1(sK1)),
% 4.03/0.99    inference(cnf_transformation,[],[f37])).
% 4.03/0.99  
% 4.03/0.99  fof(f9,axiom,(
% 4.03/0.99    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f21,plain,(
% 4.03/0.99    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 4.03/0.99    inference(ennf_transformation,[],[f9])).
% 4.03/0.99  
% 4.03/0.99  fof(f53,plain,(
% 4.03/0.99    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 4.03/0.99    inference(cnf_transformation,[],[f21])).
% 4.03/0.99  
% 4.03/0.99  fof(f38,plain,(
% 4.03/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.03/0.99    inference(cnf_transformation,[],[f30])).
% 4.03/0.99  
% 4.03/0.99  fof(f68,plain,(
% 4.03/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.03/0.99    inference(equality_resolution,[],[f38])).
% 4.03/0.99  
% 4.03/0.99  fof(f2,axiom,(
% 4.03/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f17,plain,(
% 4.03/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 4.03/0.99    inference(ennf_transformation,[],[f2])).
% 4.03/0.99  
% 4.03/0.99  fof(f41,plain,(
% 4.03/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 4.03/0.99    inference(cnf_transformation,[],[f17])).
% 4.03/0.99  
% 4.03/0.99  fof(f13,axiom,(
% 4.03/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f25,plain,(
% 4.03/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.03/0.99    inference(ennf_transformation,[],[f13])).
% 4.03/0.99  
% 4.03/0.99  fof(f26,plain,(
% 4.03/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.03/0.99    inference(flattening,[],[f25])).
% 4.03/0.99  
% 4.03/0.99  fof(f35,plain,(
% 4.03/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.03/0.99    inference(nnf_transformation,[],[f26])).
% 4.03/0.99  
% 4.03/0.99  fof(f59,plain,(
% 4.03/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.03/0.99    inference(cnf_transformation,[],[f35])).
% 4.03/0.99  
% 4.03/0.99  fof(f66,plain,(
% 4.03/0.99    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 4.03/0.99    inference(cnf_transformation,[],[f37])).
% 4.03/0.99  
% 4.03/0.99  fof(f64,plain,(
% 4.03/0.99    v1_funct_1(sK1)),
% 4.03/0.99    inference(cnf_transformation,[],[f37])).
% 4.03/0.99  
% 4.03/0.99  fof(f5,axiom,(
% 4.03/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.03/0.99  
% 4.03/0.99  fof(f31,plain,(
% 4.03/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.03/0.99    inference(nnf_transformation,[],[f5])).
% 4.03/0.99  
% 4.03/0.99  fof(f32,plain,(
% 4.03/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.03/0.99    inference(flattening,[],[f31])).
% 4.03/0.99  
% 4.03/0.99  fof(f46,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 4.03/0.99    inference(cnf_transformation,[],[f32])).
% 4.03/0.99  
% 4.03/0.99  fof(f69,plain,(
% 4.03/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 4.03/0.99    inference(equality_resolution,[],[f46])).
% 4.03/0.99  
% 4.03/0.99  fof(f60,plain,(
% 4.03/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.03/0.99    inference(cnf_transformation,[],[f35])).
% 4.03/0.99  
% 4.03/0.99  fof(f74,plain,(
% 4.03/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 4.03/0.99    inference(equality_resolution,[],[f60])).
% 4.03/0.99  
% 4.03/0.99  fof(f45,plain,(
% 4.03/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 4.03/0.99    inference(cnf_transformation,[],[f32])).
% 4.03/0.99  
% 4.03/0.99  fof(f70,plain,(
% 4.03/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 4.03/0.99    inference(equality_resolution,[],[f45])).
% 4.03/0.99  
% 4.03/0.99  cnf(c_5,plain,
% 4.03/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 4.03/0.99      inference(cnf_transformation,[],[f43]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1320,plain,
% 4.03/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_11,plain,
% 4.03/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.03/0.99      inference(cnf_transformation,[],[f50]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1317,plain,
% 4.03/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 4.03/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_18,plain,
% 4.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.03/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.03/0.99      inference(cnf_transformation,[],[f56]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1313,plain,
% 4.03/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.03/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_3432,plain,
% 4.03/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.03/0.99      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_1317,c_1313]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_14696,plain,
% 4.03/0.99      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_1320,c_3432]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_17,plain,
% 4.03/0.99      ( v4_relat_1(X0,X1)
% 4.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 4.03/0.99      inference(cnf_transformation,[],[f55]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_14,plain,
% 4.03/0.99      ( ~ v4_relat_1(X0,X1)
% 4.03/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 4.03/0.99      | ~ v1_relat_1(X0) ),
% 4.03/0.99      inference(cnf_transformation,[],[f51]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_349,plain,
% 4.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.03/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 4.03/0.99      | ~ v1_relat_1(X0) ),
% 4.03/0.99      inference(resolution,[status(thm)],[c_17,c_14]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_16,plain,
% 4.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.03/0.99      | v1_relat_1(X0) ),
% 4.03/0.99      inference(cnf_transformation,[],[f54]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_353,plain,
% 4.03/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 4.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 4.03/0.99      inference(global_propositional_subsumption,
% 4.03/0.99                [status(thm)],
% 4.03/0.99                [c_349,c_16]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_354,plain,
% 4.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.03/0.99      | r1_tarski(k1_relat_1(X0),X1) ),
% 4.03/0.99      inference(renaming,[status(thm)],[c_353]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1310,plain,
% 4.03/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.03/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_2452,plain,
% 4.03/0.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 4.03/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_1317,c_1310]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_6055,plain,
% 4.03/0.99      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_1320,c_2452]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_0,plain,
% 4.03/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.03/0.99      inference(cnf_transformation,[],[f40]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1324,plain,
% 4.03/0.99      ( X0 = X1
% 4.03/0.99      | r1_tarski(X0,X1) != iProver_top
% 4.03/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_4000,plain,
% 4.03/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_1320,c_1324]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_6231,plain,
% 4.03/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_6055,c_4000]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_14705,plain,
% 4.03/0.99      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 4.03/0.99      inference(light_normalisation,[status(thm)],[c_14696,c_6231]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_14719,plain,
% 4.03/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 4.03/0.99      inference(instantiation,[status(thm)],[c_14705]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_26,negated_conjecture,
% 4.03/0.99      ( r1_tarski(k2_relat_1(sK1),sK0) ),
% 4.03/0.99      inference(cnf_transformation,[],[f65]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1312,plain,
% 4.03/0.99      ( r1_tarski(k2_relat_1(sK1),sK0) = iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_9,plain,
% 4.03/0.99      ( ~ r1_tarski(X0,X1)
% 4.03/0.99      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
% 4.03/0.99      inference(cnf_transformation,[],[f48]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1319,plain,
% 4.03/0.99      ( r1_tarski(X0,X1) != iProver_top
% 4.03/0.99      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_4,plain,
% 4.03/0.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 4.03/0.99      inference(cnf_transformation,[],[f42]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1321,plain,
% 4.03/0.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_3172,plain,
% 4.03/0.99      ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,X2)
% 4.03/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_1319,c_1321]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_12386,plain,
% 4.03/0.99      ( k2_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK1)),k2_zfmisc_1(X0,sK0)) = k2_zfmisc_1(X0,sK0) ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_1312,c_3172]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_28,negated_conjecture,
% 4.03/0.99      ( v1_relat_1(sK1) ),
% 4.03/0.99      inference(cnf_transformation,[],[f63]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1311,plain,
% 4.03/0.99      ( v1_relat_1(sK1) = iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_15,plain,
% 4.03/0.99      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 4.03/0.99      | ~ v1_relat_1(X0) ),
% 4.03/0.99      inference(cnf_transformation,[],[f53]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1315,plain,
% 4.03/0.99      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 4.03/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_2578,plain,
% 4.03/0.99      ( k2_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))
% 4.03/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_1315,c_1321]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_8753,plain,
% 4.03/0.99      ( k2_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) = k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)) ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_1311,c_2578]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_2,plain,
% 4.03/0.99      ( r1_tarski(X0,X0) ),
% 4.03/0.99      inference(cnf_transformation,[],[f68]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1323,plain,
% 4.03/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_3,plain,
% 4.03/0.99      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 4.03/0.99      inference(cnf_transformation,[],[f41]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1322,plain,
% 4.03/0.99      ( r1_tarski(X0,X1) = iProver_top
% 4.03/0.99      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_2462,plain,
% 4.03/0.99      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_1323,c_1322]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_3073,plain,
% 4.03/0.99      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_2462,c_1322]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_4160,plain,
% 4.03/0.99      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_3073,c_1322]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_9274,plain,
% 4.03/0.99      ( r1_tarski(sK1,k2_xboole_0(k2_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),X0),X1)) = iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_8753,c_4160]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_13003,plain,
% 4.03/0.99      ( r1_tarski(sK1,k2_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),sK0),X0)) = iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_12386,c_9274]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_9275,plain,
% 4.03/0.99      ( r1_tarski(sK1,k2_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),X0)) = iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_8753,c_3073]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_13004,plain,
% 4.03/0.99      ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) = iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_12386,c_9275]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_22,plain,
% 4.03/0.99      ( v1_funct_2(X0,X1,X2)
% 4.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.03/0.99      | k1_relset_1(X1,X2,X0) != X1
% 4.03/0.99      | k1_xboole_0 = X2 ),
% 4.03/0.99      inference(cnf_transformation,[],[f59]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_25,negated_conjecture,
% 4.03/0.99      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
% 4.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 4.03/0.99      | ~ v1_funct_1(sK1) ),
% 4.03/0.99      inference(cnf_transformation,[],[f66]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_27,negated_conjecture,
% 4.03/0.99      ( v1_funct_1(sK1) ),
% 4.03/0.99      inference(cnf_transformation,[],[f64]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_149,plain,
% 4.03/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 4.03/0.99      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
% 4.03/0.99      inference(global_propositional_subsumption,
% 4.03/0.99                [status(thm)],
% 4.03/0.99                [c_25,c_27]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_150,negated_conjecture,
% 4.03/0.99      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
% 4.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
% 4.03/0.99      inference(renaming,[status(thm)],[c_149]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_656,plain,
% 4.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 4.03/0.99      | k1_relset_1(X1,X2,X0) != X1
% 4.03/0.99      | k1_relat_1(sK1) != X1
% 4.03/0.99      | sK0 != X2
% 4.03/0.99      | sK1 != X0
% 4.03/0.99      | k1_xboole_0 = X2 ),
% 4.03/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_150]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_657,plain,
% 4.03/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 4.03/0.99      | k1_relset_1(k1_relat_1(sK1),sK0,sK1) != k1_relat_1(sK1)
% 4.03/0.99      | k1_xboole_0 = sK0 ),
% 4.03/0.99      inference(unflattening,[status(thm)],[c_656]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_665,plain,
% 4.03/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 4.03/0.99      | k1_xboole_0 = sK0 ),
% 4.03/0.99      inference(forward_subsumption_resolution,
% 4.03/0.99                [status(thm)],
% 4.03/0.99                [c_657,c_18]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1307,plain,
% 4.03/0.99      ( k1_xboole_0 = sK0
% 4.03/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_665]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_2131,plain,
% 4.03/0.99      ( sK0 = k1_xboole_0
% 4.03/0.99      | r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) != iProver_top ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_1317,c_1307]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_13254,plain,
% 4.03/0.99      ( sK0 = k1_xboole_0 ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_13004,c_2131]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_13459,plain,
% 4.03/0.99      ( r1_tarski(sK1,k2_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0),X0)) = iProver_top ),
% 4.03/0.99      inference(light_normalisation,[status(thm)],[c_13003,c_13254]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_6,plain,
% 4.03/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 4.03/0.99      inference(cnf_transformation,[],[f69]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1921,plain,
% 4.03/0.99      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_1320,c_1321]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_13460,plain,
% 4.03/0.99      ( r1_tarski(sK1,X0) = iProver_top ),
% 4.03/0.99      inference(demodulation,[status(thm)],[c_13459,c_6,c_1921]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_13476,plain,
% 4.03/0.99      ( sK1 = k1_xboole_0 ),
% 4.03/0.99      inference(superposition,[status(thm)],[c_13460,c_4000]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_21,plain,
% 4.03/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 4.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 4.03/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 4.03/0.99      inference(cnf_transformation,[],[f74]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_640,plain,
% 4.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 4.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 4.03/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 4.03/0.99      | k1_relat_1(sK1) != k1_xboole_0
% 4.03/0.99      | sK0 != X1
% 4.03/0.99      | sK1 != X0 ),
% 4.03/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_150]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_641,plain,
% 4.03/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
% 4.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 4.03/0.99      | k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 4.03/0.99      | k1_relat_1(sK1) != k1_xboole_0 ),
% 4.03/0.99      inference(unflattening,[status(thm)],[c_640]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1308,plain,
% 4.03/0.99      ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 4.03/0.99      | k1_relat_1(sK1) != k1_xboole_0
% 4.03/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
% 4.03/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_7,plain,
% 4.03/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.03/0.99      inference(cnf_transformation,[],[f70]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_1325,plain,
% 4.03/0.99      ( k1_relset_1(k1_xboole_0,sK0,sK1) != k1_xboole_0
% 4.03/0.99      | k1_relat_1(sK1) != k1_xboole_0
% 4.03/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) != iProver_top
% 4.03/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 4.03/0.99      inference(demodulation,[status(thm)],[c_1308,c_7]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_14533,plain,
% 4.03/0.99      ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0
% 4.03/0.99      | k1_relat_1(k1_xboole_0) != k1_xboole_0
% 4.03/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK0))) != iProver_top
% 4.03/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 4.03/0.99      inference(demodulation,[status(thm)],[c_13476,c_1325]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_14538,plain,
% 4.03/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 4.03/0.99      | k1_xboole_0 != k1_xboole_0
% 4.03/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 4.03/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 4.03/0.99      inference(light_normalisation,
% 4.03/0.99                [status(thm)],
% 4.03/0.99                [c_14533,c_6231,c_13254]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_14539,plain,
% 4.03/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 4.03/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 4.03/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 4.03/0.99      inference(equality_resolution_simp,[status(thm)],[c_14538]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_14540,plain,
% 4.03/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 4.03/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 4.03/0.99      inference(demodulation,[status(thm)],[c_14539,c_7]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_81,plain,
% 4.03/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_83,plain,
% 4.03/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 4.03/0.99      inference(instantiation,[status(thm)],[c_81]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_72,plain,
% 4.03/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 4.03/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 4.03/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(c_74,plain,
% 4.03/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 4.03/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 4.03/0.99      inference(instantiation,[status(thm)],[c_72]) ).
% 4.03/0.99  
% 4.03/0.99  cnf(contradiction,plain,
% 4.03/0.99      ( $false ),
% 4.03/0.99      inference(minisat,[status(thm)],[c_14719,c_14540,c_83,c_74]) ).
% 4.03/0.99  
% 4.03/0.99  
% 4.03/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.03/0.99  
% 4.03/0.99  ------                               Statistics
% 4.03/0.99  
% 4.03/0.99  ------ General
% 4.03/0.99  
% 4.03/0.99  abstr_ref_over_cycles:                  0
% 4.03/0.99  abstr_ref_under_cycles:                 0
% 4.03/0.99  gc_basic_clause_elim:                   0
% 4.03/0.99  forced_gc_time:                         0
% 4.03/0.99  parsing_time:                           0.01
% 4.03/0.99  unif_index_cands_time:                  0.
% 4.03/0.99  unif_index_add_time:                    0.
% 4.03/0.99  orderings_time:                         0.
% 4.03/0.99  out_proof_time:                         0.009
% 4.03/0.99  total_time:                             0.397
% 4.03/0.99  num_of_symbols:                         46
% 4.03/0.99  num_of_terms:                           13755
% 4.03/0.99  
% 4.03/0.99  ------ Preprocessing
% 4.03/0.99  
% 4.03/0.99  num_of_splits:                          0
% 4.03/0.99  num_of_split_atoms:                     0
% 4.03/0.99  num_of_reused_defs:                     0
% 4.03/0.99  num_eq_ax_congr_red:                    10
% 4.03/0.99  num_of_sem_filtered_clauses:            2
% 4.03/0.99  num_of_subtypes:                        0
% 4.03/0.99  monotx_restored_types:                  0
% 4.03/0.99  sat_num_of_epr_types:                   0
% 4.03/0.99  sat_num_of_non_cyclic_types:            0
% 4.03/0.99  sat_guarded_non_collapsed_types:        0
% 4.03/0.99  num_pure_diseq_elim:                    0
% 4.03/0.99  simp_replaced_by:                       0
% 4.03/0.99  res_preprocessed:                       112
% 4.03/0.99  prep_upred:                             0
% 4.03/0.99  prep_unflattend:                        38
% 4.03/0.99  smt_new_axioms:                         0
% 4.03/0.99  pred_elim_cands:                        3
% 4.03/0.99  pred_elim:                              2
% 4.03/0.99  pred_elim_cl:                           6
% 4.03/0.99  pred_elim_cycles:                       6
% 4.03/0.99  merged_defs:                            8
% 4.03/0.99  merged_defs_ncl:                        0
% 4.03/0.99  bin_hyper_res:                          8
% 4.03/0.99  prep_cycles:                            4
% 4.03/0.99  pred_elim_time:                         0.007
% 4.03/0.99  splitting_time:                         0.
% 4.03/0.99  sem_filter_time:                        0.
% 4.03/0.99  monotx_time:                            0.
% 4.03/0.99  subtype_inf_time:                       0.
% 4.03/0.99  
% 4.03/0.99  ------ Problem properties
% 4.03/0.99  
% 4.03/0.99  clauses:                                21
% 4.03/0.99  conjectures:                            2
% 4.03/0.99  epr:                                    4
% 4.03/0.99  horn:                                   20
% 4.03/0.99  ground:                                 5
% 4.03/0.99  unary:                                  6
% 4.03/0.99  binary:                                 11
% 4.03/0.99  lits:                                   43
% 4.03/0.99  lits_eq:                                14
% 4.03/0.99  fd_pure:                                0
% 4.03/0.99  fd_pseudo:                              0
% 4.03/0.99  fd_cond:                                1
% 4.03/0.99  fd_pseudo_cond:                         1
% 4.03/0.99  ac_symbols:                             0
% 4.03/0.99  
% 4.03/0.99  ------ Propositional Solver
% 4.03/0.99  
% 4.03/0.99  prop_solver_calls:                      30
% 4.03/0.99  prop_fast_solver_calls:                 852
% 4.03/0.99  smt_solver_calls:                       0
% 4.03/0.99  smt_fast_solver_calls:                  0
% 4.03/0.99  prop_num_of_clauses:                    6331
% 4.03/0.99  prop_preprocess_simplified:             12724
% 4.03/0.99  prop_fo_subsumed:                       6
% 4.03/0.99  prop_solver_time:                       0.
% 4.03/0.99  smt_solver_time:                        0.
% 4.03/0.99  smt_fast_solver_time:                   0.
% 4.03/0.99  prop_fast_solver_time:                  0.
% 4.03/0.99  prop_unsat_core_time:                   0.
% 4.03/0.99  
% 4.03/0.99  ------ QBF
% 4.03/0.99  
% 4.03/0.99  qbf_q_res:                              0
% 4.03/0.99  qbf_num_tautologies:                    0
% 4.03/0.99  qbf_prep_cycles:                        0
% 4.03/0.99  
% 4.03/0.99  ------ BMC1
% 4.03/0.99  
% 4.03/0.99  bmc1_current_bound:                     -1
% 4.03/0.99  bmc1_last_solved_bound:                 -1
% 4.03/0.99  bmc1_unsat_core_size:                   -1
% 4.03/0.99  bmc1_unsat_core_parents_size:           -1
% 4.03/0.99  bmc1_merge_next_fun:                    0
% 4.03/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.03/0.99  
% 4.03/0.99  ------ Instantiation
% 4.03/0.99  
% 4.03/0.99  inst_num_of_clauses:                    1629
% 4.03/0.99  inst_num_in_passive:                    396
% 4.03/0.99  inst_num_in_active:                     682
% 4.03/0.99  inst_num_in_unprocessed:                551
% 4.03/0.99  inst_num_of_loops:                      740
% 4.03/0.99  inst_num_of_learning_restarts:          0
% 4.03/0.99  inst_num_moves_active_passive:          57
% 4.03/0.99  inst_lit_activity:                      0
% 4.03/0.99  inst_lit_activity_moves:                0
% 4.03/0.99  inst_num_tautologies:                   0
% 4.03/0.99  inst_num_prop_implied:                  0
% 4.03/0.99  inst_num_existing_simplified:           0
% 4.03/0.99  inst_num_eq_res_simplified:             0
% 4.03/0.99  inst_num_child_elim:                    0
% 4.03/0.99  inst_num_of_dismatching_blockings:      862
% 4.03/0.99  inst_num_of_non_proper_insts:           1893
% 4.03/0.99  inst_num_of_duplicates:                 0
% 4.03/0.99  inst_inst_num_from_inst_to_res:         0
% 4.03/0.99  inst_dismatching_checking_time:         0.
% 4.03/0.99  
% 4.03/0.99  ------ Resolution
% 4.03/0.99  
% 4.03/0.99  res_num_of_clauses:                     0
% 4.03/0.99  res_num_in_passive:                     0
% 4.03/0.99  res_num_in_active:                      0
% 4.03/0.99  res_num_of_loops:                       116
% 4.03/0.99  res_forward_subset_subsumed:            193
% 4.03/0.99  res_backward_subset_subsumed:           0
% 4.03/0.99  res_forward_subsumed:                   0
% 4.03/0.99  res_backward_subsumed:                  0
% 4.03/0.99  res_forward_subsumption_resolution:     2
% 4.03/0.99  res_backward_subsumption_resolution:    0
% 4.03/0.99  res_clause_to_clause_subsumption:       2659
% 4.03/0.99  res_orphan_elimination:                 0
% 4.03/0.99  res_tautology_del:                      107
% 4.03/0.99  res_num_eq_res_simplified:              0
% 4.03/0.99  res_num_sel_changes:                    0
% 4.03/0.99  res_moves_from_active_to_pass:          0
% 4.03/0.99  
% 4.03/0.99  ------ Superposition
% 4.03/0.99  
% 4.03/0.99  sup_time_total:                         0.
% 4.03/0.99  sup_time_generating:                    0.
% 4.03/0.99  sup_time_sim_full:                      0.
% 4.03/0.99  sup_time_sim_immed:                     0.
% 4.03/0.99  
% 4.03/0.99  sup_num_of_clauses:                     376
% 4.03/0.99  sup_num_in_active:                      60
% 4.03/0.99  sup_num_in_passive:                     316
% 4.03/0.99  sup_num_of_loops:                       147
% 4.03/0.99  sup_fw_superposition:                   551
% 4.03/0.99  sup_bw_superposition:                   380
% 4.03/0.99  sup_immediate_simplified:               332
% 4.03/0.99  sup_given_eliminated:                   6
% 4.03/0.99  comparisons_done:                       0
% 4.03/0.99  comparisons_avoided:                    0
% 4.03/0.99  
% 4.03/0.99  ------ Simplifications
% 4.03/0.99  
% 4.03/0.99  
% 4.03/0.99  sim_fw_subset_subsumed:                 10
% 4.03/0.99  sim_bw_subset_subsumed:                 10
% 4.03/0.99  sim_fw_subsumed:                        94
% 4.03/0.99  sim_bw_subsumed:                        32
% 4.03/0.99  sim_fw_subsumption_res:                 0
% 4.03/0.99  sim_bw_subsumption_res:                 0
% 4.03/0.99  sim_tautology_del:                      7
% 4.03/0.99  sim_eq_tautology_del:                   71
% 4.03/0.99  sim_eq_res_simp:                        2
% 4.03/0.99  sim_fw_demodulated:                     132
% 4.03/0.99  sim_bw_demodulated:                     91
% 4.03/0.99  sim_light_normalised:                   207
% 4.03/0.99  sim_joinable_taut:                      0
% 4.03/0.99  sim_joinable_simp:                      0
% 4.03/0.99  sim_ac_normalised:                      0
% 4.03/0.99  sim_smt_subsumption:                    0
% 4.03/0.99  
%------------------------------------------------------------------------------
