%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:08 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  122 (1046 expanded)
%              Number of clauses        :   66 ( 382 expanded)
%              Number of leaves         :   13 ( 180 expanded)
%              Depth                    :   23
%              Number of atoms          :  342 (3737 expanded)
%              Number of equality atoms :  156 ( 797 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
        & r1_tarski(X0,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)
      & r1_tarski(sK0,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)
    & r1_tarski(sK0,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f36])).

fof(f62,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f24])).

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
    inference(nnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f50])).

fof(f63,plain,(
    ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f43])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_715,plain,
    ( r1_tarski(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_348,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_350,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_348,c_23])).

cnf(c_714,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_717,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1299,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_714,c_717])).

cnf(c_1317,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_350,c_1299])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_716,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1849,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_716])).

cnf(c_9,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_269,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_9,c_8])).

cnf(c_712,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_1875,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_712])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_856,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1080,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_856])).

cnf(c_1081,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1080])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_834,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1117,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_1121,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1117])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1202,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1203,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1202])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_857,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1207,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(c_1208,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1207])).

cnf(c_2339,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1875,c_28,c_1081,c_1121,c_1203,c_1208])).

cnf(c_2340,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2339])).

cnf(c_2348,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | sK1 = k1_xboole_0
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_2340])).

cnf(c_2449,plain,
    ( k7_relat_1(sK3,sK2) = sK3
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_715,c_2348])).

cnf(c_11,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_21,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_289,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_290,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK3 != k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_711,plain,
    ( sK3 != k2_partfun1(sK0,sK1,sK3,sK2)
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_254,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_255,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_713,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_255])).

cnf(c_876,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_714,c_713])).

cnf(c_894,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_711,c_876])).

cnf(c_2456,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2449,c_894])).

cnf(c_2532,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2449,c_2456])).

cnf(c_2546,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2532,c_28])).

cnf(c_2562,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2546,c_714])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2564,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2562,c_3])).

cnf(c_1441,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_712])).

cnf(c_2700,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2564,c_1441])).

cnf(c_3382,plain,
    ( k7_relat_1(sK3,X0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2700,c_28,c_1081,c_1121,c_1203,c_1208])).

cnf(c_2559,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2546,c_894])).

cnf(c_2570,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2559,c_3])).

cnf(c_3390,plain,
    ( sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3382,c_2570])).

cnf(c_3397,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3390])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3397,c_2564])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.04/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.05  
% 2.04/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.04/1.05  
% 2.04/1.05  ------  iProver source info
% 2.04/1.05  
% 2.04/1.05  git: date: 2020-06-30 10:37:57 +0100
% 2.04/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.04/1.05  git: non_committed_changes: false
% 2.04/1.05  git: last_make_outside_of_git: false
% 2.04/1.05  
% 2.04/1.05  ------ 
% 2.04/1.05  
% 2.04/1.05  ------ Input Options
% 2.04/1.05  
% 2.04/1.05  --out_options                           all
% 2.04/1.05  --tptp_safe_out                         true
% 2.04/1.05  --problem_path                          ""
% 2.04/1.05  --include_path                          ""
% 2.04/1.05  --clausifier                            res/vclausify_rel
% 2.04/1.05  --clausifier_options                    --mode clausify
% 2.04/1.05  --stdin                                 false
% 2.04/1.05  --stats_out                             all
% 2.04/1.05  
% 2.04/1.05  ------ General Options
% 2.04/1.05  
% 2.04/1.05  --fof                                   false
% 2.04/1.05  --time_out_real                         305.
% 2.04/1.05  --time_out_virtual                      -1.
% 2.04/1.05  --symbol_type_check                     false
% 2.04/1.05  --clausify_out                          false
% 2.04/1.05  --sig_cnt_out                           false
% 2.04/1.05  --trig_cnt_out                          false
% 2.04/1.05  --trig_cnt_out_tolerance                1.
% 2.04/1.05  --trig_cnt_out_sk_spl                   false
% 2.04/1.05  --abstr_cl_out                          false
% 2.04/1.05  
% 2.04/1.05  ------ Global Options
% 2.04/1.05  
% 2.04/1.05  --schedule                              default
% 2.04/1.05  --add_important_lit                     false
% 2.04/1.05  --prop_solver_per_cl                    1000
% 2.04/1.05  --min_unsat_core                        false
% 2.04/1.05  --soft_assumptions                      false
% 2.04/1.05  --soft_lemma_size                       3
% 2.04/1.05  --prop_impl_unit_size                   0
% 2.04/1.05  --prop_impl_unit                        []
% 2.04/1.05  --share_sel_clauses                     true
% 2.04/1.05  --reset_solvers                         false
% 2.04/1.05  --bc_imp_inh                            [conj_cone]
% 2.04/1.05  --conj_cone_tolerance                   3.
% 2.04/1.05  --extra_neg_conj                        none
% 2.04/1.05  --large_theory_mode                     true
% 2.04/1.05  --prolific_symb_bound                   200
% 2.04/1.05  --lt_threshold                          2000
% 2.04/1.05  --clause_weak_htbl                      true
% 2.04/1.05  --gc_record_bc_elim                     false
% 2.04/1.05  
% 2.04/1.05  ------ Preprocessing Options
% 2.04/1.05  
% 2.04/1.05  --preprocessing_flag                    true
% 2.04/1.05  --time_out_prep_mult                    0.1
% 2.04/1.05  --splitting_mode                        input
% 2.04/1.05  --splitting_grd                         true
% 2.04/1.05  --splitting_cvd                         false
% 2.04/1.05  --splitting_cvd_svl                     false
% 2.04/1.05  --splitting_nvd                         32
% 2.04/1.05  --sub_typing                            true
% 2.04/1.05  --prep_gs_sim                           true
% 2.04/1.05  --prep_unflatten                        true
% 2.04/1.05  --prep_res_sim                          true
% 2.04/1.05  --prep_upred                            true
% 2.04/1.05  --prep_sem_filter                       exhaustive
% 2.04/1.05  --prep_sem_filter_out                   false
% 2.04/1.05  --pred_elim                             true
% 2.04/1.05  --res_sim_input                         true
% 2.04/1.05  --eq_ax_congr_red                       true
% 2.04/1.05  --pure_diseq_elim                       true
% 2.04/1.05  --brand_transform                       false
% 2.04/1.05  --non_eq_to_eq                          false
% 2.04/1.05  --prep_def_merge                        true
% 2.04/1.05  --prep_def_merge_prop_impl              false
% 2.04/1.05  --prep_def_merge_mbd                    true
% 2.04/1.05  --prep_def_merge_tr_red                 false
% 2.04/1.05  --prep_def_merge_tr_cl                  false
% 2.04/1.05  --smt_preprocessing                     true
% 2.04/1.05  --smt_ac_axioms                         fast
% 2.04/1.05  --preprocessed_out                      false
% 2.04/1.05  --preprocessed_stats                    false
% 2.04/1.05  
% 2.04/1.05  ------ Abstraction refinement Options
% 2.04/1.05  
% 2.04/1.05  --abstr_ref                             []
% 2.04/1.05  --abstr_ref_prep                        false
% 2.04/1.05  --abstr_ref_until_sat                   false
% 2.04/1.05  --abstr_ref_sig_restrict                funpre
% 2.04/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.04/1.05  --abstr_ref_under                       []
% 2.04/1.05  
% 2.04/1.05  ------ SAT Options
% 2.04/1.05  
% 2.04/1.05  --sat_mode                              false
% 2.04/1.05  --sat_fm_restart_options                ""
% 2.04/1.05  --sat_gr_def                            false
% 2.04/1.05  --sat_epr_types                         true
% 2.04/1.05  --sat_non_cyclic_types                  false
% 2.04/1.05  --sat_finite_models                     false
% 2.04/1.05  --sat_fm_lemmas                         false
% 2.04/1.05  --sat_fm_prep                           false
% 2.04/1.05  --sat_fm_uc_incr                        true
% 2.04/1.05  --sat_out_model                         small
% 2.04/1.05  --sat_out_clauses                       false
% 2.04/1.05  
% 2.04/1.05  ------ QBF Options
% 2.04/1.05  
% 2.04/1.05  --qbf_mode                              false
% 2.04/1.05  --qbf_elim_univ                         false
% 2.04/1.05  --qbf_dom_inst                          none
% 2.04/1.05  --qbf_dom_pre_inst                      false
% 2.04/1.05  --qbf_sk_in                             false
% 2.04/1.05  --qbf_pred_elim                         true
% 2.04/1.05  --qbf_split                             512
% 2.04/1.05  
% 2.04/1.05  ------ BMC1 Options
% 2.04/1.05  
% 2.04/1.05  --bmc1_incremental                      false
% 2.04/1.05  --bmc1_axioms                           reachable_all
% 2.04/1.05  --bmc1_min_bound                        0
% 2.04/1.05  --bmc1_max_bound                        -1
% 2.04/1.05  --bmc1_max_bound_default                -1
% 2.04/1.05  --bmc1_symbol_reachability              true
% 2.04/1.05  --bmc1_property_lemmas                  false
% 2.04/1.05  --bmc1_k_induction                      false
% 2.04/1.05  --bmc1_non_equiv_states                 false
% 2.04/1.05  --bmc1_deadlock                         false
% 2.04/1.05  --bmc1_ucm                              false
% 2.04/1.05  --bmc1_add_unsat_core                   none
% 2.04/1.05  --bmc1_unsat_core_children              false
% 2.04/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.04/1.05  --bmc1_out_stat                         full
% 2.04/1.05  --bmc1_ground_init                      false
% 2.04/1.05  --bmc1_pre_inst_next_state              false
% 2.04/1.05  --bmc1_pre_inst_state                   false
% 2.04/1.05  --bmc1_pre_inst_reach_state             false
% 2.04/1.05  --bmc1_out_unsat_core                   false
% 2.04/1.05  --bmc1_aig_witness_out                  false
% 2.04/1.05  --bmc1_verbose                          false
% 2.04/1.05  --bmc1_dump_clauses_tptp                false
% 2.04/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.04/1.05  --bmc1_dump_file                        -
% 2.04/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.04/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.04/1.05  --bmc1_ucm_extend_mode                  1
% 2.04/1.05  --bmc1_ucm_init_mode                    2
% 2.04/1.05  --bmc1_ucm_cone_mode                    none
% 2.04/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.04/1.05  --bmc1_ucm_relax_model                  4
% 2.04/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.04/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.04/1.05  --bmc1_ucm_layered_model                none
% 2.04/1.05  --bmc1_ucm_max_lemma_size               10
% 2.04/1.05  
% 2.04/1.05  ------ AIG Options
% 2.04/1.05  
% 2.04/1.05  --aig_mode                              false
% 2.04/1.05  
% 2.04/1.05  ------ Instantiation Options
% 2.04/1.05  
% 2.04/1.05  --instantiation_flag                    true
% 2.04/1.05  --inst_sos_flag                         false
% 2.04/1.05  --inst_sos_phase                        true
% 2.04/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.04/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.04/1.05  --inst_lit_sel_side                     num_symb
% 2.04/1.05  --inst_solver_per_active                1400
% 2.04/1.05  --inst_solver_calls_frac                1.
% 2.04/1.05  --inst_passive_queue_type               priority_queues
% 2.04/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.04/1.05  --inst_passive_queues_freq              [25;2]
% 2.04/1.05  --inst_dismatching                      true
% 2.04/1.05  --inst_eager_unprocessed_to_passive     true
% 2.04/1.05  --inst_prop_sim_given                   true
% 2.04/1.05  --inst_prop_sim_new                     false
% 2.04/1.05  --inst_subs_new                         false
% 2.04/1.05  --inst_eq_res_simp                      false
% 2.04/1.05  --inst_subs_given                       false
% 2.04/1.05  --inst_orphan_elimination               true
% 2.04/1.05  --inst_learning_loop_flag               true
% 2.04/1.05  --inst_learning_start                   3000
% 2.04/1.05  --inst_learning_factor                  2
% 2.04/1.05  --inst_start_prop_sim_after_learn       3
% 2.04/1.05  --inst_sel_renew                        solver
% 2.04/1.05  --inst_lit_activity_flag                true
% 2.04/1.05  --inst_restr_to_given                   false
% 2.04/1.05  --inst_activity_threshold               500
% 2.04/1.05  --inst_out_proof                        true
% 2.04/1.05  
% 2.04/1.05  ------ Resolution Options
% 2.04/1.05  
% 2.04/1.05  --resolution_flag                       true
% 2.04/1.05  --res_lit_sel                           adaptive
% 2.04/1.05  --res_lit_sel_side                      none
% 2.04/1.05  --res_ordering                          kbo
% 2.04/1.05  --res_to_prop_solver                    active
% 2.04/1.05  --res_prop_simpl_new                    false
% 2.04/1.05  --res_prop_simpl_given                  true
% 2.04/1.05  --res_passive_queue_type                priority_queues
% 2.04/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.04/1.05  --res_passive_queues_freq               [15;5]
% 2.04/1.05  --res_forward_subs                      full
% 2.04/1.05  --res_backward_subs                     full
% 2.04/1.05  --res_forward_subs_resolution           true
% 2.04/1.05  --res_backward_subs_resolution          true
% 2.04/1.05  --res_orphan_elimination                true
% 2.04/1.05  --res_time_limit                        2.
% 2.04/1.05  --res_out_proof                         true
% 2.04/1.05  
% 2.04/1.05  ------ Superposition Options
% 2.04/1.05  
% 2.04/1.05  --superposition_flag                    true
% 2.04/1.05  --sup_passive_queue_type                priority_queues
% 2.04/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.04/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.04/1.05  --demod_completeness_check              fast
% 2.04/1.05  --demod_use_ground                      true
% 2.04/1.05  --sup_to_prop_solver                    passive
% 2.04/1.05  --sup_prop_simpl_new                    true
% 2.04/1.05  --sup_prop_simpl_given                  true
% 2.04/1.05  --sup_fun_splitting                     false
% 2.04/1.05  --sup_smt_interval                      50000
% 2.04/1.05  
% 2.04/1.05  ------ Superposition Simplification Setup
% 2.04/1.05  
% 2.04/1.05  --sup_indices_passive                   []
% 2.04/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.04/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.05  --sup_full_bw                           [BwDemod]
% 2.04/1.05  --sup_immed_triv                        [TrivRules]
% 2.04/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.04/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.05  --sup_immed_bw_main                     []
% 2.04/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.04/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.05  
% 2.04/1.05  ------ Combination Options
% 2.04/1.05  
% 2.04/1.05  --comb_res_mult                         3
% 2.04/1.05  --comb_sup_mult                         2
% 2.04/1.05  --comb_inst_mult                        10
% 2.04/1.05  
% 2.04/1.05  ------ Debug Options
% 2.04/1.05  
% 2.04/1.05  --dbg_backtrace                         false
% 2.04/1.05  --dbg_dump_prop_clauses                 false
% 2.04/1.05  --dbg_dump_prop_clauses_file            -
% 2.04/1.05  --dbg_out_stat                          false
% 2.04/1.05  ------ Parsing...
% 2.04/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.04/1.05  
% 2.04/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.04/1.05  
% 2.04/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.04/1.05  
% 2.04/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.04/1.05  ------ Proving...
% 2.04/1.05  ------ Problem Properties 
% 2.04/1.05  
% 2.04/1.05  
% 2.04/1.05  clauses                                 17
% 2.04/1.05  conjectures                             2
% 2.04/1.05  EPR                                     3
% 2.04/1.05  Horn                                    14
% 2.04/1.05  unary                                   6
% 2.04/1.05  binary                                  4
% 2.04/1.05  lits                                    36
% 2.04/1.05  lits eq                                 17
% 2.04/1.05  fd_pure                                 0
% 2.04/1.05  fd_pseudo                               0
% 2.04/1.05  fd_cond                                 1
% 2.04/1.05  fd_pseudo_cond                          1
% 2.04/1.05  AC symbols                              0
% 2.04/1.05  
% 2.04/1.05  ------ Schedule dynamic 5 is on 
% 2.04/1.05  
% 2.04/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.04/1.05  
% 2.04/1.05  
% 2.04/1.05  ------ 
% 2.04/1.05  Current options:
% 2.04/1.05  ------ 
% 2.04/1.05  
% 2.04/1.05  ------ Input Options
% 2.04/1.05  
% 2.04/1.05  --out_options                           all
% 2.04/1.05  --tptp_safe_out                         true
% 2.04/1.05  --problem_path                          ""
% 2.04/1.05  --include_path                          ""
% 2.04/1.05  --clausifier                            res/vclausify_rel
% 2.04/1.05  --clausifier_options                    --mode clausify
% 2.04/1.05  --stdin                                 false
% 2.04/1.05  --stats_out                             all
% 2.04/1.05  
% 2.04/1.05  ------ General Options
% 2.04/1.05  
% 2.04/1.05  --fof                                   false
% 2.04/1.05  --time_out_real                         305.
% 2.04/1.05  --time_out_virtual                      -1.
% 2.04/1.05  --symbol_type_check                     false
% 2.04/1.05  --clausify_out                          false
% 2.04/1.05  --sig_cnt_out                           false
% 2.04/1.05  --trig_cnt_out                          false
% 2.04/1.05  --trig_cnt_out_tolerance                1.
% 2.04/1.05  --trig_cnt_out_sk_spl                   false
% 2.04/1.05  --abstr_cl_out                          false
% 2.04/1.05  
% 2.04/1.05  ------ Global Options
% 2.04/1.05  
% 2.04/1.05  --schedule                              default
% 2.04/1.05  --add_important_lit                     false
% 2.04/1.05  --prop_solver_per_cl                    1000
% 2.04/1.05  --min_unsat_core                        false
% 2.04/1.05  --soft_assumptions                      false
% 2.04/1.05  --soft_lemma_size                       3
% 2.04/1.05  --prop_impl_unit_size                   0
% 2.04/1.05  --prop_impl_unit                        []
% 2.04/1.05  --share_sel_clauses                     true
% 2.04/1.05  --reset_solvers                         false
% 2.04/1.05  --bc_imp_inh                            [conj_cone]
% 2.04/1.05  --conj_cone_tolerance                   3.
% 2.04/1.05  --extra_neg_conj                        none
% 2.04/1.05  --large_theory_mode                     true
% 2.04/1.05  --prolific_symb_bound                   200
% 2.04/1.05  --lt_threshold                          2000
% 2.04/1.05  --clause_weak_htbl                      true
% 2.04/1.05  --gc_record_bc_elim                     false
% 2.04/1.05  
% 2.04/1.05  ------ Preprocessing Options
% 2.04/1.05  
% 2.04/1.05  --preprocessing_flag                    true
% 2.04/1.05  --time_out_prep_mult                    0.1
% 2.04/1.05  --splitting_mode                        input
% 2.04/1.05  --splitting_grd                         true
% 2.04/1.05  --splitting_cvd                         false
% 2.04/1.05  --splitting_cvd_svl                     false
% 2.04/1.05  --splitting_nvd                         32
% 2.04/1.05  --sub_typing                            true
% 2.04/1.05  --prep_gs_sim                           true
% 2.04/1.05  --prep_unflatten                        true
% 2.04/1.05  --prep_res_sim                          true
% 2.04/1.05  --prep_upred                            true
% 2.04/1.05  --prep_sem_filter                       exhaustive
% 2.04/1.05  --prep_sem_filter_out                   false
% 2.04/1.05  --pred_elim                             true
% 2.04/1.05  --res_sim_input                         true
% 2.04/1.05  --eq_ax_congr_red                       true
% 2.04/1.05  --pure_diseq_elim                       true
% 2.04/1.05  --brand_transform                       false
% 2.04/1.05  --non_eq_to_eq                          false
% 2.04/1.05  --prep_def_merge                        true
% 2.04/1.05  --prep_def_merge_prop_impl              false
% 2.04/1.05  --prep_def_merge_mbd                    true
% 2.04/1.05  --prep_def_merge_tr_red                 false
% 2.04/1.05  --prep_def_merge_tr_cl                  false
% 2.04/1.05  --smt_preprocessing                     true
% 2.04/1.05  --smt_ac_axioms                         fast
% 2.04/1.05  --preprocessed_out                      false
% 2.04/1.05  --preprocessed_stats                    false
% 2.04/1.05  
% 2.04/1.05  ------ Abstraction refinement Options
% 2.04/1.05  
% 2.04/1.05  --abstr_ref                             []
% 2.04/1.05  --abstr_ref_prep                        false
% 2.04/1.05  --abstr_ref_until_sat                   false
% 2.04/1.05  --abstr_ref_sig_restrict                funpre
% 2.04/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.04/1.05  --abstr_ref_under                       []
% 2.04/1.05  
% 2.04/1.05  ------ SAT Options
% 2.04/1.05  
% 2.04/1.05  --sat_mode                              false
% 2.04/1.05  --sat_fm_restart_options                ""
% 2.04/1.05  --sat_gr_def                            false
% 2.04/1.05  --sat_epr_types                         true
% 2.04/1.05  --sat_non_cyclic_types                  false
% 2.04/1.05  --sat_finite_models                     false
% 2.04/1.05  --sat_fm_lemmas                         false
% 2.04/1.05  --sat_fm_prep                           false
% 2.04/1.05  --sat_fm_uc_incr                        true
% 2.04/1.05  --sat_out_model                         small
% 2.04/1.05  --sat_out_clauses                       false
% 2.04/1.05  
% 2.04/1.05  ------ QBF Options
% 2.04/1.05  
% 2.04/1.05  --qbf_mode                              false
% 2.04/1.05  --qbf_elim_univ                         false
% 2.04/1.05  --qbf_dom_inst                          none
% 2.04/1.05  --qbf_dom_pre_inst                      false
% 2.04/1.05  --qbf_sk_in                             false
% 2.04/1.05  --qbf_pred_elim                         true
% 2.04/1.05  --qbf_split                             512
% 2.04/1.05  
% 2.04/1.05  ------ BMC1 Options
% 2.04/1.05  
% 2.04/1.05  --bmc1_incremental                      false
% 2.04/1.05  --bmc1_axioms                           reachable_all
% 2.04/1.05  --bmc1_min_bound                        0
% 2.04/1.05  --bmc1_max_bound                        -1
% 2.04/1.05  --bmc1_max_bound_default                -1
% 2.04/1.05  --bmc1_symbol_reachability              true
% 2.04/1.05  --bmc1_property_lemmas                  false
% 2.04/1.05  --bmc1_k_induction                      false
% 2.04/1.05  --bmc1_non_equiv_states                 false
% 2.04/1.05  --bmc1_deadlock                         false
% 2.04/1.05  --bmc1_ucm                              false
% 2.04/1.05  --bmc1_add_unsat_core                   none
% 2.04/1.05  --bmc1_unsat_core_children              false
% 2.04/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.04/1.05  --bmc1_out_stat                         full
% 2.04/1.05  --bmc1_ground_init                      false
% 2.04/1.05  --bmc1_pre_inst_next_state              false
% 2.04/1.05  --bmc1_pre_inst_state                   false
% 2.04/1.05  --bmc1_pre_inst_reach_state             false
% 2.04/1.05  --bmc1_out_unsat_core                   false
% 2.04/1.05  --bmc1_aig_witness_out                  false
% 2.04/1.05  --bmc1_verbose                          false
% 2.04/1.05  --bmc1_dump_clauses_tptp                false
% 2.04/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.04/1.05  --bmc1_dump_file                        -
% 2.04/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.04/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.04/1.05  --bmc1_ucm_extend_mode                  1
% 2.04/1.05  --bmc1_ucm_init_mode                    2
% 2.04/1.05  --bmc1_ucm_cone_mode                    none
% 2.04/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.04/1.05  --bmc1_ucm_relax_model                  4
% 2.04/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.04/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.04/1.05  --bmc1_ucm_layered_model                none
% 2.04/1.05  --bmc1_ucm_max_lemma_size               10
% 2.04/1.05  
% 2.04/1.05  ------ AIG Options
% 2.04/1.05  
% 2.04/1.05  --aig_mode                              false
% 2.04/1.05  
% 2.04/1.05  ------ Instantiation Options
% 2.04/1.05  
% 2.04/1.05  --instantiation_flag                    true
% 2.04/1.05  --inst_sos_flag                         false
% 2.04/1.05  --inst_sos_phase                        true
% 2.04/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.04/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.04/1.05  --inst_lit_sel_side                     none
% 2.04/1.05  --inst_solver_per_active                1400
% 2.04/1.05  --inst_solver_calls_frac                1.
% 2.04/1.05  --inst_passive_queue_type               priority_queues
% 2.04/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.04/1.05  --inst_passive_queues_freq              [25;2]
% 2.04/1.05  --inst_dismatching                      true
% 2.04/1.05  --inst_eager_unprocessed_to_passive     true
% 2.04/1.05  --inst_prop_sim_given                   true
% 2.04/1.05  --inst_prop_sim_new                     false
% 2.04/1.05  --inst_subs_new                         false
% 2.04/1.05  --inst_eq_res_simp                      false
% 2.04/1.05  --inst_subs_given                       false
% 2.04/1.05  --inst_orphan_elimination               true
% 2.04/1.05  --inst_learning_loop_flag               true
% 2.04/1.05  --inst_learning_start                   3000
% 2.04/1.05  --inst_learning_factor                  2
% 2.04/1.05  --inst_start_prop_sim_after_learn       3
% 2.04/1.05  --inst_sel_renew                        solver
% 2.04/1.05  --inst_lit_activity_flag                true
% 2.04/1.05  --inst_restr_to_given                   false
% 2.04/1.05  --inst_activity_threshold               500
% 2.04/1.05  --inst_out_proof                        true
% 2.04/1.05  
% 2.04/1.05  ------ Resolution Options
% 2.04/1.05  
% 2.04/1.05  --resolution_flag                       false
% 2.04/1.05  --res_lit_sel                           adaptive
% 2.04/1.05  --res_lit_sel_side                      none
% 2.04/1.05  --res_ordering                          kbo
% 2.04/1.05  --res_to_prop_solver                    active
% 2.04/1.05  --res_prop_simpl_new                    false
% 2.04/1.05  --res_prop_simpl_given                  true
% 2.04/1.05  --res_passive_queue_type                priority_queues
% 2.04/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.04/1.05  --res_passive_queues_freq               [15;5]
% 2.04/1.05  --res_forward_subs                      full
% 2.04/1.05  --res_backward_subs                     full
% 2.04/1.05  --res_forward_subs_resolution           true
% 2.04/1.05  --res_backward_subs_resolution          true
% 2.04/1.05  --res_orphan_elimination                true
% 2.04/1.05  --res_time_limit                        2.
% 2.04/1.05  --res_out_proof                         true
% 2.04/1.05  
% 2.04/1.05  ------ Superposition Options
% 2.04/1.05  
% 2.04/1.05  --superposition_flag                    true
% 2.04/1.05  --sup_passive_queue_type                priority_queues
% 2.04/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.04/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.04/1.05  --demod_completeness_check              fast
% 2.04/1.05  --demod_use_ground                      true
% 2.04/1.05  --sup_to_prop_solver                    passive
% 2.04/1.05  --sup_prop_simpl_new                    true
% 2.04/1.05  --sup_prop_simpl_given                  true
% 2.04/1.05  --sup_fun_splitting                     false
% 2.04/1.05  --sup_smt_interval                      50000
% 2.04/1.05  
% 2.04/1.05  ------ Superposition Simplification Setup
% 2.04/1.05  
% 2.04/1.05  --sup_indices_passive                   []
% 2.04/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.04/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.05  --sup_full_bw                           [BwDemod]
% 2.04/1.05  --sup_immed_triv                        [TrivRules]
% 2.04/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.04/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.05  --sup_immed_bw_main                     []
% 2.04/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.04/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.05  
% 2.04/1.05  ------ Combination Options
% 2.04/1.05  
% 2.04/1.05  --comb_res_mult                         3
% 2.04/1.05  --comb_sup_mult                         2
% 2.04/1.05  --comb_inst_mult                        10
% 2.04/1.05  
% 2.04/1.05  ------ Debug Options
% 2.04/1.05  
% 2.04/1.05  --dbg_backtrace                         false
% 2.04/1.05  --dbg_dump_prop_clauses                 false
% 2.04/1.05  --dbg_dump_prop_clauses_file            -
% 2.04/1.05  --dbg_out_stat                          false
% 2.04/1.05  
% 2.04/1.05  
% 2.04/1.05  
% 2.04/1.05  
% 2.04/1.05  ------ Proving...
% 2.04/1.05  
% 2.04/1.05  
% 2.04/1.05  % SZS status Theorem for theBenchmark.p
% 2.04/1.05  
% 2.04/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 2.04/1.05  
% 2.04/1.05  fof(f12,conjecture,(
% 2.04/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 2.04/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.05  
% 2.04/1.05  fof(f13,negated_conjecture,(
% 2.04/1.05    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 2.04/1.05    inference(negated_conjecture,[],[f12])).
% 2.04/1.05  
% 2.04/1.05  fof(f28,plain,(
% 2.04/1.05    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.04/1.05    inference(ennf_transformation,[],[f13])).
% 2.04/1.05  
% 2.04/1.05  fof(f29,plain,(
% 2.04/1.05    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.04/1.05    inference(flattening,[],[f28])).
% 2.04/1.05  
% 2.04/1.05  fof(f36,plain,(
% 2.04/1.05    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) & r1_tarski(sK0,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.04/1.05    introduced(choice_axiom,[])).
% 2.04/1.05  
% 2.04/1.05  fof(f37,plain,(
% 2.04/1.05    ~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) & r1_tarski(sK0,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.04/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f36])).
% 2.04/1.05  
% 2.04/1.05  fof(f62,plain,(
% 2.04/1.05    r1_tarski(sK0,sK2)),
% 2.04/1.05    inference(cnf_transformation,[],[f37])).
% 2.04/1.05  
% 2.04/1.05  fof(f10,axiom,(
% 2.04/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.04/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.05  
% 2.04/1.05  fof(f24,plain,(
% 2.04/1.05    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/1.05    inference(ennf_transformation,[],[f10])).
% 2.04/1.05  
% 2.04/1.05  fof(f25,plain,(
% 2.04/1.05    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/1.05    inference(flattening,[],[f24])).
% 2.04/1.05  
% 2.04/1.05  fof(f35,plain,(
% 2.04/1.05    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/1.05    inference(nnf_transformation,[],[f25])).
% 2.04/1.05  
% 2.04/1.05  fof(f52,plain,(
% 2.04/1.05    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.04/1.05    inference(cnf_transformation,[],[f35])).
% 2.04/1.05  
% 2.04/1.05  fof(f60,plain,(
% 2.04/1.05    v1_funct_2(sK3,sK0,sK1)),
% 2.04/1.05    inference(cnf_transformation,[],[f37])).
% 2.04/1.05  
% 2.04/1.05  fof(f61,plain,(
% 2.04/1.05    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.04/1.05    inference(cnf_transformation,[],[f37])).
% 2.04/1.05  
% 2.04/1.05  fof(f7,axiom,(
% 2.04/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.04/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.05  
% 2.04/1.05  fof(f19,plain,(
% 2.04/1.05    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/1.05    inference(ennf_transformation,[],[f7])).
% 2.04/1.05  
% 2.04/1.05  fof(f48,plain,(
% 2.04/1.05    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.04/1.05    inference(cnf_transformation,[],[f19])).
% 2.04/1.05  
% 2.04/1.05  fof(f9,axiom,(
% 2.04/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 2.04/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.05  
% 2.04/1.05  fof(f22,plain,(
% 2.04/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.04/1.05    inference(ennf_transformation,[],[f9])).
% 2.04/1.05  
% 2.04/1.05  fof(f23,plain,(
% 2.04/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.04/1.05    inference(flattening,[],[f22])).
% 2.04/1.05  
% 2.04/1.05  fof(f51,plain,(
% 2.04/1.05    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 2.04/1.05    inference(cnf_transformation,[],[f23])).
% 2.04/1.05  
% 2.04/1.05  fof(f6,axiom,(
% 2.04/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.04/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.05  
% 2.04/1.05  fof(f14,plain,(
% 2.04/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.04/1.05    inference(pure_predicate_removal,[],[f6])).
% 2.04/1.05  
% 2.04/1.05  fof(f18,plain,(
% 2.04/1.05    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/1.05    inference(ennf_transformation,[],[f14])).
% 2.04/1.05  
% 2.04/1.05  fof(f47,plain,(
% 2.04/1.05    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.04/1.05    inference(cnf_transformation,[],[f18])).
% 2.04/1.05  
% 2.04/1.05  fof(f5,axiom,(
% 2.04/1.05    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.04/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.05  
% 2.04/1.05  fof(f16,plain,(
% 2.04/1.05    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.04/1.05    inference(ennf_transformation,[],[f5])).
% 2.04/1.05  
% 2.04/1.05  fof(f17,plain,(
% 2.04/1.05    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.04/1.05    inference(flattening,[],[f16])).
% 2.04/1.05  
% 2.04/1.05  fof(f46,plain,(
% 2.04/1.05    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.04/1.05    inference(cnf_transformation,[],[f17])).
% 2.04/1.05  
% 2.04/1.05  fof(f3,axiom,(
% 2.04/1.05    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.04/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.05  
% 2.04/1.05  fof(f15,plain,(
% 2.04/1.05    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.04/1.05    inference(ennf_transformation,[],[f3])).
% 2.04/1.05  
% 2.04/1.05  fof(f44,plain,(
% 2.04/1.05    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.04/1.05    inference(cnf_transformation,[],[f15])).
% 2.04/1.05  
% 2.04/1.05  fof(f4,axiom,(
% 2.04/1.05    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.04/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.05  
% 2.04/1.05  fof(f45,plain,(
% 2.04/1.05    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.04/1.05    inference(cnf_transformation,[],[f4])).
% 2.04/1.05  
% 2.04/1.05  fof(f1,axiom,(
% 2.04/1.05    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.04/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.05  
% 2.04/1.05  fof(f30,plain,(
% 2.04/1.05    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.04/1.05    inference(nnf_transformation,[],[f1])).
% 2.04/1.05  
% 2.04/1.05  fof(f31,plain,(
% 2.04/1.05    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.04/1.05    inference(flattening,[],[f30])).
% 2.04/1.05  
% 2.04/1.05  fof(f38,plain,(
% 2.04/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.04/1.05    inference(cnf_transformation,[],[f31])).
% 2.04/1.05  
% 2.04/1.05  fof(f65,plain,(
% 2.04/1.05    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.04/1.05    inference(equality_resolution,[],[f38])).
% 2.04/1.05  
% 2.04/1.05  fof(f8,axiom,(
% 2.04/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.04/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.05  
% 2.04/1.05  fof(f20,plain,(
% 2.04/1.05    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.04/1.05    inference(ennf_transformation,[],[f8])).
% 2.04/1.05  
% 2.04/1.05  fof(f21,plain,(
% 2.04/1.05    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/1.05    inference(flattening,[],[f20])).
% 2.04/1.05  
% 2.04/1.05  fof(f34,plain,(
% 2.04/1.05    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.04/1.05    inference(nnf_transformation,[],[f21])).
% 2.04/1.05  
% 2.04/1.05  fof(f50,plain,(
% 2.04/1.05    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.04/1.05    inference(cnf_transformation,[],[f34])).
% 2.04/1.05  
% 2.04/1.05  fof(f68,plain,(
% 2.04/1.05    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.04/1.05    inference(equality_resolution,[],[f50])).
% 2.04/1.05  
% 2.04/1.05  fof(f63,plain,(
% 2.04/1.05    ~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)),
% 2.04/1.05    inference(cnf_transformation,[],[f37])).
% 2.04/1.05  
% 2.04/1.05  fof(f11,axiom,(
% 2.04/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.04/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.05  
% 2.04/1.05  fof(f26,plain,(
% 2.04/1.05    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.04/1.05    inference(ennf_transformation,[],[f11])).
% 2.04/1.05  
% 2.04/1.05  fof(f27,plain,(
% 2.04/1.05    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.04/1.05    inference(flattening,[],[f26])).
% 2.04/1.05  
% 2.04/1.05  fof(f58,plain,(
% 2.04/1.05    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.04/1.05    inference(cnf_transformation,[],[f27])).
% 2.04/1.05  
% 2.04/1.05  fof(f59,plain,(
% 2.04/1.05    v1_funct_1(sK3)),
% 2.04/1.05    inference(cnf_transformation,[],[f37])).
% 2.04/1.05  
% 2.04/1.05  fof(f2,axiom,(
% 2.04/1.05    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.04/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.05  
% 2.04/1.05  fof(f32,plain,(
% 2.04/1.05    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.04/1.05    inference(nnf_transformation,[],[f2])).
% 2.04/1.05  
% 2.04/1.05  fof(f33,plain,(
% 2.04/1.05    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.04/1.05    inference(flattening,[],[f32])).
% 2.04/1.05  
% 2.04/1.05  fof(f43,plain,(
% 2.04/1.05    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.04/1.05    inference(cnf_transformation,[],[f33])).
% 2.04/1.05  
% 2.04/1.05  fof(f66,plain,(
% 2.04/1.05    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.04/1.05    inference(equality_resolution,[],[f43])).
% 2.04/1.05  
% 2.04/1.05  cnf(c_22,negated_conjecture,
% 2.04/1.05      ( r1_tarski(sK0,sK2) ),
% 2.04/1.05      inference(cnf_transformation,[],[f62]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_715,plain,
% 2.04/1.05      ( r1_tarski(sK0,sK2) = iProver_top ),
% 2.04/1.05      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_19,plain,
% 2.04/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 2.04/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.04/1.05      | k1_relset_1(X1,X2,X0) = X1
% 2.04/1.05      | k1_xboole_0 = X2 ),
% 2.04/1.05      inference(cnf_transformation,[],[f52]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_24,negated_conjecture,
% 2.04/1.05      ( v1_funct_2(sK3,sK0,sK1) ),
% 2.04/1.05      inference(cnf_transformation,[],[f60]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_347,plain,
% 2.04/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.04/1.05      | k1_relset_1(X1,X2,X0) = X1
% 2.04/1.05      | sK3 != X0
% 2.04/1.05      | sK1 != X2
% 2.04/1.05      | sK0 != X1
% 2.04/1.05      | k1_xboole_0 = X2 ),
% 2.04/1.05      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_348,plain,
% 2.04/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.04/1.05      | k1_relset_1(sK0,sK1,sK3) = sK0
% 2.04/1.05      | k1_xboole_0 = sK1 ),
% 2.04/1.05      inference(unflattening,[status(thm)],[c_347]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_23,negated_conjecture,
% 2.04/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.04/1.05      inference(cnf_transformation,[],[f61]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_350,plain,
% 2.04/1.05      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 2.04/1.05      inference(global_propositional_subsumption,
% 2.04/1.05                [status(thm)],
% 2.04/1.05                [c_348,c_23]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_714,plain,
% 2.04/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.04/1.05      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_10,plain,
% 2.04/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.04/1.05      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.04/1.05      inference(cnf_transformation,[],[f48]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_717,plain,
% 2.04/1.05      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.04/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.04/1.05      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_1299,plain,
% 2.04/1.05      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 2.04/1.05      inference(superposition,[status(thm)],[c_714,c_717]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_1317,plain,
% 2.04/1.05      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 2.04/1.05      inference(superposition,[status(thm)],[c_350,c_1299]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_13,plain,
% 2.04/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.04/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 2.04/1.05      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 2.04/1.05      inference(cnf_transformation,[],[f51]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_716,plain,
% 2.04/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.04/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 2.04/1.05      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 2.04/1.05      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_1849,plain,
% 2.04/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 2.04/1.05      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 2.04/1.05      inference(superposition,[status(thm)],[c_714,c_716]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_9,plain,
% 2.04/1.05      ( v4_relat_1(X0,X1)
% 2.04/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.04/1.05      inference(cnf_transformation,[],[f47]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_8,plain,
% 2.04/1.05      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.04/1.05      inference(cnf_transformation,[],[f46]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_269,plain,
% 2.04/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.04/1.05      | ~ v1_relat_1(X0)
% 2.04/1.05      | k7_relat_1(X0,X1) = X0 ),
% 2.04/1.05      inference(resolution,[status(thm)],[c_9,c_8]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_712,plain,
% 2.04/1.05      ( k7_relat_1(X0,X1) = X0
% 2.04/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.04/1.05      | v1_relat_1(X0) != iProver_top ),
% 2.04/1.05      inference(predicate_to_equality,[status(thm)],[c_269]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_1875,plain,
% 2.04/1.05      ( k7_relat_1(sK3,X0) = sK3
% 2.04/1.05      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 2.04/1.05      | v1_relat_1(sK3) != iProver_top ),
% 2.04/1.05      inference(superposition,[status(thm)],[c_1849,c_712]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_28,plain,
% 2.04/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.04/1.05      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_856,plain,
% 2.04/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.04/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
% 2.04/1.05      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 2.04/1.05      inference(instantiation,[status(thm)],[c_13]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_1080,plain,
% 2.04/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
% 2.04/1.05      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.04/1.05      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
% 2.04/1.05      inference(instantiation,[status(thm)],[c_856]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_1081,plain,
% 2.04/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top
% 2.04/1.05      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.04/1.05      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top ),
% 2.04/1.05      inference(predicate_to_equality,[status(thm)],[c_1080]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_6,plain,
% 2.04/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.04/1.05      | ~ v1_relat_1(X1)
% 2.04/1.05      | v1_relat_1(X0) ),
% 2.04/1.05      inference(cnf_transformation,[],[f44]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_834,plain,
% 2.04/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.04/1.05      | v1_relat_1(X0)
% 2.04/1.05      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.04/1.05      inference(instantiation,[status(thm)],[c_6]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_1117,plain,
% 2.04/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
% 2.04/1.05      | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))
% 2.04/1.05      | v1_relat_1(sK3) ),
% 2.04/1.05      inference(instantiation,[status(thm)],[c_834]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_1121,plain,
% 2.04/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) != iProver_top
% 2.04/1.05      | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) != iProver_top
% 2.04/1.05      | v1_relat_1(sK3) = iProver_top ),
% 2.04/1.05      inference(predicate_to_equality,[status(thm)],[c_1117]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_7,plain,
% 2.04/1.05      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.04/1.05      inference(cnf_transformation,[],[f45]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_1202,plain,
% 2.04/1.05      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) ),
% 2.04/1.05      inference(instantiation,[status(thm)],[c_7]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_1203,plain,
% 2.04/1.05      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) = iProver_top ),
% 2.04/1.05      inference(predicate_to_equality,[status(thm)],[c_1202]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_2,plain,
% 2.04/1.05      ( r1_tarski(X0,X0) ),
% 2.04/1.05      inference(cnf_transformation,[],[f65]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_857,plain,
% 2.04/1.05      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 2.04/1.05      inference(instantiation,[status(thm)],[c_2]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_1207,plain,
% 2.04/1.05      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
% 2.04/1.05      inference(instantiation,[status(thm)],[c_857]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_1208,plain,
% 2.04/1.05      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) = iProver_top ),
% 2.04/1.05      inference(predicate_to_equality,[status(thm)],[c_1207]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_2339,plain,
% 2.04/1.05      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 2.04/1.05      | k7_relat_1(sK3,X0) = sK3 ),
% 2.04/1.05      inference(global_propositional_subsumption,
% 2.04/1.05                [status(thm)],
% 2.04/1.05                [c_1875,c_28,c_1081,c_1121,c_1203,c_1208]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_2340,plain,
% 2.04/1.05      ( k7_relat_1(sK3,X0) = sK3
% 2.04/1.05      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 2.04/1.05      inference(renaming,[status(thm)],[c_2339]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_2348,plain,
% 2.04/1.05      ( k7_relat_1(sK3,X0) = sK3
% 2.04/1.05      | sK1 = k1_xboole_0
% 2.04/1.05      | r1_tarski(sK0,X0) != iProver_top ),
% 2.04/1.05      inference(superposition,[status(thm)],[c_1317,c_2340]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_2449,plain,
% 2.04/1.05      ( k7_relat_1(sK3,sK2) = sK3 | sK1 = k1_xboole_0 ),
% 2.04/1.05      inference(superposition,[status(thm)],[c_715,c_2348]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_11,plain,
% 2.04/1.05      ( r2_relset_1(X0,X1,X2,X2)
% 2.04/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.04/1.05      inference(cnf_transformation,[],[f68]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_21,negated_conjecture,
% 2.04/1.05      ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
% 2.04/1.05      inference(cnf_transformation,[],[f63]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_289,plain,
% 2.04/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.04/1.05      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 2.04/1.05      | sK3 != X0
% 2.04/1.05      | sK1 != X2
% 2.04/1.05      | sK0 != X1 ),
% 2.04/1.05      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_290,plain,
% 2.04/1.05      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.04/1.05      | sK3 != k2_partfun1(sK0,sK1,sK3,sK2) ),
% 2.04/1.05      inference(unflattening,[status(thm)],[c_289]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_711,plain,
% 2.04/1.05      ( sK3 != k2_partfun1(sK0,sK1,sK3,sK2)
% 2.04/1.05      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.04/1.05      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_20,plain,
% 2.04/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.04/1.05      | ~ v1_funct_1(X0)
% 2.04/1.05      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.04/1.05      inference(cnf_transformation,[],[f58]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_25,negated_conjecture,
% 2.04/1.05      ( v1_funct_1(sK3) ),
% 2.04/1.05      inference(cnf_transformation,[],[f59]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_254,plain,
% 2.04/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.04/1.05      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 2.04/1.05      | sK3 != X0 ),
% 2.04/1.05      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_255,plain,
% 2.04/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.04/1.05      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 2.04/1.05      inference(unflattening,[status(thm)],[c_254]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_713,plain,
% 2.04/1.05      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 2.04/1.05      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.04/1.05      inference(predicate_to_equality,[status(thm)],[c_255]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_876,plain,
% 2.04/1.05      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 2.04/1.05      inference(superposition,[status(thm)],[c_714,c_713]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_894,plain,
% 2.04/1.05      ( k7_relat_1(sK3,sK2) != sK3
% 2.04/1.05      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.04/1.05      inference(demodulation,[status(thm)],[c_711,c_876]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_2456,plain,
% 2.04/1.05      ( sK1 = k1_xboole_0
% 2.04/1.05      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.04/1.05      inference(superposition,[status(thm)],[c_2449,c_894]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_2532,plain,
% 2.04/1.05      ( sK1 = k1_xboole_0
% 2.04/1.05      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.04/1.05      inference(superposition,[status(thm)],[c_2449,c_2456]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_2546,plain,
% 2.04/1.05      ( sK1 = k1_xboole_0 ),
% 2.04/1.05      inference(global_propositional_subsumption,
% 2.04/1.05                [status(thm)],
% 2.04/1.05                [c_2532,c_28]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_2562,plain,
% 2.04/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 2.04/1.05      inference(demodulation,[status(thm)],[c_2546,c_714]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_3,plain,
% 2.04/1.05      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.04/1.05      inference(cnf_transformation,[],[f66]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_2564,plain,
% 2.04/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.04/1.05      inference(demodulation,[status(thm)],[c_2562,c_3]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_1441,plain,
% 2.04/1.05      ( k7_relat_1(X0,X1) = X0
% 2.04/1.05      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.04/1.05      | v1_relat_1(X0) != iProver_top ),
% 2.04/1.05      inference(superposition,[status(thm)],[c_3,c_712]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_2700,plain,
% 2.04/1.05      ( k7_relat_1(sK3,X0) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 2.04/1.05      inference(superposition,[status(thm)],[c_2564,c_1441]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_3382,plain,
% 2.04/1.05      ( k7_relat_1(sK3,X0) = sK3 ),
% 2.04/1.05      inference(global_propositional_subsumption,
% 2.04/1.05                [status(thm)],
% 2.04/1.05                [c_2700,c_28,c_1081,c_1121,c_1203,c_1208]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_2559,plain,
% 2.04/1.05      ( k7_relat_1(sK3,sK2) != sK3
% 2.04/1.05      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 2.04/1.05      inference(demodulation,[status(thm)],[c_2546,c_894]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_2570,plain,
% 2.04/1.05      ( k7_relat_1(sK3,sK2) != sK3
% 2.04/1.05      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.04/1.05      inference(demodulation,[status(thm)],[c_2559,c_3]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_3390,plain,
% 2.04/1.05      ( sK3 != sK3
% 2.04/1.05      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.04/1.05      inference(demodulation,[status(thm)],[c_3382,c_2570]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(c_3397,plain,
% 2.04/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.04/1.05      inference(equality_resolution_simp,[status(thm)],[c_3390]) ).
% 2.04/1.05  
% 2.04/1.05  cnf(contradiction,plain,
% 2.04/1.05      ( $false ),
% 2.04/1.05      inference(minisat,[status(thm)],[c_3397,c_2564]) ).
% 2.04/1.05  
% 2.04/1.05  
% 2.04/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.04/1.05  
% 2.04/1.05  ------                               Statistics
% 2.04/1.05  
% 2.04/1.05  ------ General
% 2.04/1.05  
% 2.04/1.05  abstr_ref_over_cycles:                  0
% 2.04/1.05  abstr_ref_under_cycles:                 0
% 2.04/1.05  gc_basic_clause_elim:                   0
% 2.04/1.05  forced_gc_time:                         0
% 2.04/1.05  parsing_time:                           0.014
% 2.04/1.05  unif_index_cands_time:                  0.
% 2.04/1.05  unif_index_add_time:                    0.
% 2.04/1.05  orderings_time:                         0.
% 2.04/1.05  out_proof_time:                         0.009
% 2.04/1.05  total_time:                             0.17
% 2.04/1.05  num_of_symbols:                         49
% 2.04/1.05  num_of_terms:                           2980
% 2.04/1.05  
% 2.04/1.05  ------ Preprocessing
% 2.04/1.05  
% 2.04/1.05  num_of_splits:                          0
% 2.04/1.05  num_of_split_atoms:                     0
% 2.04/1.05  num_of_reused_defs:                     0
% 2.04/1.05  num_eq_ax_congr_red:                    11
% 2.04/1.05  num_of_sem_filtered_clauses:            1
% 2.04/1.05  num_of_subtypes:                        0
% 2.04/1.05  monotx_restored_types:                  0
% 2.04/1.05  sat_num_of_epr_types:                   0
% 2.04/1.05  sat_num_of_non_cyclic_types:            0
% 2.04/1.05  sat_guarded_non_collapsed_types:        0
% 2.04/1.05  num_pure_diseq_elim:                    0
% 2.04/1.05  simp_replaced_by:                       0
% 2.04/1.05  res_preprocessed:                       97
% 2.04/1.05  prep_upred:                             0
% 2.04/1.05  prep_unflattend:                        35
% 2.04/1.05  smt_new_axioms:                         0
% 2.04/1.05  pred_elim_cands:                        3
% 2.04/1.05  pred_elim:                              4
% 2.04/1.05  pred_elim_cl:                           8
% 2.04/1.05  pred_elim_cycles:                       6
% 2.04/1.05  merged_defs:                            0
% 2.04/1.05  merged_defs_ncl:                        0
% 2.04/1.05  bin_hyper_res:                          0
% 2.04/1.05  prep_cycles:                            4
% 2.04/1.05  pred_elim_time:                         0.005
% 2.04/1.05  splitting_time:                         0.
% 2.04/1.05  sem_filter_time:                        0.
% 2.04/1.05  monotx_time:                            0.001
% 2.04/1.05  subtype_inf_time:                       0.
% 2.04/1.05  
% 2.04/1.05  ------ Problem properties
% 2.04/1.05  
% 2.04/1.05  clauses:                                17
% 2.04/1.05  conjectures:                            2
% 2.04/1.05  epr:                                    3
% 2.04/1.05  horn:                                   14
% 2.04/1.05  ground:                                 6
% 2.04/1.05  unary:                                  6
% 2.04/1.05  binary:                                 4
% 2.04/1.05  lits:                                   36
% 2.04/1.05  lits_eq:                                17
% 2.04/1.05  fd_pure:                                0
% 2.04/1.05  fd_pseudo:                              0
% 2.04/1.05  fd_cond:                                1
% 2.04/1.05  fd_pseudo_cond:                         1
% 2.04/1.05  ac_symbols:                             0
% 2.04/1.05  
% 2.04/1.05  ------ Propositional Solver
% 2.04/1.05  
% 2.04/1.05  prop_solver_calls:                      30
% 2.04/1.05  prop_fast_solver_calls:                 619
% 2.04/1.05  smt_solver_calls:                       0
% 2.04/1.05  smt_fast_solver_calls:                  0
% 2.04/1.05  prop_num_of_clauses:                    1289
% 2.04/1.05  prop_preprocess_simplified:             3830
% 2.04/1.05  prop_fo_subsumed:                       10
% 2.04/1.05  prop_solver_time:                       0.
% 2.04/1.05  smt_solver_time:                        0.
% 2.04/1.05  smt_fast_solver_time:                   0.
% 2.04/1.05  prop_fast_solver_time:                  0.
% 2.04/1.05  prop_unsat_core_time:                   0.
% 2.04/1.05  
% 2.04/1.05  ------ QBF
% 2.04/1.05  
% 2.04/1.05  qbf_q_res:                              0
% 2.04/1.05  qbf_num_tautologies:                    0
% 2.04/1.05  qbf_prep_cycles:                        0
% 2.04/1.05  
% 2.04/1.05  ------ BMC1
% 2.04/1.05  
% 2.04/1.05  bmc1_current_bound:                     -1
% 2.04/1.05  bmc1_last_solved_bound:                 -1
% 2.04/1.05  bmc1_unsat_core_size:                   -1
% 2.04/1.05  bmc1_unsat_core_parents_size:           -1
% 2.04/1.05  bmc1_merge_next_fun:                    0
% 2.04/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.04/1.05  
% 2.04/1.05  ------ Instantiation
% 2.04/1.05  
% 2.04/1.05  inst_num_of_clauses:                    506
% 2.04/1.05  inst_num_in_passive:                    227
% 2.04/1.05  inst_num_in_active:                     251
% 2.04/1.05  inst_num_in_unprocessed:                28
% 2.04/1.05  inst_num_of_loops:                      300
% 2.04/1.05  inst_num_of_learning_restarts:          0
% 2.04/1.05  inst_num_moves_active_passive:          45
% 2.04/1.05  inst_lit_activity:                      0
% 2.04/1.05  inst_lit_activity_moves:                0
% 2.04/1.05  inst_num_tautologies:                   0
% 2.04/1.05  inst_num_prop_implied:                  0
% 2.04/1.05  inst_num_existing_simplified:           0
% 2.04/1.05  inst_num_eq_res_simplified:             0
% 2.04/1.05  inst_num_child_elim:                    0
% 2.04/1.05  inst_num_of_dismatching_blockings:      66
% 2.04/1.05  inst_num_of_non_proper_insts:           550
% 2.04/1.05  inst_num_of_duplicates:                 0
% 2.04/1.05  inst_inst_num_from_inst_to_res:         0
% 2.04/1.05  inst_dismatching_checking_time:         0.
% 2.04/1.05  
% 2.04/1.05  ------ Resolution
% 2.04/1.05  
% 2.04/1.05  res_num_of_clauses:                     0
% 2.04/1.05  res_num_in_passive:                     0
% 2.04/1.05  res_num_in_active:                      0
% 2.04/1.05  res_num_of_loops:                       101
% 2.04/1.05  res_forward_subset_subsumed:            51
% 2.04/1.05  res_backward_subset_subsumed:           2
% 2.04/1.05  res_forward_subsumed:                   0
% 2.04/1.05  res_backward_subsumed:                  0
% 2.04/1.05  res_forward_subsumption_resolution:     0
% 2.04/1.05  res_backward_subsumption_resolution:    0
% 2.04/1.05  res_clause_to_clause_subsumption:       144
% 2.04/1.05  res_orphan_elimination:                 0
% 2.04/1.05  res_tautology_del:                      30
% 2.04/1.05  res_num_eq_res_simplified:              0
% 2.04/1.05  res_num_sel_changes:                    0
% 2.04/1.05  res_moves_from_active_to_pass:          0
% 2.04/1.05  
% 2.04/1.05  ------ Superposition
% 2.04/1.05  
% 2.04/1.05  sup_time_total:                         0.
% 2.04/1.05  sup_time_generating:                    0.
% 2.04/1.05  sup_time_sim_full:                      0.
% 2.04/1.05  sup_time_sim_immed:                     0.
% 2.04/1.05  
% 2.04/1.05  sup_num_of_clauses:                     57
% 2.04/1.05  sup_num_in_active:                      31
% 2.04/1.05  sup_num_in_passive:                     26
% 2.04/1.05  sup_num_of_loops:                       59
% 2.04/1.05  sup_fw_superposition:                   47
% 2.04/1.05  sup_bw_superposition:                   43
% 2.04/1.05  sup_immediate_simplified:               27
% 2.04/1.05  sup_given_eliminated:                   1
% 2.04/1.05  comparisons_done:                       0
% 2.04/1.05  comparisons_avoided:                    18
% 2.04/1.05  
% 2.04/1.05  ------ Simplifications
% 2.04/1.05  
% 2.04/1.05  
% 2.04/1.05  sim_fw_subset_subsumed:                 16
% 2.04/1.05  sim_bw_subset_subsumed:                 14
% 2.04/1.05  sim_fw_subsumed:                        6
% 2.04/1.05  sim_bw_subsumed:                        2
% 2.04/1.05  sim_fw_subsumption_res:                 3
% 2.04/1.05  sim_bw_subsumption_res:                 1
% 2.04/1.05  sim_tautology_del:                      3
% 2.04/1.05  sim_eq_tautology_del:                   5
% 2.04/1.05  sim_eq_res_simp:                        2
% 2.04/1.05  sim_fw_demodulated:                     6
% 2.04/1.05  sim_bw_demodulated:                     21
% 2.04/1.05  sim_light_normalised:                   1
% 2.04/1.05  sim_joinable_taut:                      0
% 2.04/1.05  sim_joinable_simp:                      0
% 2.04/1.05  sim_ac_normalised:                      0
% 2.04/1.05  sim_smt_subsumption:                    0
% 2.04/1.05  
%------------------------------------------------------------------------------
