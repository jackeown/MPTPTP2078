%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:02 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 962 expanded)
%              Number of clauses        :   57 ( 320 expanded)
%              Number of leaves         :   12 ( 171 expanded)
%              Depth                    :   23
%              Number of atoms          :  326 (3467 expanded)
%              Number of equality atoms :  154 ( 814 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f35,plain,
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

fof(f36,plain,
    ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)
    & r1_tarski(sK0,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f35])).

fof(f60,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f23])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f19])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f61,plain,(
    ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f42])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1213,plain,
    ( r1_tarski(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_362,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_364,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_362,c_22])).

cnf(c_1212,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1215,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2091,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1212,c_1215])).

cnf(c_2281,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_364,c_2091])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1217,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1214,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_262,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_8,c_6])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_266,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_262,c_8,c_7,c_6])).

cnf(c_1210,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_2044,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_1210])).

cnf(c_3251,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_2044])).

cnf(c_3367,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | sK1 = k1_xboole_0
    | r1_tarski(sK0,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2281,c_3251])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1324,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1325,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1324])).

cnf(c_3685,plain,
    ( r1_tarski(sK0,X0) != iProver_top
    | sK1 = k1_xboole_0
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3367,c_27,c_1325])).

cnf(c_3686,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | sK1 = k1_xboole_0
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3685])).

cnf(c_3693,plain,
    ( k7_relat_1(sK3,sK2) = sK3
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1213,c_3686])).

cnf(c_10,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_20,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_303,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_304,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK3 != k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_1209,plain,
    ( sK3 != k2_partfun1(sK0,sK1,sK3,sK2)
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_247,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_248,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_1211,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_248])).

cnf(c_1352,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1212,c_1211])).

cnf(c_1365,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1209,c_1352])).

cnf(c_3700,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3693,c_1365])).

cnf(c_3805,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3693,c_3700])).

cnf(c_3821,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3805,c_27])).

cnf(c_3837,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3821,c_1212])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3839,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3837,c_3])).

cnf(c_1805,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1210])).

cnf(c_3979,plain,
    ( k7_relat_1(sK3,X0) = sK3 ),
    inference(superposition,[status(thm)],[c_3839,c_1805])).

cnf(c_3834,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3821,c_1365])).

cnf(c_3845,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3834,c_3])).

cnf(c_4150,plain,
    ( sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3979,c_3845])).

cnf(c_4151,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4150])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4151,c_3839])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:28:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.00/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.00  
% 3.00/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/1.00  
% 3.00/1.00  ------  iProver source info
% 3.00/1.00  
% 3.00/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.00/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/1.00  git: non_committed_changes: false
% 3.00/1.00  git: last_make_outside_of_git: false
% 3.00/1.00  
% 3.00/1.00  ------ 
% 3.00/1.00  
% 3.00/1.00  ------ Input Options
% 3.00/1.00  
% 3.00/1.00  --out_options                           all
% 3.00/1.00  --tptp_safe_out                         true
% 3.00/1.00  --problem_path                          ""
% 3.00/1.00  --include_path                          ""
% 3.00/1.00  --clausifier                            res/vclausify_rel
% 3.00/1.00  --clausifier_options                    --mode clausify
% 3.00/1.00  --stdin                                 false
% 3.00/1.00  --stats_out                             all
% 3.00/1.00  
% 3.00/1.00  ------ General Options
% 3.00/1.00  
% 3.00/1.00  --fof                                   false
% 3.00/1.00  --time_out_real                         305.
% 3.00/1.00  --time_out_virtual                      -1.
% 3.00/1.00  --symbol_type_check                     false
% 3.00/1.00  --clausify_out                          false
% 3.00/1.00  --sig_cnt_out                           false
% 3.00/1.01  --trig_cnt_out                          false
% 3.00/1.01  --trig_cnt_out_tolerance                1.
% 3.00/1.01  --trig_cnt_out_sk_spl                   false
% 3.00/1.01  --abstr_cl_out                          false
% 3.00/1.01  
% 3.00/1.01  ------ Global Options
% 3.00/1.01  
% 3.00/1.01  --schedule                              default
% 3.00/1.01  --add_important_lit                     false
% 3.00/1.01  --prop_solver_per_cl                    1000
% 3.00/1.01  --min_unsat_core                        false
% 3.00/1.01  --soft_assumptions                      false
% 3.00/1.01  --soft_lemma_size                       3
% 3.00/1.01  --prop_impl_unit_size                   0
% 3.00/1.01  --prop_impl_unit                        []
% 3.00/1.01  --share_sel_clauses                     true
% 3.00/1.01  --reset_solvers                         false
% 3.00/1.01  --bc_imp_inh                            [conj_cone]
% 3.00/1.01  --conj_cone_tolerance                   3.
% 3.00/1.01  --extra_neg_conj                        none
% 3.00/1.01  --large_theory_mode                     true
% 3.00/1.01  --prolific_symb_bound                   200
% 3.00/1.01  --lt_threshold                          2000
% 3.00/1.01  --clause_weak_htbl                      true
% 3.00/1.01  --gc_record_bc_elim                     false
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing Options
% 3.00/1.01  
% 3.00/1.01  --preprocessing_flag                    true
% 3.00/1.01  --time_out_prep_mult                    0.1
% 3.00/1.01  --splitting_mode                        input
% 3.00/1.01  --splitting_grd                         true
% 3.00/1.01  --splitting_cvd                         false
% 3.00/1.01  --splitting_cvd_svl                     false
% 3.00/1.01  --splitting_nvd                         32
% 3.00/1.01  --sub_typing                            true
% 3.00/1.01  --prep_gs_sim                           true
% 3.00/1.01  --prep_unflatten                        true
% 3.00/1.01  --prep_res_sim                          true
% 3.00/1.01  --prep_upred                            true
% 3.00/1.01  --prep_sem_filter                       exhaustive
% 3.00/1.01  --prep_sem_filter_out                   false
% 3.00/1.01  --pred_elim                             true
% 3.00/1.01  --res_sim_input                         true
% 3.00/1.01  --eq_ax_congr_red                       true
% 3.00/1.01  --pure_diseq_elim                       true
% 3.00/1.01  --brand_transform                       false
% 3.00/1.01  --non_eq_to_eq                          false
% 3.00/1.01  --prep_def_merge                        true
% 3.00/1.01  --prep_def_merge_prop_impl              false
% 3.00/1.01  --prep_def_merge_mbd                    true
% 3.00/1.01  --prep_def_merge_tr_red                 false
% 3.00/1.01  --prep_def_merge_tr_cl                  false
% 3.00/1.01  --smt_preprocessing                     true
% 3.00/1.01  --smt_ac_axioms                         fast
% 3.00/1.01  --preprocessed_out                      false
% 3.00/1.01  --preprocessed_stats                    false
% 3.00/1.01  
% 3.00/1.01  ------ Abstraction refinement Options
% 3.00/1.01  
% 3.00/1.01  --abstr_ref                             []
% 3.00/1.01  --abstr_ref_prep                        false
% 3.00/1.01  --abstr_ref_until_sat                   false
% 3.00/1.01  --abstr_ref_sig_restrict                funpre
% 3.00/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.01  --abstr_ref_under                       []
% 3.00/1.01  
% 3.00/1.01  ------ SAT Options
% 3.00/1.01  
% 3.00/1.01  --sat_mode                              false
% 3.00/1.01  --sat_fm_restart_options                ""
% 3.00/1.01  --sat_gr_def                            false
% 3.00/1.01  --sat_epr_types                         true
% 3.00/1.01  --sat_non_cyclic_types                  false
% 3.00/1.01  --sat_finite_models                     false
% 3.00/1.01  --sat_fm_lemmas                         false
% 3.00/1.01  --sat_fm_prep                           false
% 3.00/1.01  --sat_fm_uc_incr                        true
% 3.00/1.01  --sat_out_model                         small
% 3.00/1.01  --sat_out_clauses                       false
% 3.00/1.01  
% 3.00/1.01  ------ QBF Options
% 3.00/1.01  
% 3.00/1.01  --qbf_mode                              false
% 3.00/1.01  --qbf_elim_univ                         false
% 3.00/1.01  --qbf_dom_inst                          none
% 3.00/1.01  --qbf_dom_pre_inst                      false
% 3.00/1.01  --qbf_sk_in                             false
% 3.00/1.01  --qbf_pred_elim                         true
% 3.00/1.01  --qbf_split                             512
% 3.00/1.01  
% 3.00/1.01  ------ BMC1 Options
% 3.00/1.01  
% 3.00/1.01  --bmc1_incremental                      false
% 3.00/1.01  --bmc1_axioms                           reachable_all
% 3.00/1.01  --bmc1_min_bound                        0
% 3.00/1.01  --bmc1_max_bound                        -1
% 3.00/1.01  --bmc1_max_bound_default                -1
% 3.00/1.01  --bmc1_symbol_reachability              true
% 3.00/1.01  --bmc1_property_lemmas                  false
% 3.00/1.01  --bmc1_k_induction                      false
% 3.00/1.01  --bmc1_non_equiv_states                 false
% 3.00/1.01  --bmc1_deadlock                         false
% 3.00/1.01  --bmc1_ucm                              false
% 3.00/1.01  --bmc1_add_unsat_core                   none
% 3.00/1.01  --bmc1_unsat_core_children              false
% 3.00/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.01  --bmc1_out_stat                         full
% 3.00/1.01  --bmc1_ground_init                      false
% 3.00/1.01  --bmc1_pre_inst_next_state              false
% 3.00/1.01  --bmc1_pre_inst_state                   false
% 3.00/1.01  --bmc1_pre_inst_reach_state             false
% 3.00/1.01  --bmc1_out_unsat_core                   false
% 3.00/1.01  --bmc1_aig_witness_out                  false
% 3.00/1.01  --bmc1_verbose                          false
% 3.00/1.01  --bmc1_dump_clauses_tptp                false
% 3.00/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.01  --bmc1_dump_file                        -
% 3.00/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.01  --bmc1_ucm_extend_mode                  1
% 3.00/1.01  --bmc1_ucm_init_mode                    2
% 3.00/1.01  --bmc1_ucm_cone_mode                    none
% 3.00/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.01  --bmc1_ucm_relax_model                  4
% 3.00/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.01  --bmc1_ucm_layered_model                none
% 3.00/1.01  --bmc1_ucm_max_lemma_size               10
% 3.00/1.01  
% 3.00/1.01  ------ AIG Options
% 3.00/1.01  
% 3.00/1.01  --aig_mode                              false
% 3.00/1.01  
% 3.00/1.01  ------ Instantiation Options
% 3.00/1.01  
% 3.00/1.01  --instantiation_flag                    true
% 3.00/1.01  --inst_sos_flag                         false
% 3.00/1.01  --inst_sos_phase                        true
% 3.00/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel_side                     num_symb
% 3.00/1.01  --inst_solver_per_active                1400
% 3.00/1.01  --inst_solver_calls_frac                1.
% 3.00/1.01  --inst_passive_queue_type               priority_queues
% 3.00/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.01  --inst_passive_queues_freq              [25;2]
% 3.00/1.01  --inst_dismatching                      true
% 3.00/1.01  --inst_eager_unprocessed_to_passive     true
% 3.00/1.01  --inst_prop_sim_given                   true
% 3.00/1.01  --inst_prop_sim_new                     false
% 3.00/1.01  --inst_subs_new                         false
% 3.00/1.01  --inst_eq_res_simp                      false
% 3.00/1.01  --inst_subs_given                       false
% 3.00/1.01  --inst_orphan_elimination               true
% 3.00/1.01  --inst_learning_loop_flag               true
% 3.00/1.01  --inst_learning_start                   3000
% 3.00/1.01  --inst_learning_factor                  2
% 3.00/1.01  --inst_start_prop_sim_after_learn       3
% 3.00/1.01  --inst_sel_renew                        solver
% 3.00/1.01  --inst_lit_activity_flag                true
% 3.00/1.01  --inst_restr_to_given                   false
% 3.00/1.01  --inst_activity_threshold               500
% 3.00/1.01  --inst_out_proof                        true
% 3.00/1.01  
% 3.00/1.01  ------ Resolution Options
% 3.00/1.01  
% 3.00/1.01  --resolution_flag                       true
% 3.00/1.01  --res_lit_sel                           adaptive
% 3.00/1.01  --res_lit_sel_side                      none
% 3.00/1.01  --res_ordering                          kbo
% 3.00/1.01  --res_to_prop_solver                    active
% 3.00/1.01  --res_prop_simpl_new                    false
% 3.00/1.01  --res_prop_simpl_given                  true
% 3.00/1.01  --res_passive_queue_type                priority_queues
% 3.00/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.01  --res_passive_queues_freq               [15;5]
% 3.00/1.01  --res_forward_subs                      full
% 3.00/1.01  --res_backward_subs                     full
% 3.00/1.01  --res_forward_subs_resolution           true
% 3.00/1.01  --res_backward_subs_resolution          true
% 3.00/1.01  --res_orphan_elimination                true
% 3.00/1.01  --res_time_limit                        2.
% 3.00/1.01  --res_out_proof                         true
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Options
% 3.00/1.01  
% 3.00/1.01  --superposition_flag                    true
% 3.00/1.01  --sup_passive_queue_type                priority_queues
% 3.00/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.01  --demod_completeness_check              fast
% 3.00/1.01  --demod_use_ground                      true
% 3.00/1.01  --sup_to_prop_solver                    passive
% 3.00/1.01  --sup_prop_simpl_new                    true
% 3.00/1.01  --sup_prop_simpl_given                  true
% 3.00/1.01  --sup_fun_splitting                     false
% 3.00/1.01  --sup_smt_interval                      50000
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Simplification Setup
% 3.00/1.01  
% 3.00/1.01  --sup_indices_passive                   []
% 3.00/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_full_bw                           [BwDemod]
% 3.00/1.01  --sup_immed_triv                        [TrivRules]
% 3.00/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_immed_bw_main                     []
% 3.00/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  
% 3.00/1.01  ------ Combination Options
% 3.00/1.01  
% 3.00/1.01  --comb_res_mult                         3
% 3.00/1.01  --comb_sup_mult                         2
% 3.00/1.01  --comb_inst_mult                        10
% 3.00/1.01  
% 3.00/1.01  ------ Debug Options
% 3.00/1.01  
% 3.00/1.01  --dbg_backtrace                         false
% 3.00/1.01  --dbg_dump_prop_clauses                 false
% 3.00/1.01  --dbg_dump_prop_clauses_file            -
% 3.00/1.01  --dbg_out_stat                          false
% 3.00/1.01  ------ Parsing...
% 3.00/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/1.01  ------ Proving...
% 3.00/1.01  ------ Problem Properties 
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  clauses                                 16
% 3.00/1.01  conjectures                             2
% 3.00/1.01  EPR                                     3
% 3.00/1.01  Horn                                    13
% 3.00/1.01  unary                                   5
% 3.00/1.01  binary                                  6
% 3.00/1.01  lits                                    34
% 3.00/1.01  lits eq                                 17
% 3.00/1.01  fd_pure                                 0
% 3.00/1.01  fd_pseudo                               0
% 3.00/1.01  fd_cond                                 1
% 3.00/1.01  fd_pseudo_cond                          1
% 3.00/1.01  AC symbols                              0
% 3.00/1.01  
% 3.00/1.01  ------ Schedule dynamic 5 is on 
% 3.00/1.01  
% 3.00/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  ------ 
% 3.00/1.01  Current options:
% 3.00/1.01  ------ 
% 3.00/1.01  
% 3.00/1.01  ------ Input Options
% 3.00/1.01  
% 3.00/1.01  --out_options                           all
% 3.00/1.01  --tptp_safe_out                         true
% 3.00/1.01  --problem_path                          ""
% 3.00/1.01  --include_path                          ""
% 3.00/1.01  --clausifier                            res/vclausify_rel
% 3.00/1.01  --clausifier_options                    --mode clausify
% 3.00/1.01  --stdin                                 false
% 3.00/1.01  --stats_out                             all
% 3.00/1.01  
% 3.00/1.01  ------ General Options
% 3.00/1.01  
% 3.00/1.01  --fof                                   false
% 3.00/1.01  --time_out_real                         305.
% 3.00/1.01  --time_out_virtual                      -1.
% 3.00/1.01  --symbol_type_check                     false
% 3.00/1.01  --clausify_out                          false
% 3.00/1.01  --sig_cnt_out                           false
% 3.00/1.01  --trig_cnt_out                          false
% 3.00/1.01  --trig_cnt_out_tolerance                1.
% 3.00/1.01  --trig_cnt_out_sk_spl                   false
% 3.00/1.01  --abstr_cl_out                          false
% 3.00/1.01  
% 3.00/1.01  ------ Global Options
% 3.00/1.01  
% 3.00/1.01  --schedule                              default
% 3.00/1.01  --add_important_lit                     false
% 3.00/1.01  --prop_solver_per_cl                    1000
% 3.00/1.01  --min_unsat_core                        false
% 3.00/1.01  --soft_assumptions                      false
% 3.00/1.01  --soft_lemma_size                       3
% 3.00/1.01  --prop_impl_unit_size                   0
% 3.00/1.01  --prop_impl_unit                        []
% 3.00/1.01  --share_sel_clauses                     true
% 3.00/1.01  --reset_solvers                         false
% 3.00/1.01  --bc_imp_inh                            [conj_cone]
% 3.00/1.01  --conj_cone_tolerance                   3.
% 3.00/1.01  --extra_neg_conj                        none
% 3.00/1.01  --large_theory_mode                     true
% 3.00/1.01  --prolific_symb_bound                   200
% 3.00/1.01  --lt_threshold                          2000
% 3.00/1.01  --clause_weak_htbl                      true
% 3.00/1.01  --gc_record_bc_elim                     false
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing Options
% 3.00/1.01  
% 3.00/1.01  --preprocessing_flag                    true
% 3.00/1.01  --time_out_prep_mult                    0.1
% 3.00/1.01  --splitting_mode                        input
% 3.00/1.01  --splitting_grd                         true
% 3.00/1.01  --splitting_cvd                         false
% 3.00/1.01  --splitting_cvd_svl                     false
% 3.00/1.01  --splitting_nvd                         32
% 3.00/1.01  --sub_typing                            true
% 3.00/1.01  --prep_gs_sim                           true
% 3.00/1.01  --prep_unflatten                        true
% 3.00/1.01  --prep_res_sim                          true
% 3.00/1.01  --prep_upred                            true
% 3.00/1.01  --prep_sem_filter                       exhaustive
% 3.00/1.01  --prep_sem_filter_out                   false
% 3.00/1.01  --pred_elim                             true
% 3.00/1.01  --res_sim_input                         true
% 3.00/1.01  --eq_ax_congr_red                       true
% 3.00/1.01  --pure_diseq_elim                       true
% 3.00/1.01  --brand_transform                       false
% 3.00/1.01  --non_eq_to_eq                          false
% 3.00/1.01  --prep_def_merge                        true
% 3.00/1.01  --prep_def_merge_prop_impl              false
% 3.00/1.01  --prep_def_merge_mbd                    true
% 3.00/1.01  --prep_def_merge_tr_red                 false
% 3.00/1.01  --prep_def_merge_tr_cl                  false
% 3.00/1.01  --smt_preprocessing                     true
% 3.00/1.01  --smt_ac_axioms                         fast
% 3.00/1.01  --preprocessed_out                      false
% 3.00/1.01  --preprocessed_stats                    false
% 3.00/1.01  
% 3.00/1.01  ------ Abstraction refinement Options
% 3.00/1.01  
% 3.00/1.01  --abstr_ref                             []
% 3.00/1.01  --abstr_ref_prep                        false
% 3.00/1.01  --abstr_ref_until_sat                   false
% 3.00/1.01  --abstr_ref_sig_restrict                funpre
% 3.00/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.01  --abstr_ref_under                       []
% 3.00/1.01  
% 3.00/1.01  ------ SAT Options
% 3.00/1.01  
% 3.00/1.01  --sat_mode                              false
% 3.00/1.01  --sat_fm_restart_options                ""
% 3.00/1.01  --sat_gr_def                            false
% 3.00/1.01  --sat_epr_types                         true
% 3.00/1.01  --sat_non_cyclic_types                  false
% 3.00/1.01  --sat_finite_models                     false
% 3.00/1.01  --sat_fm_lemmas                         false
% 3.00/1.01  --sat_fm_prep                           false
% 3.00/1.01  --sat_fm_uc_incr                        true
% 3.00/1.01  --sat_out_model                         small
% 3.00/1.01  --sat_out_clauses                       false
% 3.00/1.01  
% 3.00/1.01  ------ QBF Options
% 3.00/1.01  
% 3.00/1.01  --qbf_mode                              false
% 3.00/1.01  --qbf_elim_univ                         false
% 3.00/1.01  --qbf_dom_inst                          none
% 3.00/1.01  --qbf_dom_pre_inst                      false
% 3.00/1.01  --qbf_sk_in                             false
% 3.00/1.01  --qbf_pred_elim                         true
% 3.00/1.01  --qbf_split                             512
% 3.00/1.01  
% 3.00/1.01  ------ BMC1 Options
% 3.00/1.01  
% 3.00/1.01  --bmc1_incremental                      false
% 3.00/1.01  --bmc1_axioms                           reachable_all
% 3.00/1.01  --bmc1_min_bound                        0
% 3.00/1.01  --bmc1_max_bound                        -1
% 3.00/1.01  --bmc1_max_bound_default                -1
% 3.00/1.01  --bmc1_symbol_reachability              true
% 3.00/1.01  --bmc1_property_lemmas                  false
% 3.00/1.01  --bmc1_k_induction                      false
% 3.00/1.01  --bmc1_non_equiv_states                 false
% 3.00/1.01  --bmc1_deadlock                         false
% 3.00/1.01  --bmc1_ucm                              false
% 3.00/1.01  --bmc1_add_unsat_core                   none
% 3.00/1.01  --bmc1_unsat_core_children              false
% 3.00/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.01  --bmc1_out_stat                         full
% 3.00/1.01  --bmc1_ground_init                      false
% 3.00/1.01  --bmc1_pre_inst_next_state              false
% 3.00/1.01  --bmc1_pre_inst_state                   false
% 3.00/1.01  --bmc1_pre_inst_reach_state             false
% 3.00/1.01  --bmc1_out_unsat_core                   false
% 3.00/1.01  --bmc1_aig_witness_out                  false
% 3.00/1.01  --bmc1_verbose                          false
% 3.00/1.01  --bmc1_dump_clauses_tptp                false
% 3.00/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.01  --bmc1_dump_file                        -
% 3.00/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.01  --bmc1_ucm_extend_mode                  1
% 3.00/1.01  --bmc1_ucm_init_mode                    2
% 3.00/1.01  --bmc1_ucm_cone_mode                    none
% 3.00/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.01  --bmc1_ucm_relax_model                  4
% 3.00/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.01  --bmc1_ucm_layered_model                none
% 3.00/1.01  --bmc1_ucm_max_lemma_size               10
% 3.00/1.01  
% 3.00/1.01  ------ AIG Options
% 3.00/1.01  
% 3.00/1.01  --aig_mode                              false
% 3.00/1.01  
% 3.00/1.01  ------ Instantiation Options
% 3.00/1.01  
% 3.00/1.01  --instantiation_flag                    true
% 3.00/1.01  --inst_sos_flag                         false
% 3.00/1.01  --inst_sos_phase                        true
% 3.00/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel_side                     none
% 3.00/1.01  --inst_solver_per_active                1400
% 3.00/1.01  --inst_solver_calls_frac                1.
% 3.00/1.01  --inst_passive_queue_type               priority_queues
% 3.00/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.01  --inst_passive_queues_freq              [25;2]
% 3.00/1.01  --inst_dismatching                      true
% 3.00/1.01  --inst_eager_unprocessed_to_passive     true
% 3.00/1.01  --inst_prop_sim_given                   true
% 3.00/1.01  --inst_prop_sim_new                     false
% 3.00/1.01  --inst_subs_new                         false
% 3.00/1.01  --inst_eq_res_simp                      false
% 3.00/1.01  --inst_subs_given                       false
% 3.00/1.01  --inst_orphan_elimination               true
% 3.00/1.01  --inst_learning_loop_flag               true
% 3.00/1.01  --inst_learning_start                   3000
% 3.00/1.01  --inst_learning_factor                  2
% 3.00/1.01  --inst_start_prop_sim_after_learn       3
% 3.00/1.01  --inst_sel_renew                        solver
% 3.00/1.01  --inst_lit_activity_flag                true
% 3.00/1.01  --inst_restr_to_given                   false
% 3.00/1.01  --inst_activity_threshold               500
% 3.00/1.01  --inst_out_proof                        true
% 3.00/1.01  
% 3.00/1.01  ------ Resolution Options
% 3.00/1.01  
% 3.00/1.01  --resolution_flag                       false
% 3.00/1.01  --res_lit_sel                           adaptive
% 3.00/1.01  --res_lit_sel_side                      none
% 3.00/1.01  --res_ordering                          kbo
% 3.00/1.01  --res_to_prop_solver                    active
% 3.00/1.01  --res_prop_simpl_new                    false
% 3.00/1.01  --res_prop_simpl_given                  true
% 3.00/1.01  --res_passive_queue_type                priority_queues
% 3.00/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.01  --res_passive_queues_freq               [15;5]
% 3.00/1.01  --res_forward_subs                      full
% 3.00/1.01  --res_backward_subs                     full
% 3.00/1.01  --res_forward_subs_resolution           true
% 3.00/1.01  --res_backward_subs_resolution          true
% 3.00/1.01  --res_orphan_elimination                true
% 3.00/1.01  --res_time_limit                        2.
% 3.00/1.01  --res_out_proof                         true
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Options
% 3.00/1.01  
% 3.00/1.01  --superposition_flag                    true
% 3.00/1.01  --sup_passive_queue_type                priority_queues
% 3.00/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.01  --demod_completeness_check              fast
% 3.00/1.01  --demod_use_ground                      true
% 3.00/1.01  --sup_to_prop_solver                    passive
% 3.00/1.01  --sup_prop_simpl_new                    true
% 3.00/1.01  --sup_prop_simpl_given                  true
% 3.00/1.01  --sup_fun_splitting                     false
% 3.00/1.01  --sup_smt_interval                      50000
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Simplification Setup
% 3.00/1.01  
% 3.00/1.01  --sup_indices_passive                   []
% 3.00/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_full_bw                           [BwDemod]
% 3.00/1.01  --sup_immed_triv                        [TrivRules]
% 3.00/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_immed_bw_main                     []
% 3.00/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  
% 3.00/1.01  ------ Combination Options
% 3.00/1.01  
% 3.00/1.01  --comb_res_mult                         3
% 3.00/1.01  --comb_sup_mult                         2
% 3.00/1.01  --comb_inst_mult                        10
% 3.00/1.01  
% 3.00/1.01  ------ Debug Options
% 3.00/1.01  
% 3.00/1.01  --dbg_backtrace                         false
% 3.00/1.01  --dbg_dump_prop_clauses                 false
% 3.00/1.01  --dbg_dump_prop_clauses_file            -
% 3.00/1.01  --dbg_out_stat                          false
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  ------ Proving...
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  % SZS status Theorem for theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  fof(f11,conjecture,(
% 3.00/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f12,negated_conjecture,(
% 3.00/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 3.00/1.01    inference(negated_conjecture,[],[f11])).
% 3.00/1.01  
% 3.00/1.01  fof(f27,plain,(
% 3.00/1.01    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.00/1.01    inference(ennf_transformation,[],[f12])).
% 3.00/1.01  
% 3.00/1.01  fof(f28,plain,(
% 3.00/1.01    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.00/1.01    inference(flattening,[],[f27])).
% 3.00/1.01  
% 3.00/1.01  fof(f35,plain,(
% 3.00/1.01    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) & r1_tarski(sK0,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.00/1.01    introduced(choice_axiom,[])).
% 3.00/1.01  
% 3.00/1.01  fof(f36,plain,(
% 3.00/1.01    ~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) & r1_tarski(sK0,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.00/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f35])).
% 3.00/1.01  
% 3.00/1.01  fof(f60,plain,(
% 3.00/1.01    r1_tarski(sK0,sK2)),
% 3.00/1.01    inference(cnf_transformation,[],[f36])).
% 3.00/1.01  
% 3.00/1.01  fof(f9,axiom,(
% 3.00/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f23,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(ennf_transformation,[],[f9])).
% 3.00/1.01  
% 3.00/1.01  fof(f24,plain,(
% 3.00/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(flattening,[],[f23])).
% 3.00/1.01  
% 3.00/1.01  fof(f34,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(nnf_transformation,[],[f24])).
% 3.00/1.01  
% 3.00/1.01  fof(f50,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f34])).
% 3.00/1.01  
% 3.00/1.01  fof(f58,plain,(
% 3.00/1.01    v1_funct_2(sK3,sK0,sK1)),
% 3.00/1.01    inference(cnf_transformation,[],[f36])).
% 3.00/1.01  
% 3.00/1.01  fof(f59,plain,(
% 3.00/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.00/1.01    inference(cnf_transformation,[],[f36])).
% 3.00/1.01  
% 3.00/1.01  fof(f6,axiom,(
% 3.00/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f18,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(ennf_transformation,[],[f6])).
% 3.00/1.01  
% 3.00/1.01  fof(f46,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f18])).
% 3.00/1.01  
% 3.00/1.01  fof(f1,axiom,(
% 3.00/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f29,plain,(
% 3.00/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.00/1.01    inference(nnf_transformation,[],[f1])).
% 3.00/1.01  
% 3.00/1.01  fof(f30,plain,(
% 3.00/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.00/1.01    inference(flattening,[],[f29])).
% 3.00/1.01  
% 3.00/1.01  fof(f37,plain,(
% 3.00/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.00/1.01    inference(cnf_transformation,[],[f30])).
% 3.00/1.01  
% 3.00/1.01  fof(f63,plain,(
% 3.00/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.00/1.01    inference(equality_resolution,[],[f37])).
% 3.00/1.01  
% 3.00/1.01  fof(f8,axiom,(
% 3.00/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f21,plain,(
% 3.00/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.00/1.01    inference(ennf_transformation,[],[f8])).
% 3.00/1.01  
% 3.00/1.01  fof(f22,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.00/1.01    inference(flattening,[],[f21])).
% 3.00/1.01  
% 3.00/1.01  fof(f49,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f22])).
% 3.00/1.01  
% 3.00/1.01  fof(f5,axiom,(
% 3.00/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f13,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.00/1.01    inference(pure_predicate_removal,[],[f5])).
% 3.00/1.01  
% 3.00/1.01  fof(f17,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(ennf_transformation,[],[f13])).
% 3.00/1.01  
% 3.00/1.01  fof(f45,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f17])).
% 3.00/1.01  
% 3.00/1.01  fof(f3,axiom,(
% 3.00/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f14,plain,(
% 3.00/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.00/1.01    inference(ennf_transformation,[],[f3])).
% 3.00/1.01  
% 3.00/1.01  fof(f15,plain,(
% 3.00/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.00/1.01    inference(flattening,[],[f14])).
% 3.00/1.01  
% 3.00/1.01  fof(f43,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f15])).
% 3.00/1.01  
% 3.00/1.01  fof(f4,axiom,(
% 3.00/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f16,plain,(
% 3.00/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(ennf_transformation,[],[f4])).
% 3.00/1.01  
% 3.00/1.01  fof(f44,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f16])).
% 3.00/1.01  
% 3.00/1.01  fof(f7,axiom,(
% 3.00/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f19,plain,(
% 3.00/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.00/1.01    inference(ennf_transformation,[],[f7])).
% 3.00/1.01  
% 3.00/1.01  fof(f20,plain,(
% 3.00/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(flattening,[],[f19])).
% 3.00/1.01  
% 3.00/1.01  fof(f33,plain,(
% 3.00/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(nnf_transformation,[],[f20])).
% 3.00/1.01  
% 3.00/1.01  fof(f48,plain,(
% 3.00/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f33])).
% 3.00/1.01  
% 3.00/1.01  fof(f66,plain,(
% 3.00/1.01    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.01    inference(equality_resolution,[],[f48])).
% 3.00/1.01  
% 3.00/1.01  fof(f61,plain,(
% 3.00/1.01    ~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)),
% 3.00/1.01    inference(cnf_transformation,[],[f36])).
% 3.00/1.01  
% 3.00/1.01  fof(f10,axiom,(
% 3.00/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f25,plain,(
% 3.00/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.00/1.01    inference(ennf_transformation,[],[f10])).
% 3.00/1.01  
% 3.00/1.01  fof(f26,plain,(
% 3.00/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.00/1.01    inference(flattening,[],[f25])).
% 3.00/1.01  
% 3.00/1.01  fof(f56,plain,(
% 3.00/1.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f26])).
% 3.00/1.01  
% 3.00/1.01  fof(f57,plain,(
% 3.00/1.01    v1_funct_1(sK3)),
% 3.00/1.01    inference(cnf_transformation,[],[f36])).
% 3.00/1.01  
% 3.00/1.01  fof(f2,axiom,(
% 3.00/1.01    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f31,plain,(
% 3.00/1.01    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.00/1.01    inference(nnf_transformation,[],[f2])).
% 3.00/1.01  
% 3.00/1.01  fof(f32,plain,(
% 3.00/1.01    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.00/1.01    inference(flattening,[],[f31])).
% 3.00/1.01  
% 3.00/1.01  fof(f42,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.00/1.01    inference(cnf_transformation,[],[f32])).
% 3.00/1.01  
% 3.00/1.01  fof(f64,plain,(
% 3.00/1.01    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.00/1.01    inference(equality_resolution,[],[f42])).
% 3.00/1.01  
% 3.00/1.01  cnf(c_21,negated_conjecture,
% 3.00/1.01      ( r1_tarski(sK0,sK2) ),
% 3.00/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1213,plain,
% 3.00/1.01      ( r1_tarski(sK0,sK2) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_18,plain,
% 3.00/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.00/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.00/1.01      | k1_xboole_0 = X2 ),
% 3.00/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_23,negated_conjecture,
% 3.00/1.01      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.00/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_361,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.00/1.01      | sK3 != X0
% 3.00/1.01      | sK1 != X2
% 3.00/1.01      | sK0 != X1
% 3.00/1.01      | k1_xboole_0 = X2 ),
% 3.00/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_362,plain,
% 3.00/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.00/1.01      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.00/1.01      | k1_xboole_0 = sK1 ),
% 3.00/1.01      inference(unflattening,[status(thm)],[c_361]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_22,negated_conjecture,
% 3.00/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.00/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_364,plain,
% 3.00/1.01      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_362,c_22]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1212,plain,
% 3.00/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_9,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1215,plain,
% 3.00/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.00/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2091,plain,
% 3.00/1.01      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1212,c_1215]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2281,plain,
% 3.00/1.01      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_364,c_2091]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2,plain,
% 3.00/1.01      ( r1_tarski(X0,X0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1217,plain,
% 3.00/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_12,plain,
% 3.00/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.00/1.01      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.00/1.01      | ~ v1_relat_1(X0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1214,plain,
% 3.00/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.00/1.01      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.00/1.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.00/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_8,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | v4_relat_1(X0,X1) ),
% 3.00/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_6,plain,
% 3.00/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.00/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_262,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | ~ v1_relat_1(X0)
% 3.00/1.01      | k7_relat_1(X0,X1) = X0 ),
% 3.00/1.01      inference(resolution,[status(thm)],[c_8,c_6]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_7,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | v1_relat_1(X0) ),
% 3.00/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_266,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | k7_relat_1(X0,X1) = X0 ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_262,c_8,c_7,c_6]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1210,plain,
% 3.00/1.01      ( k7_relat_1(X0,X1) = X0
% 3.00/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_266]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_2044,plain,
% 3.00/1.01      ( k7_relat_1(X0,X1) = X0
% 3.00/1.01      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.00/1.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.00/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1214,c_1210]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3251,plain,
% 3.00/1.01      ( k7_relat_1(X0,X1) = X0
% 3.00/1.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.00/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1217,c_2044]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3367,plain,
% 3.00/1.01      ( k7_relat_1(sK3,X0) = sK3
% 3.00/1.01      | sK1 = k1_xboole_0
% 3.00/1.01      | r1_tarski(sK0,X0) != iProver_top
% 3.00/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_2281,c_3251]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_27,plain,
% 3.00/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1324,plain,
% 3.00/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.00/1.01      | v1_relat_1(sK3) ),
% 3.00/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1325,plain,
% 3.00/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.00/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_1324]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3685,plain,
% 3.00/1.01      ( r1_tarski(sK0,X0) != iProver_top
% 3.00/1.01      | sK1 = k1_xboole_0
% 3.00/1.01      | k7_relat_1(sK3,X0) = sK3 ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_3367,c_27,c_1325]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3686,plain,
% 3.00/1.01      ( k7_relat_1(sK3,X0) = sK3
% 3.00/1.01      | sK1 = k1_xboole_0
% 3.00/1.01      | r1_tarski(sK0,X0) != iProver_top ),
% 3.00/1.01      inference(renaming,[status(thm)],[c_3685]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3693,plain,
% 3.00/1.01      ( k7_relat_1(sK3,sK2) = sK3 | sK1 = k1_xboole_0 ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1213,c_3686]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_10,plain,
% 3.00/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 3.00/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.00/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_20,negated_conjecture,
% 3.00/1.01      ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
% 3.00/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_303,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.00/1.01      | sK3 != X0
% 3.00/1.01      | sK1 != X2
% 3.00/1.01      | sK0 != X1 ),
% 3.00/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_304,plain,
% 3.00/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.00/1.01      | sK3 != k2_partfun1(sK0,sK1,sK3,sK2) ),
% 3.00/1.01      inference(unflattening,[status(thm)],[c_303]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1209,plain,
% 3.00/1.01      ( sK3 != k2_partfun1(sK0,sK1,sK3,sK2)
% 3.00/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_19,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | ~ v1_funct_1(X0)
% 3.00/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.00/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_24,negated_conjecture,
% 3.00/1.01      ( v1_funct_1(sK3) ),
% 3.00/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_247,plain,
% 3.00/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 3.00/1.01      | sK3 != X0 ),
% 3.00/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_248,plain,
% 3.00/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.00/1.01      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.00/1.01      inference(unflattening,[status(thm)],[c_247]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1211,plain,
% 3.00/1.01      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 3.00/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.00/1.01      inference(predicate_to_equality,[status(thm)],[c_248]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1352,plain,
% 3.00/1.01      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_1212,c_1211]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1365,plain,
% 3.00/1.01      ( k7_relat_1(sK3,sK2) != sK3
% 3.00/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_1209,c_1352]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3700,plain,
% 3.00/1.01      ( sK1 = k1_xboole_0
% 3.00/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_3693,c_1365]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3805,plain,
% 3.00/1.01      ( sK1 = k1_xboole_0
% 3.00/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_3693,c_3700]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3821,plain,
% 3.00/1.01      ( sK1 = k1_xboole_0 ),
% 3.00/1.01      inference(global_propositional_subsumption,
% 3.00/1.01                [status(thm)],
% 3.00/1.01                [c_3805,c_27]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3837,plain,
% 3.00/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_3821,c_1212]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3,plain,
% 3.00/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.00/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3839,plain,
% 3.00/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_3837,c_3]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_1805,plain,
% 3.00/1.01      ( k7_relat_1(X0,X1) = X0
% 3.00/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_3,c_1210]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3979,plain,
% 3.00/1.01      ( k7_relat_1(sK3,X0) = sK3 ),
% 3.00/1.01      inference(superposition,[status(thm)],[c_3839,c_1805]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3834,plain,
% 3.00/1.01      ( k7_relat_1(sK3,sK2) != sK3
% 3.00/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_3821,c_1365]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_3845,plain,
% 3.00/1.01      ( k7_relat_1(sK3,sK2) != sK3
% 3.00/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_3834,c_3]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4150,plain,
% 3.00/1.01      ( sK3 != sK3
% 3.00/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.00/1.01      inference(demodulation,[status(thm)],[c_3979,c_3845]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(c_4151,plain,
% 3.00/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.00/1.01      inference(equality_resolution_simp,[status(thm)],[c_4150]) ).
% 3.00/1.01  
% 3.00/1.01  cnf(contradiction,plain,
% 3.00/1.01      ( $false ),
% 3.00/1.01      inference(minisat,[status(thm)],[c_4151,c_3839]) ).
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  ------                               Statistics
% 3.00/1.01  
% 3.00/1.01  ------ General
% 3.00/1.01  
% 3.00/1.01  abstr_ref_over_cycles:                  0
% 3.00/1.01  abstr_ref_under_cycles:                 0
% 3.00/1.01  gc_basic_clause_elim:                   0
% 3.00/1.01  forced_gc_time:                         0
% 3.00/1.01  parsing_time:                           0.015
% 3.00/1.01  unif_index_cands_time:                  0.
% 3.00/1.01  unif_index_add_time:                    0.
% 3.00/1.01  orderings_time:                         0.
% 3.00/1.01  out_proof_time:                         0.027
% 3.00/1.01  total_time:                             0.224
% 3.00/1.01  num_of_symbols:                         50
% 3.00/1.01  num_of_terms:                           3336
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing
% 3.00/1.01  
% 3.00/1.01  num_of_splits:                          0
% 3.00/1.01  num_of_split_atoms:                     0
% 3.00/1.01  num_of_reused_defs:                     0
% 3.00/1.01  num_eq_ax_congr_red:                    17
% 3.00/1.01  num_of_sem_filtered_clauses:            1
% 3.00/1.01  num_of_subtypes:                        0
% 3.00/1.01  monotx_restored_types:                  0
% 3.00/1.01  sat_num_of_epr_types:                   0
% 3.00/1.01  sat_num_of_non_cyclic_types:            0
% 3.00/1.01  sat_guarded_non_collapsed_types:        0
% 3.00/1.01  num_pure_diseq_elim:                    0
% 3.00/1.01  simp_replaced_by:                       0
% 3.00/1.01  res_preprocessed:                       91
% 3.00/1.01  prep_upred:                             0
% 3.00/1.01  prep_unflattend:                        49
% 3.00/1.01  smt_new_axioms:                         0
% 3.00/1.01  pred_elim_cands:                        3
% 3.00/1.01  pred_elim:                              4
% 3.00/1.01  pred_elim_cl:                           8
% 3.00/1.01  pred_elim_cycles:                       8
% 3.00/1.01  merged_defs:                            0
% 3.00/1.01  merged_defs_ncl:                        0
% 3.00/1.01  bin_hyper_res:                          0
% 3.00/1.01  prep_cycles:                            4
% 3.00/1.01  pred_elim_time:                         0.013
% 3.00/1.01  splitting_time:                         0.
% 3.00/1.01  sem_filter_time:                        0.
% 3.00/1.01  monotx_time:                            0.001
% 3.00/1.01  subtype_inf_time:                       0.
% 3.00/1.01  
% 3.00/1.01  ------ Problem properties
% 3.00/1.01  
% 3.00/1.01  clauses:                                16
% 3.00/1.01  conjectures:                            2
% 3.00/1.01  epr:                                    3
% 3.00/1.01  horn:                                   13
% 3.00/1.01  ground:                                 6
% 3.00/1.01  unary:                                  5
% 3.00/1.01  binary:                                 6
% 3.00/1.01  lits:                                   34
% 3.00/1.01  lits_eq:                                17
% 3.00/1.01  fd_pure:                                0
% 3.00/1.01  fd_pseudo:                              0
% 3.00/1.01  fd_cond:                                1
% 3.00/1.01  fd_pseudo_cond:                         1
% 3.00/1.01  ac_symbols:                             0
% 3.00/1.01  
% 3.00/1.01  ------ Propositional Solver
% 3.00/1.01  
% 3.00/1.01  prop_solver_calls:                      30
% 3.00/1.01  prop_fast_solver_calls:                 727
% 3.00/1.01  smt_solver_calls:                       0
% 3.00/1.01  smt_fast_solver_calls:                  0
% 3.00/1.01  prop_num_of_clauses:                    1478
% 3.00/1.01  prop_preprocess_simplified:             4114
% 3.00/1.01  prop_fo_subsumed:                       10
% 3.00/1.01  prop_solver_time:                       0.
% 3.00/1.01  smt_solver_time:                        0.
% 3.00/1.01  smt_fast_solver_time:                   0.
% 3.00/1.01  prop_fast_solver_time:                  0.
% 3.00/1.01  prop_unsat_core_time:                   0.
% 3.00/1.01  
% 3.00/1.01  ------ QBF
% 3.00/1.01  
% 3.00/1.01  qbf_q_res:                              0
% 3.00/1.01  qbf_num_tautologies:                    0
% 3.00/1.01  qbf_prep_cycles:                        0
% 3.00/1.01  
% 3.00/1.01  ------ BMC1
% 3.00/1.01  
% 3.00/1.01  bmc1_current_bound:                     -1
% 3.00/1.01  bmc1_last_solved_bound:                 -1
% 3.00/1.01  bmc1_unsat_core_size:                   -1
% 3.00/1.01  bmc1_unsat_core_parents_size:           -1
% 3.00/1.01  bmc1_merge_next_fun:                    0
% 3.00/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.00/1.01  
% 3.00/1.01  ------ Instantiation
% 3.00/1.01  
% 3.00/1.01  inst_num_of_clauses:                    661
% 3.00/1.01  inst_num_in_passive:                    169
% 3.00/1.01  inst_num_in_active:                     285
% 3.00/1.01  inst_num_in_unprocessed:                208
% 3.00/1.01  inst_num_of_loops:                      310
% 3.00/1.01  inst_num_of_learning_restarts:          0
% 3.00/1.01  inst_num_moves_active_passive:          21
% 3.00/1.01  inst_lit_activity:                      0
% 3.00/1.01  inst_lit_activity_moves:                0
% 3.00/1.01  inst_num_tautologies:                   0
% 3.00/1.01  inst_num_prop_implied:                  0
% 3.00/1.01  inst_num_existing_simplified:           0
% 3.00/1.01  inst_num_eq_res_simplified:             0
% 3.00/1.01  inst_num_child_elim:                    0
% 3.00/1.01  inst_num_of_dismatching_blockings:      53
% 3.00/1.01  inst_num_of_non_proper_insts:           603
% 3.00/1.01  inst_num_of_duplicates:                 0
% 3.00/1.01  inst_inst_num_from_inst_to_res:         0
% 3.00/1.01  inst_dismatching_checking_time:         0.
% 3.00/1.01  
% 3.00/1.01  ------ Resolution
% 3.00/1.01  
% 3.00/1.01  res_num_of_clauses:                     0
% 3.00/1.01  res_num_in_passive:                     0
% 3.00/1.01  res_num_in_active:                      0
% 3.00/1.01  res_num_of_loops:                       95
% 3.00/1.01  res_forward_subset_subsumed:            52
% 3.00/1.01  res_backward_subset_subsumed:           2
% 3.00/1.01  res_forward_subsumed:                   0
% 3.00/1.01  res_backward_subsumed:                  0
% 3.00/1.01  res_forward_subsumption_resolution:     0
% 3.00/1.01  res_backward_subsumption_resolution:    0
% 3.00/1.01  res_clause_to_clause_subsumption:       223
% 3.00/1.01  res_orphan_elimination:                 0
% 3.00/1.01  res_tautology_del:                      38
% 3.00/1.01  res_num_eq_res_simplified:              0
% 3.00/1.01  res_num_sel_changes:                    0
% 3.00/1.01  res_moves_from_active_to_pass:          0
% 3.00/1.01  
% 3.00/1.01  ------ Superposition
% 3.00/1.01  
% 3.00/1.01  sup_time_total:                         0.
% 3.00/1.01  sup_time_generating:                    0.
% 3.00/1.01  sup_time_sim_full:                      0.
% 3.00/1.01  sup_time_sim_immed:                     0.
% 3.00/1.01  
% 3.00/1.01  sup_num_of_clauses:                     47
% 3.00/1.01  sup_num_in_active:                      32
% 3.00/1.01  sup_num_in_passive:                     15
% 3.00/1.01  sup_num_of_loops:                       60
% 3.00/1.01  sup_fw_superposition:                   43
% 3.00/1.01  sup_bw_superposition:                   19
% 3.00/1.01  sup_immediate_simplified:               14
% 3.00/1.01  sup_given_eliminated:                   2
% 3.00/1.01  comparisons_done:                       0
% 3.00/1.01  comparisons_avoided:                    36
% 3.00/1.01  
% 3.00/1.01  ------ Simplifications
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  sim_fw_subset_subsumed:                 7
% 3.00/1.01  sim_bw_subset_subsumed:                 4
% 3.00/1.01  sim_fw_subsumed:                        0
% 3.00/1.01  sim_bw_subsumed:                        4
% 3.00/1.01  sim_fw_subsumption_res:                 2
% 3.00/1.01  sim_bw_subsumption_res:                 0
% 3.00/1.01  sim_tautology_del:                      1
% 3.00/1.01  sim_eq_tautology_del:                   10
% 3.00/1.01  sim_eq_res_simp:                        2
% 3.00/1.01  sim_fw_demodulated:                     7
% 3.00/1.01  sim_bw_demodulated:                     23
% 3.00/1.01  sim_light_normalised:                   0
% 3.00/1.01  sim_joinable_taut:                      0
% 3.00/1.01  sim_joinable_simp:                      0
% 3.00/1.01  sim_ac_normalised:                      0
% 3.00/1.01  sim_smt_subsumption:                    0
% 3.00/1.01  
%------------------------------------------------------------------------------
