%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:58 EST 2020

% Result     : Theorem 34.93s
% Output     : CNFRefutation 34.93s
% Verified   : 
% Statistics : Number of formulae       :  245 (2896 expanded)
%              Number of clauses        :  158 (1169 expanded)
%              Number of leaves         :   23 ( 509 expanded)
%              Depth                    :   37
%              Number of atoms          :  735 (13237 expanded)
%              Number of equality atoms :  425 (4033 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f40,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f49,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f49])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f86,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f94,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f92,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f91])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f85,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1481,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1483,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4211,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_1483])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4430,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4211,c_36])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1484,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2695,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_1484])).

cnf(c_2970,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2695,c_36])).

cnf(c_4436,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4430,c_2970])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1482,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_34])).

cnf(c_547,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_549,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_547,c_33])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1487,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2842,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1481,c_1487])).

cnf(c_2908,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_549,c_2842])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1488,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3498,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2908,c_1488])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1491,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1493,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2394,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_1493])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_253,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_254,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_253])).

cnf(c_317,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_254])).

cnf(c_1479,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_2397,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2394,c_1479])).

cnf(c_2445,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1491,c_2397])).

cnf(c_3661,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3498,c_2445])).

cnf(c_3662,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3661])).

cnf(c_3670,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1482,c_3662])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1497,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_20,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1486,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3806,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1486])).

cnf(c_4979,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1497,c_3806])).

cnf(c_16459,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3670,c_4979])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2691,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2692,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2691])).

cnf(c_16576,plain,
    ( r1_tarski(sK2,k1_xboole_0) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16459,c_2445,c_2692])).

cnf(c_16577,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16576])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_425,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_12])).

cnf(c_1478,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_1807,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1478])).

cnf(c_16581,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16577,c_1807])).

cnf(c_16608,plain,
    ( r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16581,c_2445,c_2692])).

cnf(c_16609,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16608])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1485,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4443,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4430,c_1485])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4583,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4443,c_36,c_38])).

cnf(c_4594,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4583,c_1478])).

cnf(c_3808,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1486,c_1487])).

cnf(c_92859,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3670,c_3808])).

cnf(c_93663,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_92859,c_2445,c_2692])).

cnf(c_93664,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_93663])).

cnf(c_93672,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4594,c_93664])).

cnf(c_94129,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_93672,c_2445,c_2692])).

cnf(c_94130,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_94129])).

cnf(c_94135,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1497,c_94130])).

cnf(c_24,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_531,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_1473,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_4435,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4430,c_1473])).

cnf(c_94484,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_94135,c_4435])).

cnf(c_94639,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_94484,c_3670])).

cnf(c_94644,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1486,c_94639])).

cnf(c_16,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_47255,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_47257,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47255])).

cnf(c_97325,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_94644,c_2445,c_2692,c_47257])).

cnf(c_97326,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_97325])).

cnf(c_97331,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16609,c_97326])).

cnf(c_97330,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4594,c_97326])).

cnf(c_97395,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_97331,c_2445,c_2692,c_97330])).

cnf(c_97399,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4436,c_97395])).

cnf(c_23,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_499,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_1475,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_1502,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1475,c_6])).

cnf(c_1764,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1765,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1764])).

cnf(c_1960,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1502,c_36,c_38,c_1765])).

cnf(c_1961,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1960])).

cnf(c_4433,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4430,c_1961])).

cnf(c_98076,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_97399,c_4433])).

cnf(c_21,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_452,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_453,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_1477,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1501,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1477,c_5])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_105,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_106,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_858,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1546,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_858])).

cnf(c_1595,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1546])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1661,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_857,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1750,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(c_1762,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_858])).

cnf(c_1763,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_859,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1568,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_1645,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1568])).

cnf(c_1894,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1645])).

cnf(c_1957,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1501,c_32,c_31,c_105,c_106,c_1595,c_1661,c_1750,c_1763,c_1894])).

cnf(c_1958,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1957])).

cnf(c_98094,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_97399,c_1958])).

cnf(c_98105,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_98094])).

cnf(c_98120,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_98076,c_98105])).

cnf(c_98121,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_98120])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1490,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2537,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2445,c_1490])).

cnf(c_98122,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_98121,c_2537])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1496,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1494,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2841,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1494,c_1487])).

cnf(c_7257,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1496,c_2841])).

cnf(c_1489,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2830,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2537,c_1489])).

cnf(c_3092,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2830,c_2445])).

cnf(c_1495,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3097,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3092,c_1495])).

cnf(c_7264,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7257,c_3097])).

cnf(c_98123,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_98122,c_6,c_7264])).

cnf(c_98124,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_98123])).

cnf(c_110,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_112,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_102,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_104,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_98124,c_112,c_104])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 34.93/5.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.93/5.02  
% 34.93/5.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 34.93/5.02  
% 34.93/5.02  ------  iProver source info
% 34.93/5.02  
% 34.93/5.02  git: date: 2020-06-30 10:37:57 +0100
% 34.93/5.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 34.93/5.02  git: non_committed_changes: false
% 34.93/5.02  git: last_make_outside_of_git: false
% 34.93/5.02  
% 34.93/5.02  ------ 
% 34.93/5.02  
% 34.93/5.02  ------ Input Options
% 34.93/5.02  
% 34.93/5.02  --out_options                           all
% 34.93/5.02  --tptp_safe_out                         true
% 34.93/5.02  --problem_path                          ""
% 34.93/5.02  --include_path                          ""
% 34.93/5.02  --clausifier                            res/vclausify_rel
% 34.93/5.02  --clausifier_options                    ""
% 34.93/5.02  --stdin                                 false
% 34.93/5.02  --stats_out                             all
% 34.93/5.02  
% 34.93/5.02  ------ General Options
% 34.93/5.02  
% 34.93/5.02  --fof                                   false
% 34.93/5.02  --time_out_real                         305.
% 34.93/5.02  --time_out_virtual                      -1.
% 34.93/5.02  --symbol_type_check                     false
% 34.93/5.02  --clausify_out                          false
% 34.93/5.02  --sig_cnt_out                           false
% 34.93/5.02  --trig_cnt_out                          false
% 34.93/5.02  --trig_cnt_out_tolerance                1.
% 34.93/5.02  --trig_cnt_out_sk_spl                   false
% 34.93/5.02  --abstr_cl_out                          false
% 34.93/5.02  
% 34.93/5.02  ------ Global Options
% 34.93/5.02  
% 34.93/5.02  --schedule                              default
% 34.93/5.02  --add_important_lit                     false
% 34.93/5.02  --prop_solver_per_cl                    1000
% 34.93/5.02  --min_unsat_core                        false
% 34.93/5.02  --soft_assumptions                      false
% 34.93/5.02  --soft_lemma_size                       3
% 34.93/5.02  --prop_impl_unit_size                   0
% 34.93/5.02  --prop_impl_unit                        []
% 34.93/5.02  --share_sel_clauses                     true
% 34.93/5.02  --reset_solvers                         false
% 34.93/5.02  --bc_imp_inh                            [conj_cone]
% 34.93/5.02  --conj_cone_tolerance                   3.
% 34.93/5.02  --extra_neg_conj                        none
% 34.93/5.02  --large_theory_mode                     true
% 34.93/5.02  --prolific_symb_bound                   200
% 34.93/5.02  --lt_threshold                          2000
% 34.93/5.02  --clause_weak_htbl                      true
% 34.93/5.02  --gc_record_bc_elim                     false
% 34.93/5.02  
% 34.93/5.02  ------ Preprocessing Options
% 34.93/5.02  
% 34.93/5.02  --preprocessing_flag                    true
% 34.93/5.02  --time_out_prep_mult                    0.1
% 34.93/5.02  --splitting_mode                        input
% 34.93/5.02  --splitting_grd                         true
% 34.93/5.02  --splitting_cvd                         false
% 34.93/5.02  --splitting_cvd_svl                     false
% 34.93/5.02  --splitting_nvd                         32
% 34.93/5.02  --sub_typing                            true
% 34.93/5.02  --prep_gs_sim                           true
% 34.93/5.02  --prep_unflatten                        true
% 34.93/5.02  --prep_res_sim                          true
% 34.93/5.02  --prep_upred                            true
% 34.93/5.02  --prep_sem_filter                       exhaustive
% 34.93/5.02  --prep_sem_filter_out                   false
% 34.93/5.02  --pred_elim                             true
% 34.93/5.02  --res_sim_input                         true
% 34.93/5.02  --eq_ax_congr_red                       true
% 34.93/5.02  --pure_diseq_elim                       true
% 34.93/5.02  --brand_transform                       false
% 34.93/5.02  --non_eq_to_eq                          false
% 34.93/5.02  --prep_def_merge                        true
% 34.93/5.02  --prep_def_merge_prop_impl              false
% 34.93/5.02  --prep_def_merge_mbd                    true
% 34.93/5.02  --prep_def_merge_tr_red                 false
% 34.93/5.02  --prep_def_merge_tr_cl                  false
% 34.93/5.02  --smt_preprocessing                     true
% 34.93/5.02  --smt_ac_axioms                         fast
% 34.93/5.02  --preprocessed_out                      false
% 34.93/5.02  --preprocessed_stats                    false
% 34.93/5.02  
% 34.93/5.02  ------ Abstraction refinement Options
% 34.93/5.02  
% 34.93/5.02  --abstr_ref                             []
% 34.93/5.02  --abstr_ref_prep                        false
% 34.93/5.02  --abstr_ref_until_sat                   false
% 34.93/5.02  --abstr_ref_sig_restrict                funpre
% 34.93/5.02  --abstr_ref_af_restrict_to_split_sk     false
% 34.93/5.02  --abstr_ref_under                       []
% 34.93/5.02  
% 34.93/5.02  ------ SAT Options
% 34.93/5.02  
% 34.93/5.02  --sat_mode                              false
% 34.93/5.02  --sat_fm_restart_options                ""
% 34.93/5.02  --sat_gr_def                            false
% 34.93/5.02  --sat_epr_types                         true
% 34.93/5.02  --sat_non_cyclic_types                  false
% 34.93/5.02  --sat_finite_models                     false
% 34.93/5.02  --sat_fm_lemmas                         false
% 34.93/5.02  --sat_fm_prep                           false
% 34.93/5.02  --sat_fm_uc_incr                        true
% 34.93/5.02  --sat_out_model                         small
% 34.93/5.02  --sat_out_clauses                       false
% 34.93/5.02  
% 34.93/5.02  ------ QBF Options
% 34.93/5.02  
% 34.93/5.02  --qbf_mode                              false
% 34.93/5.02  --qbf_elim_univ                         false
% 34.93/5.02  --qbf_dom_inst                          none
% 34.93/5.02  --qbf_dom_pre_inst                      false
% 34.93/5.02  --qbf_sk_in                             false
% 34.93/5.02  --qbf_pred_elim                         true
% 34.93/5.02  --qbf_split                             512
% 34.93/5.02  
% 34.93/5.02  ------ BMC1 Options
% 34.93/5.02  
% 34.93/5.02  --bmc1_incremental                      false
% 34.93/5.02  --bmc1_axioms                           reachable_all
% 34.93/5.02  --bmc1_min_bound                        0
% 34.93/5.02  --bmc1_max_bound                        -1
% 34.93/5.02  --bmc1_max_bound_default                -1
% 34.93/5.02  --bmc1_symbol_reachability              true
% 34.93/5.02  --bmc1_property_lemmas                  false
% 34.93/5.02  --bmc1_k_induction                      false
% 34.93/5.02  --bmc1_non_equiv_states                 false
% 34.93/5.02  --bmc1_deadlock                         false
% 34.93/5.02  --bmc1_ucm                              false
% 34.93/5.02  --bmc1_add_unsat_core                   none
% 34.93/5.02  --bmc1_unsat_core_children              false
% 34.93/5.02  --bmc1_unsat_core_extrapolate_axioms    false
% 34.93/5.02  --bmc1_out_stat                         full
% 34.93/5.02  --bmc1_ground_init                      false
% 34.93/5.02  --bmc1_pre_inst_next_state              false
% 34.93/5.02  --bmc1_pre_inst_state                   false
% 34.93/5.02  --bmc1_pre_inst_reach_state             false
% 34.93/5.02  --bmc1_out_unsat_core                   false
% 34.93/5.02  --bmc1_aig_witness_out                  false
% 34.93/5.02  --bmc1_verbose                          false
% 34.93/5.02  --bmc1_dump_clauses_tptp                false
% 34.93/5.02  --bmc1_dump_unsat_core_tptp             false
% 34.93/5.02  --bmc1_dump_file                        -
% 34.93/5.02  --bmc1_ucm_expand_uc_limit              128
% 34.93/5.02  --bmc1_ucm_n_expand_iterations          6
% 34.93/5.02  --bmc1_ucm_extend_mode                  1
% 34.93/5.02  --bmc1_ucm_init_mode                    2
% 34.93/5.02  --bmc1_ucm_cone_mode                    none
% 34.93/5.02  --bmc1_ucm_reduced_relation_type        0
% 34.93/5.02  --bmc1_ucm_relax_model                  4
% 34.93/5.02  --bmc1_ucm_full_tr_after_sat            true
% 34.93/5.02  --bmc1_ucm_expand_neg_assumptions       false
% 34.93/5.02  --bmc1_ucm_layered_model                none
% 34.93/5.02  --bmc1_ucm_max_lemma_size               10
% 34.93/5.02  
% 34.93/5.02  ------ AIG Options
% 34.93/5.02  
% 34.93/5.02  --aig_mode                              false
% 34.93/5.02  
% 34.93/5.02  ------ Instantiation Options
% 34.93/5.02  
% 34.93/5.02  --instantiation_flag                    true
% 34.93/5.02  --inst_sos_flag                         true
% 34.93/5.02  --inst_sos_phase                        true
% 34.93/5.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 34.93/5.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 34.93/5.02  --inst_lit_sel_side                     num_symb
% 34.93/5.02  --inst_solver_per_active                1400
% 34.93/5.02  --inst_solver_calls_frac                1.
% 34.93/5.02  --inst_passive_queue_type               priority_queues
% 34.93/5.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 34.93/5.02  --inst_passive_queues_freq              [25;2]
% 34.93/5.02  --inst_dismatching                      true
% 34.93/5.02  --inst_eager_unprocessed_to_passive     true
% 34.93/5.02  --inst_prop_sim_given                   true
% 34.93/5.02  --inst_prop_sim_new                     false
% 34.93/5.02  --inst_subs_new                         false
% 34.93/5.02  --inst_eq_res_simp                      false
% 34.93/5.02  --inst_subs_given                       false
% 34.93/5.02  --inst_orphan_elimination               true
% 34.93/5.02  --inst_learning_loop_flag               true
% 34.93/5.02  --inst_learning_start                   3000
% 34.93/5.02  --inst_learning_factor                  2
% 34.93/5.02  --inst_start_prop_sim_after_learn       3
% 34.93/5.02  --inst_sel_renew                        solver
% 34.93/5.02  --inst_lit_activity_flag                true
% 34.93/5.02  --inst_restr_to_given                   false
% 34.93/5.02  --inst_activity_threshold               500
% 34.93/5.02  --inst_out_proof                        true
% 34.93/5.02  
% 34.93/5.02  ------ Resolution Options
% 34.93/5.02  
% 34.93/5.02  --resolution_flag                       true
% 34.93/5.02  --res_lit_sel                           adaptive
% 34.93/5.02  --res_lit_sel_side                      none
% 34.93/5.02  --res_ordering                          kbo
% 34.93/5.02  --res_to_prop_solver                    active
% 34.93/5.02  --res_prop_simpl_new                    false
% 34.93/5.02  --res_prop_simpl_given                  true
% 34.93/5.02  --res_passive_queue_type                priority_queues
% 34.93/5.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 34.93/5.02  --res_passive_queues_freq               [15;5]
% 34.93/5.02  --res_forward_subs                      full
% 34.93/5.02  --res_backward_subs                     full
% 34.93/5.02  --res_forward_subs_resolution           true
% 34.93/5.02  --res_backward_subs_resolution          true
% 34.93/5.02  --res_orphan_elimination                true
% 34.93/5.02  --res_time_limit                        2.
% 34.93/5.02  --res_out_proof                         true
% 34.93/5.02  
% 34.93/5.02  ------ Superposition Options
% 34.93/5.02  
% 34.93/5.02  --superposition_flag                    true
% 34.93/5.02  --sup_passive_queue_type                priority_queues
% 34.93/5.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 34.93/5.02  --sup_passive_queues_freq               [8;1;4]
% 34.93/5.02  --demod_completeness_check              fast
% 34.93/5.02  --demod_use_ground                      true
% 34.93/5.02  --sup_to_prop_solver                    passive
% 34.93/5.02  --sup_prop_simpl_new                    true
% 34.93/5.02  --sup_prop_simpl_given                  true
% 34.93/5.02  --sup_fun_splitting                     true
% 34.93/5.02  --sup_smt_interval                      50000
% 34.93/5.02  
% 34.93/5.02  ------ Superposition Simplification Setup
% 34.93/5.02  
% 34.93/5.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 34.93/5.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 34.93/5.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 34.93/5.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 34.93/5.02  --sup_full_triv                         [TrivRules;PropSubs]
% 34.93/5.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 34.93/5.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 34.93/5.02  --sup_immed_triv                        [TrivRules]
% 34.93/5.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 34.93/5.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 34.93/5.02  --sup_immed_bw_main                     []
% 34.93/5.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 34.93/5.02  --sup_input_triv                        [Unflattening;TrivRules]
% 34.93/5.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 34.93/5.02  --sup_input_bw                          []
% 34.93/5.02  
% 34.93/5.02  ------ Combination Options
% 34.93/5.02  
% 34.93/5.02  --comb_res_mult                         3
% 34.93/5.02  --comb_sup_mult                         2
% 34.93/5.02  --comb_inst_mult                        10
% 34.93/5.02  
% 34.93/5.02  ------ Debug Options
% 34.93/5.02  
% 34.93/5.02  --dbg_backtrace                         false
% 34.93/5.02  --dbg_dump_prop_clauses                 false
% 34.93/5.02  --dbg_dump_prop_clauses_file            -
% 34.93/5.02  --dbg_out_stat                          false
% 34.93/5.02  ------ Parsing...
% 34.93/5.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 34.93/5.02  
% 34.93/5.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 34.93/5.02  
% 34.93/5.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 34.93/5.02  
% 34.93/5.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 34.93/5.02  ------ Proving...
% 34.93/5.02  ------ Problem Properties 
% 34.93/5.02  
% 34.93/5.02  
% 34.93/5.02  clauses                                 32
% 34.93/5.02  conjectures                             4
% 34.93/5.02  EPR                                     8
% 34.93/5.02  Horn                                    29
% 34.93/5.02  unary                                   8
% 34.93/5.02  binary                                  9
% 34.93/5.02  lits                                    80
% 34.93/5.02  lits eq                                 29
% 34.93/5.02  fd_pure                                 0
% 34.93/5.02  fd_pseudo                               0
% 34.93/5.02  fd_cond                                 2
% 34.93/5.02  fd_pseudo_cond                          1
% 34.93/5.02  AC symbols                              0
% 34.93/5.02  
% 34.93/5.02  ------ Schedule dynamic 5 is on 
% 34.93/5.02  
% 34.93/5.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 34.93/5.02  
% 34.93/5.02  
% 34.93/5.02  ------ 
% 34.93/5.02  Current options:
% 34.93/5.02  ------ 
% 34.93/5.02  
% 34.93/5.02  ------ Input Options
% 34.93/5.02  
% 34.93/5.02  --out_options                           all
% 34.93/5.02  --tptp_safe_out                         true
% 34.93/5.02  --problem_path                          ""
% 34.93/5.02  --include_path                          ""
% 34.93/5.02  --clausifier                            res/vclausify_rel
% 34.93/5.02  --clausifier_options                    ""
% 34.93/5.02  --stdin                                 false
% 34.93/5.02  --stats_out                             all
% 34.93/5.02  
% 34.93/5.02  ------ General Options
% 34.93/5.02  
% 34.93/5.02  --fof                                   false
% 34.93/5.02  --time_out_real                         305.
% 34.93/5.02  --time_out_virtual                      -1.
% 34.93/5.02  --symbol_type_check                     false
% 34.93/5.02  --clausify_out                          false
% 34.93/5.02  --sig_cnt_out                           false
% 34.93/5.02  --trig_cnt_out                          false
% 34.93/5.02  --trig_cnt_out_tolerance                1.
% 34.93/5.02  --trig_cnt_out_sk_spl                   false
% 34.93/5.02  --abstr_cl_out                          false
% 34.93/5.02  
% 34.93/5.02  ------ Global Options
% 34.93/5.02  
% 34.93/5.02  --schedule                              default
% 34.93/5.02  --add_important_lit                     false
% 34.93/5.02  --prop_solver_per_cl                    1000
% 34.93/5.02  --min_unsat_core                        false
% 34.93/5.02  --soft_assumptions                      false
% 34.93/5.02  --soft_lemma_size                       3
% 34.93/5.02  --prop_impl_unit_size                   0
% 34.93/5.02  --prop_impl_unit                        []
% 34.93/5.02  --share_sel_clauses                     true
% 34.93/5.02  --reset_solvers                         false
% 34.93/5.02  --bc_imp_inh                            [conj_cone]
% 34.93/5.02  --conj_cone_tolerance                   3.
% 34.93/5.02  --extra_neg_conj                        none
% 34.93/5.02  --large_theory_mode                     true
% 34.93/5.02  --prolific_symb_bound                   200
% 34.93/5.02  --lt_threshold                          2000
% 34.93/5.02  --clause_weak_htbl                      true
% 34.93/5.02  --gc_record_bc_elim                     false
% 34.93/5.02  
% 34.93/5.02  ------ Preprocessing Options
% 34.93/5.02  
% 34.93/5.02  --preprocessing_flag                    true
% 34.93/5.02  --time_out_prep_mult                    0.1
% 34.93/5.02  --splitting_mode                        input
% 34.93/5.02  --splitting_grd                         true
% 34.93/5.02  --splitting_cvd                         false
% 34.93/5.02  --splitting_cvd_svl                     false
% 34.93/5.02  --splitting_nvd                         32
% 34.93/5.02  --sub_typing                            true
% 34.93/5.02  --prep_gs_sim                           true
% 34.93/5.02  --prep_unflatten                        true
% 34.93/5.02  --prep_res_sim                          true
% 34.93/5.02  --prep_upred                            true
% 34.93/5.02  --prep_sem_filter                       exhaustive
% 34.93/5.02  --prep_sem_filter_out                   false
% 34.93/5.02  --pred_elim                             true
% 34.93/5.02  --res_sim_input                         true
% 34.93/5.02  --eq_ax_congr_red                       true
% 34.93/5.02  --pure_diseq_elim                       true
% 34.93/5.02  --brand_transform                       false
% 34.93/5.02  --non_eq_to_eq                          false
% 34.93/5.02  --prep_def_merge                        true
% 34.93/5.02  --prep_def_merge_prop_impl              false
% 34.93/5.02  --prep_def_merge_mbd                    true
% 34.93/5.02  --prep_def_merge_tr_red                 false
% 34.93/5.02  --prep_def_merge_tr_cl                  false
% 34.93/5.02  --smt_preprocessing                     true
% 34.93/5.02  --smt_ac_axioms                         fast
% 34.93/5.02  --preprocessed_out                      false
% 34.93/5.02  --preprocessed_stats                    false
% 34.93/5.02  
% 34.93/5.02  ------ Abstraction refinement Options
% 34.93/5.02  
% 34.93/5.02  --abstr_ref                             []
% 34.93/5.02  --abstr_ref_prep                        false
% 34.93/5.02  --abstr_ref_until_sat                   false
% 34.93/5.02  --abstr_ref_sig_restrict                funpre
% 34.93/5.02  --abstr_ref_af_restrict_to_split_sk     false
% 34.93/5.02  --abstr_ref_under                       []
% 34.93/5.02  
% 34.93/5.02  ------ SAT Options
% 34.93/5.02  
% 34.93/5.02  --sat_mode                              false
% 34.93/5.02  --sat_fm_restart_options                ""
% 34.93/5.02  --sat_gr_def                            false
% 34.93/5.02  --sat_epr_types                         true
% 34.93/5.02  --sat_non_cyclic_types                  false
% 34.93/5.02  --sat_finite_models                     false
% 34.93/5.02  --sat_fm_lemmas                         false
% 34.93/5.02  --sat_fm_prep                           false
% 34.93/5.02  --sat_fm_uc_incr                        true
% 34.93/5.02  --sat_out_model                         small
% 34.93/5.02  --sat_out_clauses                       false
% 34.93/5.02  
% 34.93/5.02  ------ QBF Options
% 34.93/5.02  
% 34.93/5.02  --qbf_mode                              false
% 34.93/5.02  --qbf_elim_univ                         false
% 34.93/5.02  --qbf_dom_inst                          none
% 34.93/5.02  --qbf_dom_pre_inst                      false
% 34.93/5.02  --qbf_sk_in                             false
% 34.93/5.02  --qbf_pred_elim                         true
% 34.93/5.02  --qbf_split                             512
% 34.93/5.02  
% 34.93/5.02  ------ BMC1 Options
% 34.93/5.02  
% 34.93/5.02  --bmc1_incremental                      false
% 34.93/5.02  --bmc1_axioms                           reachable_all
% 34.93/5.02  --bmc1_min_bound                        0
% 34.93/5.02  --bmc1_max_bound                        -1
% 34.93/5.02  --bmc1_max_bound_default                -1
% 34.93/5.02  --bmc1_symbol_reachability              true
% 34.93/5.02  --bmc1_property_lemmas                  false
% 34.93/5.02  --bmc1_k_induction                      false
% 34.93/5.02  --bmc1_non_equiv_states                 false
% 34.93/5.02  --bmc1_deadlock                         false
% 34.93/5.02  --bmc1_ucm                              false
% 34.93/5.02  --bmc1_add_unsat_core                   none
% 34.93/5.02  --bmc1_unsat_core_children              false
% 34.93/5.02  --bmc1_unsat_core_extrapolate_axioms    false
% 34.93/5.02  --bmc1_out_stat                         full
% 34.93/5.02  --bmc1_ground_init                      false
% 34.93/5.02  --bmc1_pre_inst_next_state              false
% 34.93/5.02  --bmc1_pre_inst_state                   false
% 34.93/5.02  --bmc1_pre_inst_reach_state             false
% 34.93/5.02  --bmc1_out_unsat_core                   false
% 34.93/5.02  --bmc1_aig_witness_out                  false
% 34.93/5.02  --bmc1_verbose                          false
% 34.93/5.02  --bmc1_dump_clauses_tptp                false
% 34.93/5.02  --bmc1_dump_unsat_core_tptp             false
% 34.93/5.02  --bmc1_dump_file                        -
% 34.93/5.02  --bmc1_ucm_expand_uc_limit              128
% 34.93/5.02  --bmc1_ucm_n_expand_iterations          6
% 34.93/5.02  --bmc1_ucm_extend_mode                  1
% 34.93/5.02  --bmc1_ucm_init_mode                    2
% 34.93/5.02  --bmc1_ucm_cone_mode                    none
% 34.93/5.02  --bmc1_ucm_reduced_relation_type        0
% 34.93/5.02  --bmc1_ucm_relax_model                  4
% 34.93/5.02  --bmc1_ucm_full_tr_after_sat            true
% 34.93/5.02  --bmc1_ucm_expand_neg_assumptions       false
% 34.93/5.02  --bmc1_ucm_layered_model                none
% 34.93/5.02  --bmc1_ucm_max_lemma_size               10
% 34.93/5.02  
% 34.93/5.02  ------ AIG Options
% 34.93/5.02  
% 34.93/5.02  --aig_mode                              false
% 34.93/5.02  
% 34.93/5.02  ------ Instantiation Options
% 34.93/5.02  
% 34.93/5.02  --instantiation_flag                    true
% 34.93/5.02  --inst_sos_flag                         true
% 34.93/5.02  --inst_sos_phase                        true
% 34.93/5.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 34.93/5.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 34.93/5.02  --inst_lit_sel_side                     none
% 34.93/5.02  --inst_solver_per_active                1400
% 34.93/5.02  --inst_solver_calls_frac                1.
% 34.93/5.02  --inst_passive_queue_type               priority_queues
% 34.93/5.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 34.93/5.02  --inst_passive_queues_freq              [25;2]
% 34.93/5.02  --inst_dismatching                      true
% 34.93/5.02  --inst_eager_unprocessed_to_passive     true
% 34.93/5.02  --inst_prop_sim_given                   true
% 34.93/5.02  --inst_prop_sim_new                     false
% 34.93/5.02  --inst_subs_new                         false
% 34.93/5.02  --inst_eq_res_simp                      false
% 34.93/5.02  --inst_subs_given                       false
% 34.93/5.02  --inst_orphan_elimination               true
% 34.93/5.02  --inst_learning_loop_flag               true
% 34.93/5.02  --inst_learning_start                   3000
% 34.93/5.02  --inst_learning_factor                  2
% 34.93/5.02  --inst_start_prop_sim_after_learn       3
% 34.93/5.02  --inst_sel_renew                        solver
% 34.93/5.02  --inst_lit_activity_flag                true
% 34.93/5.02  --inst_restr_to_given                   false
% 34.93/5.02  --inst_activity_threshold               500
% 34.93/5.02  --inst_out_proof                        true
% 34.93/5.02  
% 34.93/5.02  ------ Resolution Options
% 34.93/5.02  
% 34.93/5.02  --resolution_flag                       false
% 34.93/5.02  --res_lit_sel                           adaptive
% 34.93/5.02  --res_lit_sel_side                      none
% 34.93/5.02  --res_ordering                          kbo
% 34.93/5.02  --res_to_prop_solver                    active
% 34.93/5.02  --res_prop_simpl_new                    false
% 34.93/5.02  --res_prop_simpl_given                  true
% 34.93/5.02  --res_passive_queue_type                priority_queues
% 34.93/5.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 34.93/5.02  --res_passive_queues_freq               [15;5]
% 34.93/5.02  --res_forward_subs                      full
% 34.93/5.02  --res_backward_subs                     full
% 34.93/5.02  --res_forward_subs_resolution           true
% 34.93/5.02  --res_backward_subs_resolution          true
% 34.93/5.02  --res_orphan_elimination                true
% 34.93/5.02  --res_time_limit                        2.
% 34.93/5.02  --res_out_proof                         true
% 34.93/5.02  
% 34.93/5.02  ------ Superposition Options
% 34.93/5.02  
% 34.93/5.02  --superposition_flag                    true
% 34.93/5.02  --sup_passive_queue_type                priority_queues
% 34.93/5.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 34.93/5.02  --sup_passive_queues_freq               [8;1;4]
% 34.93/5.02  --demod_completeness_check              fast
% 34.93/5.02  --demod_use_ground                      true
% 34.93/5.02  --sup_to_prop_solver                    passive
% 34.93/5.02  --sup_prop_simpl_new                    true
% 34.93/5.02  --sup_prop_simpl_given                  true
% 34.93/5.02  --sup_fun_splitting                     true
% 34.93/5.02  --sup_smt_interval                      50000
% 34.93/5.02  
% 34.93/5.02  ------ Superposition Simplification Setup
% 34.93/5.02  
% 34.93/5.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 34.93/5.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 34.93/5.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 34.93/5.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 34.93/5.02  --sup_full_triv                         [TrivRules;PropSubs]
% 34.93/5.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 34.93/5.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 34.93/5.02  --sup_immed_triv                        [TrivRules]
% 34.93/5.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 34.93/5.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 34.93/5.02  --sup_immed_bw_main                     []
% 34.93/5.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 34.93/5.02  --sup_input_triv                        [Unflattening;TrivRules]
% 34.93/5.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 34.93/5.02  --sup_input_bw                          []
% 34.93/5.02  
% 34.93/5.02  ------ Combination Options
% 34.93/5.02  
% 34.93/5.02  --comb_res_mult                         3
% 34.93/5.02  --comb_sup_mult                         2
% 34.93/5.02  --comb_inst_mult                        10
% 34.93/5.02  
% 34.93/5.02  ------ Debug Options
% 34.93/5.02  
% 34.93/5.02  --dbg_backtrace                         false
% 34.93/5.02  --dbg_dump_prop_clauses                 false
% 34.93/5.02  --dbg_dump_prop_clauses_file            -
% 34.93/5.02  --dbg_out_stat                          false
% 34.93/5.02  
% 34.93/5.02  
% 34.93/5.02  
% 34.93/5.02  
% 34.93/5.02  ------ Proving...
% 34.93/5.02  
% 34.93/5.02  
% 34.93/5.02  % SZS status Theorem for theBenchmark.p
% 34.93/5.02  
% 34.93/5.02  % SZS output start CNFRefutation for theBenchmark.p
% 34.93/5.02  
% 34.93/5.02  fof(f19,conjecture,(
% 34.93/5.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f20,negated_conjecture,(
% 34.93/5.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 34.93/5.02    inference(negated_conjecture,[],[f19])).
% 34.93/5.02  
% 34.93/5.02  fof(f40,plain,(
% 34.93/5.02    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 34.93/5.02    inference(ennf_transformation,[],[f20])).
% 34.93/5.02  
% 34.93/5.02  fof(f41,plain,(
% 34.93/5.02    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 34.93/5.02    inference(flattening,[],[f40])).
% 34.93/5.02  
% 34.93/5.02  fof(f49,plain,(
% 34.93/5.02    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 34.93/5.02    introduced(choice_axiom,[])).
% 34.93/5.02  
% 34.93/5.02  fof(f50,plain,(
% 34.93/5.02    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 34.93/5.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f49])).
% 34.93/5.02  
% 34.93/5.02  fof(f83,plain,(
% 34.93/5.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 34.93/5.02    inference(cnf_transformation,[],[f50])).
% 34.93/5.02  
% 34.93/5.02  fof(f18,axiom,(
% 34.93/5.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f38,plain,(
% 34.93/5.02    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 34.93/5.02    inference(ennf_transformation,[],[f18])).
% 34.93/5.02  
% 34.93/5.02  fof(f39,plain,(
% 34.93/5.02    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 34.93/5.02    inference(flattening,[],[f38])).
% 34.93/5.02  
% 34.93/5.02  fof(f80,plain,(
% 34.93/5.02    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 34.93/5.02    inference(cnf_transformation,[],[f39])).
% 34.93/5.02  
% 34.93/5.02  fof(f81,plain,(
% 34.93/5.02    v1_funct_1(sK3)),
% 34.93/5.02    inference(cnf_transformation,[],[f50])).
% 34.93/5.02  
% 34.93/5.02  fof(f17,axiom,(
% 34.93/5.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f36,plain,(
% 34.93/5.02    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 34.93/5.02    inference(ennf_transformation,[],[f17])).
% 34.93/5.02  
% 34.93/5.02  fof(f37,plain,(
% 34.93/5.02    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 34.93/5.02    inference(flattening,[],[f36])).
% 34.93/5.02  
% 34.93/5.02  fof(f78,plain,(
% 34.93/5.02    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 34.93/5.02    inference(cnf_transformation,[],[f37])).
% 34.93/5.02  
% 34.93/5.02  fof(f84,plain,(
% 34.93/5.02    r1_tarski(sK2,sK0)),
% 34.93/5.02    inference(cnf_transformation,[],[f50])).
% 34.93/5.02  
% 34.93/5.02  fof(f16,axiom,(
% 34.93/5.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f34,plain,(
% 34.93/5.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 34.93/5.02    inference(ennf_transformation,[],[f16])).
% 34.93/5.02  
% 34.93/5.02  fof(f35,plain,(
% 34.93/5.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 34.93/5.02    inference(flattening,[],[f34])).
% 34.93/5.02  
% 34.93/5.02  fof(f48,plain,(
% 34.93/5.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 34.93/5.02    inference(nnf_transformation,[],[f35])).
% 34.93/5.02  
% 34.93/5.02  fof(f72,plain,(
% 34.93/5.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 34.93/5.02    inference(cnf_transformation,[],[f48])).
% 34.93/5.02  
% 34.93/5.02  fof(f82,plain,(
% 34.93/5.02    v1_funct_2(sK3,sK0,sK1)),
% 34.93/5.02    inference(cnf_transformation,[],[f50])).
% 34.93/5.02  
% 34.93/5.02  fof(f14,axiom,(
% 34.93/5.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f31,plain,(
% 34.93/5.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 34.93/5.02    inference(ennf_transformation,[],[f14])).
% 34.93/5.02  
% 34.93/5.02  fof(f70,plain,(
% 34.93/5.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 34.93/5.02    inference(cnf_transformation,[],[f31])).
% 34.93/5.02  
% 34.93/5.02  fof(f12,axiom,(
% 34.93/5.02    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f28,plain,(
% 34.93/5.02    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 34.93/5.02    inference(ennf_transformation,[],[f12])).
% 34.93/5.02  
% 34.93/5.02  fof(f29,plain,(
% 34.93/5.02    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 34.93/5.02    inference(flattening,[],[f28])).
% 34.93/5.02  
% 34.93/5.02  fof(f68,plain,(
% 34.93/5.02    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 34.93/5.02    inference(cnf_transformation,[],[f29])).
% 34.93/5.02  
% 34.93/5.02  fof(f9,axiom,(
% 34.93/5.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f65,plain,(
% 34.93/5.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 34.93/5.02    inference(cnf_transformation,[],[f9])).
% 34.93/5.02  
% 34.93/5.02  fof(f5,axiom,(
% 34.93/5.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f46,plain,(
% 34.93/5.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 34.93/5.02    inference(nnf_transformation,[],[f5])).
% 34.93/5.02  
% 34.93/5.02  fof(f59,plain,(
% 34.93/5.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 34.93/5.02    inference(cnf_transformation,[],[f46])).
% 34.93/5.02  
% 34.93/5.02  fof(f6,axiom,(
% 34.93/5.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f23,plain,(
% 34.93/5.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 34.93/5.02    inference(ennf_transformation,[],[f6])).
% 34.93/5.02  
% 34.93/5.02  fof(f61,plain,(
% 34.93/5.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 34.93/5.02    inference(cnf_transformation,[],[f23])).
% 34.93/5.02  
% 34.93/5.02  fof(f60,plain,(
% 34.93/5.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 34.93/5.02    inference(cnf_transformation,[],[f46])).
% 34.93/5.02  
% 34.93/5.02  fof(f1,axiom,(
% 34.93/5.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f42,plain,(
% 34.93/5.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 34.93/5.02    inference(nnf_transformation,[],[f1])).
% 34.93/5.02  
% 34.93/5.02  fof(f43,plain,(
% 34.93/5.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 34.93/5.02    inference(flattening,[],[f42])).
% 34.93/5.02  
% 34.93/5.02  fof(f52,plain,(
% 34.93/5.02    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 34.93/5.02    inference(cnf_transformation,[],[f43])).
% 34.93/5.02  
% 34.93/5.02  fof(f87,plain,(
% 34.93/5.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 34.93/5.02    inference(equality_resolution,[],[f52])).
% 34.93/5.02  
% 34.93/5.02  fof(f4,axiom,(
% 34.93/5.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f44,plain,(
% 34.93/5.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 34.93/5.02    inference(nnf_transformation,[],[f4])).
% 34.93/5.02  
% 34.93/5.02  fof(f45,plain,(
% 34.93/5.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 34.93/5.02    inference(flattening,[],[f44])).
% 34.93/5.02  
% 34.93/5.02  fof(f57,plain,(
% 34.93/5.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 34.93/5.02    inference(cnf_transformation,[],[f45])).
% 34.93/5.02  
% 34.93/5.02  fof(f90,plain,(
% 34.93/5.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 34.93/5.02    inference(equality_resolution,[],[f57])).
% 34.93/5.02  
% 34.93/5.02  fof(f15,axiom,(
% 34.93/5.02    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f32,plain,(
% 34.93/5.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 34.93/5.02    inference(ennf_transformation,[],[f15])).
% 34.93/5.02  
% 34.93/5.02  fof(f33,plain,(
% 34.93/5.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 34.93/5.02    inference(flattening,[],[f32])).
% 34.93/5.02  
% 34.93/5.02  fof(f71,plain,(
% 34.93/5.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 34.93/5.02    inference(cnf_transformation,[],[f33])).
% 34.93/5.02  
% 34.93/5.02  fof(f8,axiom,(
% 34.93/5.02    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f25,plain,(
% 34.93/5.02    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 34.93/5.02    inference(ennf_transformation,[],[f8])).
% 34.93/5.02  
% 34.93/5.02  fof(f64,plain,(
% 34.93/5.02    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 34.93/5.02    inference(cnf_transformation,[],[f25])).
% 34.93/5.02  
% 34.93/5.02  fof(f13,axiom,(
% 34.93/5.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f21,plain,(
% 34.93/5.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 34.93/5.02    inference(pure_predicate_removal,[],[f13])).
% 34.93/5.02  
% 34.93/5.02  fof(f30,plain,(
% 34.93/5.02    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 34.93/5.02    inference(ennf_transformation,[],[f21])).
% 34.93/5.02  
% 34.93/5.02  fof(f69,plain,(
% 34.93/5.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 34.93/5.02    inference(cnf_transformation,[],[f30])).
% 34.93/5.02  
% 34.93/5.02  fof(f7,axiom,(
% 34.93/5.02    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f24,plain,(
% 34.93/5.02    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 34.93/5.02    inference(ennf_transformation,[],[f7])).
% 34.93/5.02  
% 34.93/5.02  fof(f47,plain,(
% 34.93/5.02    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 34.93/5.02    inference(nnf_transformation,[],[f24])).
% 34.93/5.02  
% 34.93/5.02  fof(f62,plain,(
% 34.93/5.02    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 34.93/5.02    inference(cnf_transformation,[],[f47])).
% 34.93/5.02  
% 34.93/5.02  fof(f79,plain,(
% 34.93/5.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 34.93/5.02    inference(cnf_transformation,[],[f37])).
% 34.93/5.02  
% 34.93/5.02  fof(f74,plain,(
% 34.93/5.02    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 34.93/5.02    inference(cnf_transformation,[],[f48])).
% 34.93/5.02  
% 34.93/5.02  fof(f86,plain,(
% 34.93/5.02    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 34.93/5.02    inference(cnf_transformation,[],[f50])).
% 34.93/5.02  
% 34.93/5.02  fof(f11,axiom,(
% 34.93/5.02    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f27,plain,(
% 34.93/5.02    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 34.93/5.02    inference(ennf_transformation,[],[f11])).
% 34.93/5.02  
% 34.93/5.02  fof(f67,plain,(
% 34.93/5.02    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 34.93/5.02    inference(cnf_transformation,[],[f27])).
% 34.93/5.02  
% 34.93/5.02  fof(f75,plain,(
% 34.93/5.02    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 34.93/5.02    inference(cnf_transformation,[],[f48])).
% 34.93/5.02  
% 34.93/5.02  fof(f94,plain,(
% 34.93/5.02    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 34.93/5.02    inference(equality_resolution,[],[f75])).
% 34.93/5.02  
% 34.93/5.02  fof(f77,plain,(
% 34.93/5.02    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 34.93/5.02    inference(cnf_transformation,[],[f48])).
% 34.93/5.02  
% 34.93/5.02  fof(f91,plain,(
% 34.93/5.02    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 34.93/5.02    inference(equality_resolution,[],[f77])).
% 34.93/5.02  
% 34.93/5.02  fof(f92,plain,(
% 34.93/5.02    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 34.93/5.02    inference(equality_resolution,[],[f91])).
% 34.93/5.02  
% 34.93/5.02  fof(f58,plain,(
% 34.93/5.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 34.93/5.02    inference(cnf_transformation,[],[f45])).
% 34.93/5.02  
% 34.93/5.02  fof(f89,plain,(
% 34.93/5.02    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 34.93/5.02    inference(equality_resolution,[],[f58])).
% 34.93/5.02  
% 34.93/5.02  fof(f85,plain,(
% 34.93/5.02    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 34.93/5.02    inference(cnf_transformation,[],[f50])).
% 34.93/5.02  
% 34.93/5.02  fof(f56,plain,(
% 34.93/5.02    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 34.93/5.02    inference(cnf_transformation,[],[f45])).
% 34.93/5.02  
% 34.93/5.02  fof(f3,axiom,(
% 34.93/5.02    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f22,plain,(
% 34.93/5.02    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 34.93/5.02    inference(ennf_transformation,[],[f3])).
% 34.93/5.02  
% 34.93/5.02  fof(f55,plain,(
% 34.93/5.02    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 34.93/5.02    inference(cnf_transformation,[],[f22])).
% 34.93/5.02  
% 34.93/5.02  fof(f10,axiom,(
% 34.93/5.02    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f26,plain,(
% 34.93/5.02    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 34.93/5.02    inference(ennf_transformation,[],[f10])).
% 34.93/5.02  
% 34.93/5.02  fof(f66,plain,(
% 34.93/5.02    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 34.93/5.02    inference(cnf_transformation,[],[f26])).
% 34.93/5.02  
% 34.93/5.02  fof(f2,axiom,(
% 34.93/5.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 34.93/5.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 34.93/5.02  
% 34.93/5.02  fof(f54,plain,(
% 34.93/5.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 34.93/5.02    inference(cnf_transformation,[],[f2])).
% 34.93/5.02  
% 34.93/5.02  cnf(c_33,negated_conjecture,
% 34.93/5.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 34.93/5.02      inference(cnf_transformation,[],[f83]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1481,plain,
% 34.93/5.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_29,plain,
% 34.93/5.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 34.93/5.02      | ~ v1_funct_1(X0)
% 34.93/5.02      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 34.93/5.02      inference(cnf_transformation,[],[f80]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1483,plain,
% 34.93/5.02      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 34.93/5.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 34.93/5.02      | v1_funct_1(X2) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_4211,plain,
% 34.93/5.02      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 34.93/5.02      | v1_funct_1(sK3) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_1481,c_1483]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_35,negated_conjecture,
% 34.93/5.02      ( v1_funct_1(sK3) ),
% 34.93/5.02      inference(cnf_transformation,[],[f81]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_36,plain,
% 34.93/5.02      ( v1_funct_1(sK3) = iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_4430,plain,
% 34.93/5.02      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 34.93/5.02      inference(global_propositional_subsumption,
% 34.93/5.02                [status(thm)],
% 34.93/5.02                [c_4211,c_36]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_28,plain,
% 34.93/5.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 34.93/5.02      | ~ v1_funct_1(X0)
% 34.93/5.02      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 34.93/5.02      inference(cnf_transformation,[],[f78]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1484,plain,
% 34.93/5.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 34.93/5.02      | v1_funct_1(X0) != iProver_top
% 34.93/5.02      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_2695,plain,
% 34.93/5.02      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 34.93/5.02      | v1_funct_1(sK3) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_1481,c_1484]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_2970,plain,
% 34.93/5.02      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 34.93/5.02      inference(global_propositional_subsumption,
% 34.93/5.02                [status(thm)],
% 34.93/5.02                [c_2695,c_36]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_4436,plain,
% 34.93/5.02      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 34.93/5.02      inference(demodulation,[status(thm)],[c_4430,c_2970]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_32,negated_conjecture,
% 34.93/5.02      ( r1_tarski(sK2,sK0) ),
% 34.93/5.02      inference(cnf_transformation,[],[f84]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1482,plain,
% 34.93/5.02      ( r1_tarski(sK2,sK0) = iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_26,plain,
% 34.93/5.02      ( ~ v1_funct_2(X0,X1,X2)
% 34.93/5.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 34.93/5.02      | k1_relset_1(X1,X2,X0) = X1
% 34.93/5.02      | k1_xboole_0 = X2 ),
% 34.93/5.02      inference(cnf_transformation,[],[f72]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_34,negated_conjecture,
% 34.93/5.02      ( v1_funct_2(sK3,sK0,sK1) ),
% 34.93/5.02      inference(cnf_transformation,[],[f82]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_546,plain,
% 34.93/5.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 34.93/5.02      | k1_relset_1(X1,X2,X0) = X1
% 34.93/5.02      | sK3 != X0
% 34.93/5.02      | sK1 != X2
% 34.93/5.02      | sK0 != X1
% 34.93/5.02      | k1_xboole_0 = X2 ),
% 34.93/5.02      inference(resolution_lifted,[status(thm)],[c_26,c_34]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_547,plain,
% 34.93/5.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 34.93/5.02      | k1_relset_1(sK0,sK1,sK3) = sK0
% 34.93/5.02      | k1_xboole_0 = sK1 ),
% 34.93/5.02      inference(unflattening,[status(thm)],[c_546]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_549,plain,
% 34.93/5.02      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 34.93/5.02      inference(global_propositional_subsumption,
% 34.93/5.02                [status(thm)],
% 34.93/5.02                [c_547,c_33]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_19,plain,
% 34.93/5.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 34.93/5.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 34.93/5.02      inference(cnf_transformation,[],[f70]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1487,plain,
% 34.93/5.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 34.93/5.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_2842,plain,
% 34.93/5.02      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_1481,c_1487]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_2908,plain,
% 34.93/5.02      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_549,c_2842]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_17,plain,
% 34.93/5.02      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 34.93/5.02      | ~ v1_relat_1(X1)
% 34.93/5.02      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 34.93/5.02      inference(cnf_transformation,[],[f68]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1488,plain,
% 34.93/5.02      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 34.93/5.02      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 34.93/5.02      | v1_relat_1(X0) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_3498,plain,
% 34.93/5.02      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 34.93/5.02      | sK1 = k1_xboole_0
% 34.93/5.02      | r1_tarski(X0,sK0) != iProver_top
% 34.93/5.02      | v1_relat_1(sK3) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_2908,c_1488]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_14,plain,
% 34.93/5.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 34.93/5.02      inference(cnf_transformation,[],[f65]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1491,plain,
% 34.93/5.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_9,plain,
% 34.93/5.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 34.93/5.02      inference(cnf_transformation,[],[f59]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1493,plain,
% 34.93/5.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 34.93/5.02      | r1_tarski(X0,X1) = iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_2394,plain,
% 34.93/5.02      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_1481,c_1493]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_10,plain,
% 34.93/5.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 34.93/5.02      | ~ v1_relat_1(X1)
% 34.93/5.02      | v1_relat_1(X0) ),
% 34.93/5.02      inference(cnf_transformation,[],[f61]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_8,plain,
% 34.93/5.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 34.93/5.02      inference(cnf_transformation,[],[f60]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_253,plain,
% 34.93/5.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 34.93/5.02      inference(prop_impl,[status(thm)],[c_8]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_254,plain,
% 34.93/5.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 34.93/5.02      inference(renaming,[status(thm)],[c_253]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_317,plain,
% 34.93/5.02      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 34.93/5.02      inference(bin_hyper_res,[status(thm)],[c_10,c_254]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1479,plain,
% 34.93/5.02      ( r1_tarski(X0,X1) != iProver_top
% 34.93/5.02      | v1_relat_1(X1) != iProver_top
% 34.93/5.02      | v1_relat_1(X0) = iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_2397,plain,
% 34.93/5.02      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 34.93/5.02      | v1_relat_1(sK3) = iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_2394,c_1479]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_2445,plain,
% 34.93/5.02      ( v1_relat_1(sK3) = iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_1491,c_2397]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_3661,plain,
% 34.93/5.02      ( r1_tarski(X0,sK0) != iProver_top
% 34.93/5.02      | sK1 = k1_xboole_0
% 34.93/5.02      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 34.93/5.02      inference(global_propositional_subsumption,
% 34.93/5.02                [status(thm)],
% 34.93/5.02                [c_3498,c_2445]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_3662,plain,
% 34.93/5.02      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 34.93/5.02      | sK1 = k1_xboole_0
% 34.93/5.02      | r1_tarski(X0,sK0) != iProver_top ),
% 34.93/5.02      inference(renaming,[status(thm)],[c_3661]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_3670,plain,
% 34.93/5.02      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_1482,c_3662]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1,plain,
% 34.93/5.02      ( r1_tarski(X0,X0) ),
% 34.93/5.02      inference(cnf_transformation,[],[f87]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1497,plain,
% 34.93/5.02      ( r1_tarski(X0,X0) = iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_6,plain,
% 34.93/5.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 34.93/5.02      inference(cnf_transformation,[],[f90]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_20,plain,
% 34.93/5.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 34.93/5.02      | ~ r1_tarski(k1_relat_1(X0),X1)
% 34.93/5.02      | ~ r1_tarski(k2_relat_1(X0),X2)
% 34.93/5.02      | ~ v1_relat_1(X0) ),
% 34.93/5.02      inference(cnf_transformation,[],[f71]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1486,plain,
% 34.93/5.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 34.93/5.02      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 34.93/5.02      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 34.93/5.02      | v1_relat_1(X0) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_3806,plain,
% 34.93/5.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 34.93/5.02      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 34.93/5.02      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 34.93/5.02      | v1_relat_1(X0) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_6,c_1486]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_4979,plain,
% 34.93/5.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 34.93/5.02      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 34.93/5.02      | v1_relat_1(X0) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_1497,c_3806]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_16459,plain,
% 34.93/5.02      ( sK1 = k1_xboole_0
% 34.93/5.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 34.93/5.02      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 34.93/5.02      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_3670,c_4979]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_13,plain,
% 34.93/5.02      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 34.93/5.02      inference(cnf_transformation,[],[f64]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_2691,plain,
% 34.93/5.02      ( v1_relat_1(k7_relat_1(sK3,sK2)) | ~ v1_relat_1(sK3) ),
% 34.93/5.02      inference(instantiation,[status(thm)],[c_13]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_2692,plain,
% 34.93/5.02      ( v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
% 34.93/5.02      | v1_relat_1(sK3) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_2691]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_16576,plain,
% 34.93/5.02      ( r1_tarski(sK2,k1_xboole_0) != iProver_top
% 34.93/5.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 34.93/5.02      | sK1 = k1_xboole_0 ),
% 34.93/5.02      inference(global_propositional_subsumption,
% 34.93/5.02                [status(thm)],
% 34.93/5.02                [c_16459,c_2445,c_2692]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_16577,plain,
% 34.93/5.02      ( sK1 = k1_xboole_0
% 34.93/5.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 34.93/5.02      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 34.93/5.02      inference(renaming,[status(thm)],[c_16576]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_18,plain,
% 34.93/5.02      ( v5_relat_1(X0,X1)
% 34.93/5.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 34.93/5.02      inference(cnf_transformation,[],[f69]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_12,plain,
% 34.93/5.02      ( ~ v5_relat_1(X0,X1)
% 34.93/5.02      | r1_tarski(k2_relat_1(X0),X1)
% 34.93/5.02      | ~ v1_relat_1(X0) ),
% 34.93/5.02      inference(cnf_transformation,[],[f62]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_425,plain,
% 34.93/5.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 34.93/5.02      | r1_tarski(k2_relat_1(X0),X2)
% 34.93/5.02      | ~ v1_relat_1(X0) ),
% 34.93/5.02      inference(resolution,[status(thm)],[c_18,c_12]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1478,plain,
% 34.93/5.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 34.93/5.02      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 34.93/5.02      | v1_relat_1(X0) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1807,plain,
% 34.93/5.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 34.93/5.02      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 34.93/5.02      | v1_relat_1(X0) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_6,c_1478]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_16581,plain,
% 34.93/5.02      ( sK1 = k1_xboole_0
% 34.93/5.02      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) = iProver_top
% 34.93/5.02      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 34.93/5.02      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_16577,c_1807]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_16608,plain,
% 34.93/5.02      ( r1_tarski(sK2,k1_xboole_0) != iProver_top
% 34.93/5.02      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) = iProver_top
% 34.93/5.02      | sK1 = k1_xboole_0 ),
% 34.93/5.02      inference(global_propositional_subsumption,
% 34.93/5.02                [status(thm)],
% 34.93/5.02                [c_16581,c_2445,c_2692]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_16609,plain,
% 34.93/5.02      ( sK1 = k1_xboole_0
% 34.93/5.02      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) = iProver_top
% 34.93/5.02      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 34.93/5.02      inference(renaming,[status(thm)],[c_16608]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_27,plain,
% 34.93/5.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 34.93/5.02      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 34.93/5.02      | ~ v1_funct_1(X0) ),
% 34.93/5.02      inference(cnf_transformation,[],[f79]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1485,plain,
% 34.93/5.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 34.93/5.02      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 34.93/5.02      | v1_funct_1(X0) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_4443,plain,
% 34.93/5.02      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 34.93/5.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 34.93/5.02      | v1_funct_1(sK3) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_4430,c_1485]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_38,plain,
% 34.93/5.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_4583,plain,
% 34.93/5.02      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 34.93/5.02      inference(global_propositional_subsumption,
% 34.93/5.02                [status(thm)],
% 34.93/5.02                [c_4443,c_36,c_38]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_4594,plain,
% 34.93/5.02      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
% 34.93/5.02      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_4583,c_1478]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_3808,plain,
% 34.93/5.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 34.93/5.02      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 34.93/5.02      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 34.93/5.02      | v1_relat_1(X2) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_1486,c_1487]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_92859,plain,
% 34.93/5.02      ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 34.93/5.02      | sK1 = k1_xboole_0
% 34.93/5.02      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
% 34.93/5.02      | r1_tarski(sK2,X0) != iProver_top
% 34.93/5.02      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_3670,c_3808]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_93663,plain,
% 34.93/5.02      ( r1_tarski(sK2,X0) != iProver_top
% 34.93/5.02      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
% 34.93/5.02      | sK1 = k1_xboole_0
% 34.93/5.02      | k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
% 34.93/5.02      inference(global_propositional_subsumption,
% 34.93/5.02                [status(thm)],
% 34.93/5.02                [c_92859,c_2445,c_2692]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_93664,plain,
% 34.93/5.02      ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 34.93/5.02      | sK1 = k1_xboole_0
% 34.93/5.02      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
% 34.93/5.02      | r1_tarski(sK2,X0) != iProver_top ),
% 34.93/5.02      inference(renaming,[status(thm)],[c_93663]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_93672,plain,
% 34.93/5.02      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 34.93/5.02      | sK1 = k1_xboole_0
% 34.93/5.02      | r1_tarski(sK2,X0) != iProver_top
% 34.93/5.02      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_4594,c_93664]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_94129,plain,
% 34.93/5.02      ( r1_tarski(sK2,X0) != iProver_top
% 34.93/5.02      | sK1 = k1_xboole_0
% 34.93/5.02      | k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
% 34.93/5.02      inference(global_propositional_subsumption,
% 34.93/5.02                [status(thm)],
% 34.93/5.02                [c_93672,c_2445,c_2692]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_94130,plain,
% 34.93/5.02      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 34.93/5.02      | sK1 = k1_xboole_0
% 34.93/5.02      | r1_tarski(sK2,X0) != iProver_top ),
% 34.93/5.02      inference(renaming,[status(thm)],[c_94129]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_94135,plain,
% 34.93/5.02      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 34.93/5.02      | sK1 = k1_xboole_0 ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_1497,c_94130]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_24,plain,
% 34.93/5.02      ( v1_funct_2(X0,X1,X2)
% 34.93/5.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 34.93/5.02      | k1_relset_1(X1,X2,X0) != X1
% 34.93/5.02      | k1_xboole_0 = X2 ),
% 34.93/5.02      inference(cnf_transformation,[],[f74]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_30,negated_conjecture,
% 34.93/5.02      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 34.93/5.02      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 34.93/5.02      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 34.93/5.02      inference(cnf_transformation,[],[f86]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_530,plain,
% 34.93/5.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 34.93/5.02      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 34.93/5.02      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 34.93/5.02      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 34.93/5.02      | k1_relset_1(X1,X2,X0) != X1
% 34.93/5.02      | sK2 != X1
% 34.93/5.02      | sK1 != X2
% 34.93/5.02      | k1_xboole_0 = X2 ),
% 34.93/5.02      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_531,plain,
% 34.93/5.02      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 34.93/5.02      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 34.93/5.02      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 34.93/5.02      | k1_xboole_0 = sK1 ),
% 34.93/5.02      inference(unflattening,[status(thm)],[c_530]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1473,plain,
% 34.93/5.02      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 34.93/5.02      | k1_xboole_0 = sK1
% 34.93/5.02      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 34.93/5.02      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_4435,plain,
% 34.93/5.02      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 34.93/5.02      | sK1 = k1_xboole_0
% 34.93/5.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 34.93/5.02      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(demodulation,[status(thm)],[c_4430,c_1473]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_94484,plain,
% 34.93/5.02      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 34.93/5.02      | sK1 = k1_xboole_0
% 34.93/5.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 34.93/5.02      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_94135,c_4435]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_94639,plain,
% 34.93/5.02      ( sK1 = k1_xboole_0
% 34.93/5.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 34.93/5.02      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(global_propositional_subsumption,
% 34.93/5.02                [status(thm)],
% 34.93/5.02                [c_94484,c_3670]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_94644,plain,
% 34.93/5.02      ( sK1 = k1_xboole_0
% 34.93/5.02      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top
% 34.93/5.02      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 34.93/5.02      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 34.93/5.02      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_1486,c_94639]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_16,plain,
% 34.93/5.02      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 34.93/5.02      inference(cnf_transformation,[],[f67]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_47255,plain,
% 34.93/5.02      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 34.93/5.02      | ~ v1_relat_1(sK3) ),
% 34.93/5.02      inference(instantiation,[status(thm)],[c_16]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_47257,plain,
% 34.93/5.02      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
% 34.93/5.02      | v1_relat_1(sK3) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_47255]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_97325,plain,
% 34.93/5.02      ( v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 34.93/5.02      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 34.93/5.02      | sK1 = k1_xboole_0 ),
% 34.93/5.02      inference(global_propositional_subsumption,
% 34.93/5.02                [status(thm)],
% 34.93/5.02                [c_94644,c_2445,c_2692,c_47257]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_97326,plain,
% 34.93/5.02      ( sK1 = k1_xboole_0
% 34.93/5.02      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 34.93/5.02      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(renaming,[status(thm)],[c_97325]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_97331,plain,
% 34.93/5.02      ( sK1 = k1_xboole_0
% 34.93/5.02      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 34.93/5.02      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_16609,c_97326]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_97330,plain,
% 34.93/5.02      ( sK1 = k1_xboole_0
% 34.93/5.02      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 34.93/5.02      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_4594,c_97326]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_97395,plain,
% 34.93/5.02      ( sK1 = k1_xboole_0
% 34.93/5.02      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(global_propositional_subsumption,
% 34.93/5.02                [status(thm)],
% 34.93/5.02                [c_97331,c_2445,c_2692,c_97330]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_97399,plain,
% 34.93/5.02      ( sK1 = k1_xboole_0 ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_4436,c_97395]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_23,plain,
% 34.93/5.02      ( v1_funct_2(X0,k1_xboole_0,X1)
% 34.93/5.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 34.93/5.02      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 34.93/5.02      inference(cnf_transformation,[],[f94]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_498,plain,
% 34.93/5.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 34.93/5.02      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 34.93/5.02      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 34.93/5.02      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 34.93/5.02      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 34.93/5.02      | sK2 != k1_xboole_0
% 34.93/5.02      | sK1 != X1 ),
% 34.93/5.02      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_499,plain,
% 34.93/5.02      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 34.93/5.02      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 34.93/5.02      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 34.93/5.02      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 34.93/5.02      | sK2 != k1_xboole_0 ),
% 34.93/5.02      inference(unflattening,[status(thm)],[c_498]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1475,plain,
% 34.93/5.02      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 34.93/5.02      | sK2 != k1_xboole_0
% 34.93/5.02      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 34.93/5.02      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 34.93/5.02      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1502,plain,
% 34.93/5.02      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 34.93/5.02      | sK2 != k1_xboole_0
% 34.93/5.02      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 34.93/5.02      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 34.93/5.02      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(demodulation,[status(thm)],[c_1475,c_6]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1764,plain,
% 34.93/5.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 34.93/5.02      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 34.93/5.02      | ~ v1_funct_1(sK3) ),
% 34.93/5.02      inference(instantiation,[status(thm)],[c_28]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1765,plain,
% 34.93/5.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 34.93/5.02      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 34.93/5.02      | v1_funct_1(sK3) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_1764]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1960,plain,
% 34.93/5.02      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 34.93/5.02      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 34.93/5.02      | sK2 != k1_xboole_0
% 34.93/5.02      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
% 34.93/5.02      inference(global_propositional_subsumption,
% 34.93/5.02                [status(thm)],
% 34.93/5.02                [c_1502,c_36,c_38,c_1765]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1961,plain,
% 34.93/5.02      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 34.93/5.02      | sK2 != k1_xboole_0
% 34.93/5.02      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 34.93/5.02      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 34.93/5.02      inference(renaming,[status(thm)],[c_1960]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_4433,plain,
% 34.93/5.02      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 34.93/5.02      | sK2 != k1_xboole_0
% 34.93/5.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 34.93/5.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 34.93/5.02      inference(demodulation,[status(thm)],[c_4430,c_1961]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_98076,plain,
% 34.93/5.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 34.93/5.02      | sK2 != k1_xboole_0
% 34.93/5.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 34.93/5.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 34.93/5.02      inference(demodulation,[status(thm)],[c_97399,c_4433]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_21,plain,
% 34.93/5.02      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 34.93/5.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 34.93/5.02      | k1_xboole_0 = X0 ),
% 34.93/5.02      inference(cnf_transformation,[],[f92]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_452,plain,
% 34.93/5.02      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 34.93/5.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 34.93/5.02      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 34.93/5.02      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 34.93/5.02      | sK2 != X0
% 34.93/5.02      | sK1 != k1_xboole_0
% 34.93/5.02      | k1_xboole_0 = X0 ),
% 34.93/5.02      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_453,plain,
% 34.93/5.02      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 34.93/5.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 34.93/5.02      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 34.93/5.02      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 34.93/5.02      | sK1 != k1_xboole_0
% 34.93/5.02      | k1_xboole_0 = sK2 ),
% 34.93/5.02      inference(unflattening,[status(thm)],[c_452]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1477,plain,
% 34.93/5.02      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 34.93/5.02      | sK1 != k1_xboole_0
% 34.93/5.02      | k1_xboole_0 = sK2
% 34.93/5.02      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 34.93/5.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 34.93/5.02      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_5,plain,
% 34.93/5.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 34.93/5.02      inference(cnf_transformation,[],[f89]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1501,plain,
% 34.93/5.02      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 34.93/5.02      | sK2 = k1_xboole_0
% 34.93/5.02      | sK1 != k1_xboole_0
% 34.93/5.02      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 34.93/5.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 34.93/5.02      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 34.93/5.02      inference(demodulation,[status(thm)],[c_1477,c_5]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_31,negated_conjecture,
% 34.93/5.02      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 34.93/5.02      inference(cnf_transformation,[],[f85]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_7,plain,
% 34.93/5.02      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 34.93/5.02      | k1_xboole_0 = X0
% 34.93/5.02      | k1_xboole_0 = X1 ),
% 34.93/5.02      inference(cnf_transformation,[],[f56]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_105,plain,
% 34.93/5.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 34.93/5.02      | k1_xboole_0 = k1_xboole_0 ),
% 34.93/5.02      inference(instantiation,[status(thm)],[c_7]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_106,plain,
% 34.93/5.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 34.93/5.02      inference(instantiation,[status(thm)],[c_6]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_858,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1546,plain,
% 34.93/5.02      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 34.93/5.02      inference(instantiation,[status(thm)],[c_858]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1595,plain,
% 34.93/5.02      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 34.93/5.02      inference(instantiation,[status(thm)],[c_1546]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_4,plain,
% 34.93/5.02      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 34.93/5.02      inference(cnf_transformation,[],[f55]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1661,plain,
% 34.93/5.02      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 34.93/5.02      inference(instantiation,[status(thm)],[c_4]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_857,plain,( X0 = X0 ),theory(equality) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1750,plain,
% 34.93/5.02      ( sK2 = sK2 ),
% 34.93/5.02      inference(instantiation,[status(thm)],[c_857]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1762,plain,
% 34.93/5.02      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 34.93/5.02      inference(instantiation,[status(thm)],[c_858]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1763,plain,
% 34.93/5.02      ( sK1 != k1_xboole_0
% 34.93/5.02      | k1_xboole_0 = sK1
% 34.93/5.02      | k1_xboole_0 != k1_xboole_0 ),
% 34.93/5.02      inference(instantiation,[status(thm)],[c_1762]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_859,plain,
% 34.93/5.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 34.93/5.02      theory(equality) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1568,plain,
% 34.93/5.02      ( ~ r1_tarski(X0,X1)
% 34.93/5.02      | r1_tarski(sK2,k1_xboole_0)
% 34.93/5.02      | sK2 != X0
% 34.93/5.02      | k1_xboole_0 != X1 ),
% 34.93/5.02      inference(instantiation,[status(thm)],[c_859]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1645,plain,
% 34.93/5.02      ( ~ r1_tarski(sK2,X0)
% 34.93/5.02      | r1_tarski(sK2,k1_xboole_0)
% 34.93/5.02      | sK2 != sK2
% 34.93/5.02      | k1_xboole_0 != X0 ),
% 34.93/5.02      inference(instantiation,[status(thm)],[c_1568]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1894,plain,
% 34.93/5.02      ( ~ r1_tarski(sK2,sK0)
% 34.93/5.02      | r1_tarski(sK2,k1_xboole_0)
% 34.93/5.02      | sK2 != sK2
% 34.93/5.02      | k1_xboole_0 != sK0 ),
% 34.93/5.02      inference(instantiation,[status(thm)],[c_1645]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1957,plain,
% 34.93/5.02      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 34.93/5.02      inference(global_propositional_subsumption,
% 34.93/5.02                [status(thm)],
% 34.93/5.02                [c_1501,c_32,c_31,c_105,c_106,c_1595,c_1661,c_1750,
% 34.93/5.02                 c_1763,c_1894]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1958,plain,
% 34.93/5.02      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 34.93/5.02      inference(renaming,[status(thm)],[c_1957]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_98094,plain,
% 34.93/5.02      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 34.93/5.02      inference(demodulation,[status(thm)],[c_97399,c_1958]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_98105,plain,
% 34.93/5.02      ( sK2 = k1_xboole_0 ),
% 34.93/5.02      inference(equality_resolution_simp,[status(thm)],[c_98094]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_98120,plain,
% 34.93/5.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 34.93/5.02      | k1_xboole_0 != k1_xboole_0
% 34.93/5.02      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 34.93/5.02      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 34.93/5.02      inference(demodulation,[status(thm)],[c_98076,c_98105]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_98121,plain,
% 34.93/5.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 34.93/5.02      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 34.93/5.02      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 34.93/5.02      inference(equality_resolution_simp,[status(thm)],[c_98120]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_15,plain,
% 34.93/5.02      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 34.93/5.02      inference(cnf_transformation,[],[f66]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1490,plain,
% 34.93/5.02      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 34.93/5.02      | v1_relat_1(X0) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_2537,plain,
% 34.93/5.02      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_2445,c_1490]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_98122,plain,
% 34.93/5.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 34.93/5.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 34.93/5.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 34.93/5.02      inference(light_normalisation,[status(thm)],[c_98121,c_2537]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_3,plain,
% 34.93/5.02      ( r1_tarski(k1_xboole_0,X0) ),
% 34.93/5.02      inference(cnf_transformation,[],[f54]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1496,plain,
% 34.93/5.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1494,plain,
% 34.93/5.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 34.93/5.02      | r1_tarski(X0,X1) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_2841,plain,
% 34.93/5.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 34.93/5.02      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_1494,c_1487]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_7257,plain,
% 34.93/5.02      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_1496,c_2841]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1489,plain,
% 34.93/5.02      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 34.93/5.02      | v1_relat_1(X0) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_2830,plain,
% 34.93/5.02      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
% 34.93/5.02      | v1_relat_1(sK3) != iProver_top ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_2537,c_1489]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_3092,plain,
% 34.93/5.02      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 34.93/5.02      inference(global_propositional_subsumption,
% 34.93/5.02                [status(thm)],
% 34.93/5.02                [c_2830,c_2445]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_1495,plain,
% 34.93/5.02      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_3097,plain,
% 34.93/5.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 34.93/5.02      inference(superposition,[status(thm)],[c_3092,c_1495]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_7264,plain,
% 34.93/5.02      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 34.93/5.02      inference(light_normalisation,[status(thm)],[c_7257,c_3097]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_98123,plain,
% 34.93/5.02      ( k1_xboole_0 != k1_xboole_0
% 34.93/5.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 34.93/5.02      inference(demodulation,[status(thm)],[c_98122,c_6,c_7264]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_98124,plain,
% 34.93/5.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 34.93/5.02      inference(equality_resolution_simp,[status(thm)],[c_98123]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_110,plain,
% 34.93/5.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_112,plain,
% 34.93/5.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 34.93/5.02      inference(instantiation,[status(thm)],[c_110]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_102,plain,
% 34.93/5.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 34.93/5.02      | r1_tarski(X0,X1) != iProver_top ),
% 34.93/5.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(c_104,plain,
% 34.93/5.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 34.93/5.02      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 34.93/5.02      inference(instantiation,[status(thm)],[c_102]) ).
% 34.93/5.02  
% 34.93/5.02  cnf(contradiction,plain,
% 34.93/5.02      ( $false ),
% 34.93/5.02      inference(minisat,[status(thm)],[c_98124,c_112,c_104]) ).
% 34.93/5.02  
% 34.93/5.02  
% 34.93/5.02  % SZS output end CNFRefutation for theBenchmark.p
% 34.93/5.02  
% 34.93/5.02  ------                               Statistics
% 34.93/5.02  
% 34.93/5.02  ------ General
% 34.93/5.02  
% 34.93/5.02  abstr_ref_over_cycles:                  0
% 34.93/5.02  abstr_ref_under_cycles:                 0
% 34.93/5.02  gc_basic_clause_elim:                   0
% 34.93/5.02  forced_gc_time:                         0
% 34.93/5.02  parsing_time:                           0.027
% 34.93/5.02  unif_index_cands_time:                  0.
% 34.93/5.02  unif_index_add_time:                    0.
% 34.93/5.02  orderings_time:                         0.
% 34.93/5.02  out_proof_time:                         0.041
% 34.93/5.02  total_time:                             4.066
% 34.93/5.02  num_of_symbols:                         49
% 34.93/5.02  num_of_terms:                           111606
% 34.93/5.02  
% 34.93/5.02  ------ Preprocessing
% 34.93/5.02  
% 34.93/5.02  num_of_splits:                          0
% 34.93/5.02  num_of_split_atoms:                     0
% 34.93/5.02  num_of_reused_defs:                     0
% 34.93/5.02  num_eq_ax_congr_red:                    10
% 34.93/5.02  num_of_sem_filtered_clauses:            1
% 34.93/5.02  num_of_subtypes:                        0
% 34.93/5.02  monotx_restored_types:                  0
% 34.93/5.02  sat_num_of_epr_types:                   0
% 34.93/5.02  sat_num_of_non_cyclic_types:            0
% 34.93/5.02  sat_guarded_non_collapsed_types:        0
% 34.93/5.02  num_pure_diseq_elim:                    0
% 34.93/5.02  simp_replaced_by:                       0
% 34.93/5.02  res_preprocessed:                       156
% 34.93/5.02  prep_upred:                             0
% 34.93/5.02  prep_unflattend:                        33
% 34.93/5.02  smt_new_axioms:                         0
% 34.93/5.02  pred_elim_cands:                        4
% 34.93/5.02  pred_elim:                              2
% 34.93/5.02  pred_elim_cl:                           3
% 34.93/5.02  pred_elim_cycles:                       4
% 34.93/5.02  merged_defs:                            8
% 34.93/5.02  merged_defs_ncl:                        0
% 34.93/5.02  bin_hyper_res:                          9
% 34.93/5.02  prep_cycles:                            4
% 34.93/5.02  pred_elim_time:                         0.022
% 34.93/5.02  splitting_time:                         0.
% 34.93/5.02  sem_filter_time:                        0.
% 34.93/5.02  monotx_time:                            0.
% 34.93/5.02  subtype_inf_time:                       0.
% 34.93/5.02  
% 34.93/5.02  ------ Problem properties
% 34.93/5.02  
% 34.93/5.02  clauses:                                32
% 34.93/5.02  conjectures:                            4
% 34.93/5.02  epr:                                    8
% 34.93/5.02  horn:                                   29
% 34.93/5.02  ground:                                 11
% 34.93/5.02  unary:                                  8
% 34.93/5.02  binary:                                 9
% 34.93/5.02  lits:                                   80
% 34.93/5.02  lits_eq:                                29
% 34.93/5.02  fd_pure:                                0
% 34.93/5.02  fd_pseudo:                              0
% 34.93/5.02  fd_cond:                                2
% 34.93/5.02  fd_pseudo_cond:                         1
% 34.93/5.02  ac_symbols:                             0
% 34.93/5.02  
% 34.93/5.02  ------ Propositional Solver
% 34.93/5.02  
% 34.93/5.02  prop_solver_calls:                      48
% 34.93/5.02  prop_fast_solver_calls:                 4880
% 34.93/5.02  smt_solver_calls:                       0
% 34.93/5.02  smt_fast_solver_calls:                  0
% 34.93/5.02  prop_num_of_clauses:                    45167
% 34.93/5.02  prop_preprocess_simplified:             70293
% 34.93/5.02  prop_fo_subsumed:                       155
% 34.93/5.02  prop_solver_time:                       0.
% 34.93/5.02  smt_solver_time:                        0.
% 34.93/5.02  smt_fast_solver_time:                   0.
% 34.93/5.02  prop_fast_solver_time:                  0.
% 34.93/5.02  prop_unsat_core_time:                   0.005
% 34.93/5.02  
% 34.93/5.02  ------ QBF
% 34.93/5.02  
% 34.93/5.02  qbf_q_res:                              0
% 34.93/5.02  qbf_num_tautologies:                    0
% 34.93/5.02  qbf_prep_cycles:                        0
% 34.93/5.02  
% 34.93/5.02  ------ BMC1
% 34.93/5.02  
% 34.93/5.02  bmc1_current_bound:                     -1
% 34.93/5.02  bmc1_last_solved_bound:                 -1
% 34.93/5.02  bmc1_unsat_core_size:                   -1
% 34.93/5.02  bmc1_unsat_core_parents_size:           -1
% 34.93/5.02  bmc1_merge_next_fun:                    0
% 34.93/5.02  bmc1_unsat_core_clauses_time:           0.
% 34.93/5.02  
% 34.93/5.02  ------ Instantiation
% 34.93/5.02  
% 34.93/5.02  inst_num_of_clauses:                    8734
% 34.93/5.02  inst_num_in_passive:                    3521
% 34.93/5.02  inst_num_in_active:                     5790
% 34.93/5.02  inst_num_in_unprocessed:                2060
% 34.93/5.02  inst_num_of_loops:                      6179
% 34.93/5.02  inst_num_of_learning_restarts:          1
% 34.93/5.02  inst_num_moves_active_passive:          381
% 34.93/5.02  inst_lit_activity:                      0
% 34.93/5.02  inst_lit_activity_moves:                0
% 34.93/5.02  inst_num_tautologies:                   0
% 34.93/5.02  inst_num_prop_implied:                  0
% 34.93/5.02  inst_num_existing_simplified:           0
% 34.93/5.02  inst_num_eq_res_simplified:             0
% 34.93/5.02  inst_num_child_elim:                    0
% 34.93/5.02  inst_num_of_dismatching_blockings:      9016
% 34.93/5.02  inst_num_of_non_proper_insts:           15914
% 34.93/5.02  inst_num_of_duplicates:                 0
% 34.93/5.02  inst_inst_num_from_inst_to_res:         0
% 34.93/5.02  inst_dismatching_checking_time:         0.
% 34.93/5.02  
% 34.93/5.02  ------ Resolution
% 34.93/5.02  
% 34.93/5.02  res_num_of_clauses:                     44
% 34.93/5.02  res_num_in_passive:                     44
% 34.93/5.02  res_num_in_active:                      0
% 34.93/5.02  res_num_of_loops:                       160
% 34.93/5.02  res_forward_subset_subsumed:            585
% 34.93/5.02  res_backward_subset_subsumed:           0
% 34.93/5.02  res_forward_subsumed:                   0
% 34.93/5.02  res_backward_subsumed:                  0
% 34.93/5.02  res_forward_subsumption_resolution:     0
% 34.93/5.02  res_backward_subsumption_resolution:    0
% 34.93/5.02  res_clause_to_clause_subsumption:       35886
% 34.93/5.02  res_orphan_elimination:                 0
% 34.93/5.02  res_tautology_del:                      909
% 34.93/5.02  res_num_eq_res_simplified:              1
% 34.93/5.02  res_num_sel_changes:                    0
% 34.93/5.02  res_moves_from_active_to_pass:          0
% 34.93/5.02  
% 34.93/5.02  ------ Superposition
% 34.93/5.02  
% 34.93/5.02  sup_time_total:                         0.
% 34.93/5.02  sup_time_generating:                    0.
% 34.93/5.02  sup_time_sim_full:                      0.
% 34.93/5.02  sup_time_sim_immed:                     0.
% 34.93/5.02  
% 34.93/5.02  sup_num_of_clauses:                     3967
% 34.93/5.02  sup_num_in_active:                      310
% 34.93/5.02  sup_num_in_passive:                     3657
% 34.93/5.02  sup_num_of_loops:                       1235
% 34.93/5.02  sup_fw_superposition:                   5284
% 34.93/5.02  sup_bw_superposition:                   3476
% 34.93/5.02  sup_immediate_simplified:               4071
% 34.93/5.02  sup_given_eliminated:                   8
% 34.93/5.02  comparisons_done:                       0
% 34.93/5.02  comparisons_avoided:                    786
% 34.93/5.02  
% 34.93/5.02  ------ Simplifications
% 34.93/5.02  
% 34.93/5.02  
% 34.93/5.02  sim_fw_subset_subsumed:                 283
% 34.93/5.02  sim_bw_subset_subsumed:                 298
% 34.93/5.02  sim_fw_subsumed:                        855
% 34.93/5.02  sim_bw_subsumed:                        141
% 34.93/5.02  sim_fw_subsumption_res:                 0
% 34.93/5.02  sim_bw_subsumption_res:                 0
% 34.93/5.02  sim_tautology_del:                      171
% 34.93/5.02  sim_eq_tautology_del:                   1572
% 34.93/5.02  sim_eq_res_simp:                        7
% 34.93/5.02  sim_fw_demodulated:                     2477
% 34.93/5.02  sim_bw_demodulated:                     764
% 34.93/5.02  sim_light_normalised:                   2332
% 34.93/5.02  sim_joinable_taut:                      0
% 34.93/5.02  sim_joinable_simp:                      0
% 34.93/5.02  sim_ac_normalised:                      0
% 34.93/5.02  sim_smt_subsumption:                    0
% 34.93/5.02  
%------------------------------------------------------------------------------
