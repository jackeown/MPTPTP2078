%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:58 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :  233 (5338 expanded)
%              Number of clauses        :  154 (1974 expanded)
%              Number of leaves         :   20 ( 950 expanded)
%              Depth                    :   32
%              Number of atoms          :  714 (27699 expanded)
%              Number of equality atoms :  431 (8991 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f45,plain,
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

fof(f46,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f45])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f75,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f46])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f83,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f53])).

fof(f76,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f46])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f86,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1027,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1029,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3165,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1027,c_1029])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3316,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3165,c_31])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1030,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1697,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1027,c_1030])).

cnf(c_1855,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1697,c_31])).

cnf(c_3323,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3316,c_1855])).

cnf(c_10,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1036,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1040,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1028,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_417,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_419,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_28])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1034,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1784,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1027,c_1034])).

cnf(c_1852,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_419,c_1784])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1035,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2298,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1852,c_1035])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1037,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1038,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2105,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1027,c_1038])).

cnf(c_2382,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_2105])).

cnf(c_2442,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2298,c_2382])).

cnf(c_2443,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2442])).

cnf(c_2450,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1028,c_2443])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1032,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2689,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1027,c_1032])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1033,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3097,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2689,c_1033])).

cnf(c_4041,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3097,c_1032])).

cnf(c_8802,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2450,c_4041])).

cnf(c_4039,plain,
    ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
    | r1_tarski(X1,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3097,c_1034])).

cnf(c_6779,plain,
    ( k1_relset_1(k1_relat_1(X0),sK1,X0) = k1_relat_1(X0)
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_4039])).

cnf(c_6856,plain,
    ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0))
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1036,c_6779])).

cnf(c_11271,plain,
    ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6856,c_2382])).

cnf(c_11274,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2450,c_11271])).

cnf(c_19,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_401,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_1020,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_3322,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3316,c_1020])).

cnf(c_11447,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11274,c_3322])).

cnf(c_12067,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11447,c_2450])).

cnf(c_12074,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8802,c_12067])).

cnf(c_1264,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1265,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1264])).

cnf(c_13260,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
    | sK1 = k1_xboole_0
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12074,c_1265])).

cnf(c_13261,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13260])).

cnf(c_13264,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_13261])).

cnf(c_13405,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1036,c_13264])).

cnf(c_13442,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13405,c_2382])).

cnf(c_13443,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13442])).

cnf(c_13446,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3323,c_13443])).

cnf(c_16,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_322,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_323,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_1024,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1044,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1024,c_4])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1251,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1252,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1251])).

cnf(c_1449,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1044,c_31,c_33,c_1252])).

cnf(c_1450,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1449])).

cnf(c_3320,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3316,c_1450])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_84,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_85,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_636,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1085,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_1123,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1176,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1249,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_1250,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1249])).

cnf(c_635,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1260,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_635])).

cnf(c_637,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1101,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_1160,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_1458,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1160])).

cnf(c_6050,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3320,c_27,c_26,c_84,c_85,c_1123,c_1176,c_1250,c_1260,c_1458])).

cnf(c_13747,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13446,c_6050])).

cnf(c_13820,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_13747])).

cnf(c_427,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_503,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_427])).

cnf(c_1019,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_3321,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3316,c_1019])).

cnf(c_13749,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13446,c_3321])).

cnf(c_13781,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13446,c_26])).

cnf(c_13782,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_13781])).

cnf(c_13817,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13749,c_13782])).

cnf(c_13818,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13817,c_4])).

cnf(c_13821,plain,
    ( k7_relat_1(sK3,k1_xboole_0) != sK3
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13820,c_13818])).

cnf(c_13829,plain,
    ( k7_relat_1(sK3,k1_xboole_0) != sK3
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13821])).

cnf(c_13776,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_13446,c_1784])).

cnf(c_13788,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_13776,c_13782])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_388,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_1021,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_1042,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1021,c_5])).

cnf(c_13778,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13446,c_1042])).

cnf(c_13785,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13778,c_13782])).

cnf(c_13786,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13785])).

cnf(c_13789,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13788,c_13786])).

cnf(c_13780,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13446,c_1027])).

cnf(c_13783,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13780,c_13782])).

cnf(c_13784,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13783,c_5])).

cnf(c_4038,plain,
    ( k2_partfun1(X0,sK1,X1,X2) = k7_relat_1(X1,X2)
    | r1_tarski(X1,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3097,c_1029])).

cnf(c_8299,plain,
    ( k2_partfun1(k1_relat_1(X0),sK1,X0,X1) = k7_relat_1(X0,X1)
    | r1_tarski(X0,sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_4038])).

cnf(c_13448,plain,
    ( k2_partfun1(k1_relat_1(X0),k1_xboole_0,X0,X1) = k7_relat_1(X0,X1)
    | r1_tarski(X0,sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8299,c_13446])).

cnf(c_13452,plain,
    ( k2_partfun1(k1_relat_1(sK3),k1_xboole_0,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_13448])).

cnf(c_13652,plain,
    ( k2_partfun1(k1_relat_1(sK3),k1_xboole_0,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13452,c_31])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1031,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2176,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,k1_xboole_0,X0,X2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1031])).

cnf(c_2183,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(X1,k1_xboole_0,X0,X2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2176,c_4])).

cnf(c_13659,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13652,c_2183])).

cnf(c_13667,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13659])).

cnf(c_3096,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1027,c_1033])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_296,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_12,c_9])).

cnf(c_1025,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_3344,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3096,c_1025])).

cnf(c_3358,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3344])).

cnf(c_3360,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,k1_xboole_0) = sK3 ),
    inference(instantiation,[status(thm)],[c_3358])).

cnf(c_3329,plain,
    ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3323])).

cnf(c_2383,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2382])).

cnf(c_1377,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_relat_1(sK3) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_1379,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_90,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13829,c_13789,c_13784,c_13667,c_3360,c_3329,c_2383,c_1379,c_90,c_85,c_84,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:55:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.75/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.75/1.52  
% 7.75/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.75/1.52  
% 7.75/1.52  ------  iProver source info
% 7.75/1.52  
% 7.75/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.75/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.75/1.52  git: non_committed_changes: false
% 7.75/1.52  git: last_make_outside_of_git: false
% 7.75/1.52  
% 7.75/1.52  ------ 
% 7.75/1.52  
% 7.75/1.52  ------ Input Options
% 7.75/1.52  
% 7.75/1.52  --out_options                           all
% 7.75/1.52  --tptp_safe_out                         true
% 7.75/1.52  --problem_path                          ""
% 7.75/1.52  --include_path                          ""
% 7.75/1.52  --clausifier                            res/vclausify_rel
% 7.75/1.52  --clausifier_options                    ""
% 7.75/1.52  --stdin                                 false
% 7.75/1.52  --stats_out                             all
% 7.75/1.52  
% 7.75/1.52  ------ General Options
% 7.75/1.52  
% 7.75/1.52  --fof                                   false
% 7.75/1.52  --time_out_real                         305.
% 7.75/1.52  --time_out_virtual                      -1.
% 7.75/1.52  --symbol_type_check                     false
% 7.75/1.52  --clausify_out                          false
% 7.75/1.52  --sig_cnt_out                           false
% 7.75/1.52  --trig_cnt_out                          false
% 7.75/1.52  --trig_cnt_out_tolerance                1.
% 7.75/1.52  --trig_cnt_out_sk_spl                   false
% 7.75/1.52  --abstr_cl_out                          false
% 7.75/1.52  
% 7.75/1.52  ------ Global Options
% 7.75/1.52  
% 7.75/1.52  --schedule                              default
% 7.75/1.52  --add_important_lit                     false
% 7.75/1.52  --prop_solver_per_cl                    1000
% 7.75/1.52  --min_unsat_core                        false
% 7.75/1.52  --soft_assumptions                      false
% 7.75/1.52  --soft_lemma_size                       3
% 7.75/1.52  --prop_impl_unit_size                   0
% 7.75/1.52  --prop_impl_unit                        []
% 7.75/1.52  --share_sel_clauses                     true
% 7.75/1.52  --reset_solvers                         false
% 7.75/1.52  --bc_imp_inh                            [conj_cone]
% 7.75/1.52  --conj_cone_tolerance                   3.
% 7.75/1.52  --extra_neg_conj                        none
% 7.75/1.52  --large_theory_mode                     true
% 7.75/1.52  --prolific_symb_bound                   200
% 7.75/1.52  --lt_threshold                          2000
% 7.75/1.52  --clause_weak_htbl                      true
% 7.75/1.52  --gc_record_bc_elim                     false
% 7.75/1.52  
% 7.75/1.52  ------ Preprocessing Options
% 7.75/1.52  
% 7.75/1.52  --preprocessing_flag                    true
% 7.75/1.52  --time_out_prep_mult                    0.1
% 7.75/1.52  --splitting_mode                        input
% 7.75/1.52  --splitting_grd                         true
% 7.75/1.52  --splitting_cvd                         false
% 7.75/1.52  --splitting_cvd_svl                     false
% 7.75/1.52  --splitting_nvd                         32
% 7.75/1.52  --sub_typing                            true
% 7.75/1.52  --prep_gs_sim                           true
% 7.75/1.52  --prep_unflatten                        true
% 7.75/1.52  --prep_res_sim                          true
% 7.75/1.52  --prep_upred                            true
% 7.75/1.52  --prep_sem_filter                       exhaustive
% 7.75/1.52  --prep_sem_filter_out                   false
% 7.75/1.52  --pred_elim                             true
% 7.75/1.52  --res_sim_input                         true
% 7.75/1.52  --eq_ax_congr_red                       true
% 7.75/1.52  --pure_diseq_elim                       true
% 7.75/1.52  --brand_transform                       false
% 7.75/1.52  --non_eq_to_eq                          false
% 7.75/1.52  --prep_def_merge                        true
% 7.75/1.52  --prep_def_merge_prop_impl              false
% 7.75/1.52  --prep_def_merge_mbd                    true
% 7.75/1.52  --prep_def_merge_tr_red                 false
% 7.75/1.52  --prep_def_merge_tr_cl                  false
% 7.75/1.52  --smt_preprocessing                     true
% 7.75/1.52  --smt_ac_axioms                         fast
% 7.75/1.52  --preprocessed_out                      false
% 7.75/1.52  --preprocessed_stats                    false
% 7.75/1.52  
% 7.75/1.52  ------ Abstraction refinement Options
% 7.75/1.52  
% 7.75/1.52  --abstr_ref                             []
% 7.75/1.52  --abstr_ref_prep                        false
% 7.75/1.52  --abstr_ref_until_sat                   false
% 7.75/1.52  --abstr_ref_sig_restrict                funpre
% 7.75/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.75/1.52  --abstr_ref_under                       []
% 7.75/1.52  
% 7.75/1.52  ------ SAT Options
% 7.75/1.52  
% 7.75/1.52  --sat_mode                              false
% 7.75/1.52  --sat_fm_restart_options                ""
% 7.75/1.52  --sat_gr_def                            false
% 7.75/1.52  --sat_epr_types                         true
% 7.75/1.52  --sat_non_cyclic_types                  false
% 7.75/1.52  --sat_finite_models                     false
% 7.75/1.52  --sat_fm_lemmas                         false
% 7.75/1.52  --sat_fm_prep                           false
% 7.75/1.52  --sat_fm_uc_incr                        true
% 7.75/1.52  --sat_out_model                         small
% 7.75/1.52  --sat_out_clauses                       false
% 7.75/1.52  
% 7.75/1.52  ------ QBF Options
% 7.75/1.52  
% 7.75/1.52  --qbf_mode                              false
% 7.75/1.52  --qbf_elim_univ                         false
% 7.75/1.52  --qbf_dom_inst                          none
% 7.75/1.52  --qbf_dom_pre_inst                      false
% 7.75/1.52  --qbf_sk_in                             false
% 7.75/1.52  --qbf_pred_elim                         true
% 7.75/1.52  --qbf_split                             512
% 7.75/1.52  
% 7.75/1.52  ------ BMC1 Options
% 7.75/1.52  
% 7.75/1.52  --bmc1_incremental                      false
% 7.75/1.52  --bmc1_axioms                           reachable_all
% 7.75/1.52  --bmc1_min_bound                        0
% 7.75/1.52  --bmc1_max_bound                        -1
% 7.75/1.52  --bmc1_max_bound_default                -1
% 7.75/1.52  --bmc1_symbol_reachability              true
% 7.75/1.52  --bmc1_property_lemmas                  false
% 7.75/1.52  --bmc1_k_induction                      false
% 7.75/1.52  --bmc1_non_equiv_states                 false
% 7.75/1.52  --bmc1_deadlock                         false
% 7.75/1.52  --bmc1_ucm                              false
% 7.75/1.52  --bmc1_add_unsat_core                   none
% 7.75/1.52  --bmc1_unsat_core_children              false
% 7.75/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.75/1.52  --bmc1_out_stat                         full
% 7.75/1.52  --bmc1_ground_init                      false
% 7.75/1.52  --bmc1_pre_inst_next_state              false
% 7.75/1.52  --bmc1_pre_inst_state                   false
% 7.75/1.52  --bmc1_pre_inst_reach_state             false
% 7.75/1.52  --bmc1_out_unsat_core                   false
% 7.75/1.52  --bmc1_aig_witness_out                  false
% 7.75/1.52  --bmc1_verbose                          false
% 7.75/1.52  --bmc1_dump_clauses_tptp                false
% 7.75/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.75/1.52  --bmc1_dump_file                        -
% 7.75/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.75/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.75/1.52  --bmc1_ucm_extend_mode                  1
% 7.75/1.52  --bmc1_ucm_init_mode                    2
% 7.75/1.52  --bmc1_ucm_cone_mode                    none
% 7.75/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.75/1.52  --bmc1_ucm_relax_model                  4
% 7.75/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.75/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.75/1.52  --bmc1_ucm_layered_model                none
% 7.75/1.52  --bmc1_ucm_max_lemma_size               10
% 7.75/1.52  
% 7.75/1.52  ------ AIG Options
% 7.75/1.52  
% 7.75/1.52  --aig_mode                              false
% 7.75/1.52  
% 7.75/1.52  ------ Instantiation Options
% 7.75/1.52  
% 7.75/1.52  --instantiation_flag                    true
% 7.75/1.52  --inst_sos_flag                         true
% 7.75/1.52  --inst_sos_phase                        true
% 7.75/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.75/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.75/1.52  --inst_lit_sel_side                     num_symb
% 7.75/1.52  --inst_solver_per_active                1400
% 7.75/1.52  --inst_solver_calls_frac                1.
% 7.75/1.52  --inst_passive_queue_type               priority_queues
% 7.75/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.75/1.52  --inst_passive_queues_freq              [25;2]
% 7.75/1.52  --inst_dismatching                      true
% 7.75/1.52  --inst_eager_unprocessed_to_passive     true
% 7.75/1.52  --inst_prop_sim_given                   true
% 7.75/1.52  --inst_prop_sim_new                     false
% 7.75/1.52  --inst_subs_new                         false
% 7.75/1.52  --inst_eq_res_simp                      false
% 7.75/1.52  --inst_subs_given                       false
% 7.75/1.52  --inst_orphan_elimination               true
% 7.75/1.52  --inst_learning_loop_flag               true
% 7.75/1.52  --inst_learning_start                   3000
% 7.75/1.52  --inst_learning_factor                  2
% 7.75/1.52  --inst_start_prop_sim_after_learn       3
% 7.75/1.52  --inst_sel_renew                        solver
% 7.75/1.52  --inst_lit_activity_flag                true
% 7.75/1.52  --inst_restr_to_given                   false
% 7.75/1.52  --inst_activity_threshold               500
% 7.75/1.52  --inst_out_proof                        true
% 7.75/1.52  
% 7.75/1.52  ------ Resolution Options
% 7.75/1.52  
% 7.75/1.52  --resolution_flag                       true
% 7.75/1.52  --res_lit_sel                           adaptive
% 7.75/1.52  --res_lit_sel_side                      none
% 7.75/1.52  --res_ordering                          kbo
% 7.75/1.52  --res_to_prop_solver                    active
% 7.75/1.52  --res_prop_simpl_new                    false
% 7.75/1.52  --res_prop_simpl_given                  true
% 7.75/1.52  --res_passive_queue_type                priority_queues
% 7.75/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.75/1.52  --res_passive_queues_freq               [15;5]
% 7.75/1.52  --res_forward_subs                      full
% 7.75/1.52  --res_backward_subs                     full
% 7.75/1.52  --res_forward_subs_resolution           true
% 7.75/1.52  --res_backward_subs_resolution          true
% 7.75/1.52  --res_orphan_elimination                true
% 7.75/1.52  --res_time_limit                        2.
% 7.75/1.52  --res_out_proof                         true
% 7.75/1.52  
% 7.75/1.52  ------ Superposition Options
% 7.75/1.52  
% 7.75/1.52  --superposition_flag                    true
% 7.75/1.52  --sup_passive_queue_type                priority_queues
% 7.75/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.75/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.75/1.52  --demod_completeness_check              fast
% 7.75/1.52  --demod_use_ground                      true
% 7.75/1.52  --sup_to_prop_solver                    passive
% 7.75/1.52  --sup_prop_simpl_new                    true
% 7.75/1.52  --sup_prop_simpl_given                  true
% 7.75/1.52  --sup_fun_splitting                     true
% 7.75/1.52  --sup_smt_interval                      50000
% 7.75/1.52  
% 7.75/1.52  ------ Superposition Simplification Setup
% 7.75/1.52  
% 7.75/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.75/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.75/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.75/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.75/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.75/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.75/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.75/1.52  --sup_immed_triv                        [TrivRules]
% 7.75/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.52  --sup_immed_bw_main                     []
% 7.75/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.75/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.75/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.52  --sup_input_bw                          []
% 7.75/1.52  
% 7.75/1.52  ------ Combination Options
% 7.75/1.52  
% 7.75/1.52  --comb_res_mult                         3
% 7.75/1.52  --comb_sup_mult                         2
% 7.75/1.52  --comb_inst_mult                        10
% 7.75/1.52  
% 7.75/1.52  ------ Debug Options
% 7.75/1.52  
% 7.75/1.52  --dbg_backtrace                         false
% 7.75/1.52  --dbg_dump_prop_clauses                 false
% 7.75/1.52  --dbg_dump_prop_clauses_file            -
% 7.75/1.52  --dbg_out_stat                          false
% 7.75/1.52  ------ Parsing...
% 7.75/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.75/1.52  
% 7.75/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.75/1.52  
% 7.75/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.75/1.52  
% 7.75/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.52  ------ Proving...
% 7.75/1.52  ------ Problem Properties 
% 7.75/1.52  
% 7.75/1.52  
% 7.75/1.52  clauses                                 28
% 7.75/1.52  conjectures                             4
% 7.75/1.52  EPR                                     6
% 7.75/1.52  Horn                                    25
% 7.75/1.52  unary                                   7
% 7.75/1.52  binary                                  5
% 7.75/1.52  lits                                    73
% 7.75/1.52  lits eq                                 29
% 7.75/1.52  fd_pure                                 0
% 7.75/1.52  fd_pseudo                               0
% 7.75/1.52  fd_cond                                 2
% 7.75/1.52  fd_pseudo_cond                          1
% 7.75/1.52  AC symbols                              0
% 7.75/1.52  
% 7.75/1.52  ------ Schedule dynamic 5 is on 
% 7.75/1.52  
% 7.75/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.75/1.52  
% 7.75/1.52  
% 7.75/1.52  ------ 
% 7.75/1.52  Current options:
% 7.75/1.52  ------ 
% 7.75/1.52  
% 7.75/1.52  ------ Input Options
% 7.75/1.52  
% 7.75/1.52  --out_options                           all
% 7.75/1.52  --tptp_safe_out                         true
% 7.75/1.52  --problem_path                          ""
% 7.75/1.52  --include_path                          ""
% 7.75/1.52  --clausifier                            res/vclausify_rel
% 7.75/1.52  --clausifier_options                    ""
% 7.75/1.52  --stdin                                 false
% 7.75/1.52  --stats_out                             all
% 7.75/1.52  
% 7.75/1.52  ------ General Options
% 7.75/1.52  
% 7.75/1.52  --fof                                   false
% 7.75/1.52  --time_out_real                         305.
% 7.75/1.52  --time_out_virtual                      -1.
% 7.75/1.52  --symbol_type_check                     false
% 7.75/1.52  --clausify_out                          false
% 7.75/1.52  --sig_cnt_out                           false
% 7.75/1.52  --trig_cnt_out                          false
% 7.75/1.52  --trig_cnt_out_tolerance                1.
% 7.75/1.52  --trig_cnt_out_sk_spl                   false
% 7.75/1.52  --abstr_cl_out                          false
% 7.75/1.52  
% 7.75/1.52  ------ Global Options
% 7.75/1.52  
% 7.75/1.52  --schedule                              default
% 7.75/1.52  --add_important_lit                     false
% 7.75/1.52  --prop_solver_per_cl                    1000
% 7.75/1.52  --min_unsat_core                        false
% 7.75/1.52  --soft_assumptions                      false
% 7.75/1.52  --soft_lemma_size                       3
% 7.75/1.52  --prop_impl_unit_size                   0
% 7.75/1.52  --prop_impl_unit                        []
% 7.75/1.52  --share_sel_clauses                     true
% 7.75/1.52  --reset_solvers                         false
% 7.75/1.52  --bc_imp_inh                            [conj_cone]
% 7.75/1.52  --conj_cone_tolerance                   3.
% 7.75/1.52  --extra_neg_conj                        none
% 7.75/1.52  --large_theory_mode                     true
% 7.75/1.52  --prolific_symb_bound                   200
% 7.75/1.52  --lt_threshold                          2000
% 7.75/1.52  --clause_weak_htbl                      true
% 7.75/1.52  --gc_record_bc_elim                     false
% 7.75/1.52  
% 7.75/1.52  ------ Preprocessing Options
% 7.75/1.52  
% 7.75/1.52  --preprocessing_flag                    true
% 7.75/1.52  --time_out_prep_mult                    0.1
% 7.75/1.52  --splitting_mode                        input
% 7.75/1.52  --splitting_grd                         true
% 7.75/1.52  --splitting_cvd                         false
% 7.75/1.52  --splitting_cvd_svl                     false
% 7.75/1.52  --splitting_nvd                         32
% 7.75/1.52  --sub_typing                            true
% 7.75/1.52  --prep_gs_sim                           true
% 7.75/1.52  --prep_unflatten                        true
% 7.75/1.52  --prep_res_sim                          true
% 7.75/1.52  --prep_upred                            true
% 7.75/1.52  --prep_sem_filter                       exhaustive
% 7.75/1.52  --prep_sem_filter_out                   false
% 7.75/1.52  --pred_elim                             true
% 7.75/1.52  --res_sim_input                         true
% 7.75/1.52  --eq_ax_congr_red                       true
% 7.75/1.52  --pure_diseq_elim                       true
% 7.75/1.52  --brand_transform                       false
% 7.75/1.52  --non_eq_to_eq                          false
% 7.75/1.52  --prep_def_merge                        true
% 7.75/1.52  --prep_def_merge_prop_impl              false
% 7.75/1.52  --prep_def_merge_mbd                    true
% 7.75/1.52  --prep_def_merge_tr_red                 false
% 7.75/1.52  --prep_def_merge_tr_cl                  false
% 7.75/1.52  --smt_preprocessing                     true
% 7.75/1.52  --smt_ac_axioms                         fast
% 7.75/1.52  --preprocessed_out                      false
% 7.75/1.52  --preprocessed_stats                    false
% 7.75/1.52  
% 7.75/1.52  ------ Abstraction refinement Options
% 7.75/1.52  
% 7.75/1.52  --abstr_ref                             []
% 7.75/1.52  --abstr_ref_prep                        false
% 7.75/1.52  --abstr_ref_until_sat                   false
% 7.75/1.52  --abstr_ref_sig_restrict                funpre
% 7.75/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.75/1.52  --abstr_ref_under                       []
% 7.75/1.52  
% 7.75/1.52  ------ SAT Options
% 7.75/1.52  
% 7.75/1.52  --sat_mode                              false
% 7.75/1.52  --sat_fm_restart_options                ""
% 7.75/1.52  --sat_gr_def                            false
% 7.75/1.52  --sat_epr_types                         true
% 7.75/1.52  --sat_non_cyclic_types                  false
% 7.75/1.52  --sat_finite_models                     false
% 7.75/1.52  --sat_fm_lemmas                         false
% 7.75/1.52  --sat_fm_prep                           false
% 7.75/1.52  --sat_fm_uc_incr                        true
% 7.75/1.52  --sat_out_model                         small
% 7.75/1.52  --sat_out_clauses                       false
% 7.75/1.52  
% 7.75/1.52  ------ QBF Options
% 7.75/1.52  
% 7.75/1.52  --qbf_mode                              false
% 7.75/1.52  --qbf_elim_univ                         false
% 7.75/1.52  --qbf_dom_inst                          none
% 7.75/1.52  --qbf_dom_pre_inst                      false
% 7.75/1.52  --qbf_sk_in                             false
% 7.75/1.52  --qbf_pred_elim                         true
% 7.75/1.52  --qbf_split                             512
% 7.75/1.52  
% 7.75/1.52  ------ BMC1 Options
% 7.75/1.52  
% 7.75/1.52  --bmc1_incremental                      false
% 7.75/1.52  --bmc1_axioms                           reachable_all
% 7.75/1.52  --bmc1_min_bound                        0
% 7.75/1.52  --bmc1_max_bound                        -1
% 7.75/1.52  --bmc1_max_bound_default                -1
% 7.75/1.52  --bmc1_symbol_reachability              true
% 7.75/1.52  --bmc1_property_lemmas                  false
% 7.75/1.52  --bmc1_k_induction                      false
% 7.75/1.52  --bmc1_non_equiv_states                 false
% 7.75/1.52  --bmc1_deadlock                         false
% 7.75/1.52  --bmc1_ucm                              false
% 7.75/1.52  --bmc1_add_unsat_core                   none
% 7.75/1.52  --bmc1_unsat_core_children              false
% 7.75/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.75/1.52  --bmc1_out_stat                         full
% 7.75/1.52  --bmc1_ground_init                      false
% 7.75/1.52  --bmc1_pre_inst_next_state              false
% 7.75/1.52  --bmc1_pre_inst_state                   false
% 7.75/1.52  --bmc1_pre_inst_reach_state             false
% 7.75/1.52  --bmc1_out_unsat_core                   false
% 7.75/1.52  --bmc1_aig_witness_out                  false
% 7.75/1.52  --bmc1_verbose                          false
% 7.75/1.52  --bmc1_dump_clauses_tptp                false
% 7.75/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.75/1.52  --bmc1_dump_file                        -
% 7.75/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.75/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.75/1.52  --bmc1_ucm_extend_mode                  1
% 7.75/1.52  --bmc1_ucm_init_mode                    2
% 7.75/1.52  --bmc1_ucm_cone_mode                    none
% 7.75/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.75/1.52  --bmc1_ucm_relax_model                  4
% 7.75/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.75/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.75/1.52  --bmc1_ucm_layered_model                none
% 7.75/1.52  --bmc1_ucm_max_lemma_size               10
% 7.75/1.52  
% 7.75/1.52  ------ AIG Options
% 7.75/1.52  
% 7.75/1.52  --aig_mode                              false
% 7.75/1.52  
% 7.75/1.52  ------ Instantiation Options
% 7.75/1.52  
% 7.75/1.52  --instantiation_flag                    true
% 7.75/1.52  --inst_sos_flag                         true
% 7.75/1.52  --inst_sos_phase                        true
% 7.75/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.75/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.75/1.52  --inst_lit_sel_side                     none
% 7.75/1.52  --inst_solver_per_active                1400
% 7.75/1.52  --inst_solver_calls_frac                1.
% 7.75/1.52  --inst_passive_queue_type               priority_queues
% 7.75/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.75/1.52  --inst_passive_queues_freq              [25;2]
% 7.75/1.52  --inst_dismatching                      true
% 7.75/1.52  --inst_eager_unprocessed_to_passive     true
% 7.75/1.52  --inst_prop_sim_given                   true
% 7.75/1.52  --inst_prop_sim_new                     false
% 7.75/1.52  --inst_subs_new                         false
% 7.75/1.52  --inst_eq_res_simp                      false
% 7.75/1.52  --inst_subs_given                       false
% 7.75/1.52  --inst_orphan_elimination               true
% 7.75/1.52  --inst_learning_loop_flag               true
% 7.75/1.52  --inst_learning_start                   3000
% 7.75/1.52  --inst_learning_factor                  2
% 7.75/1.52  --inst_start_prop_sim_after_learn       3
% 7.75/1.52  --inst_sel_renew                        solver
% 7.75/1.52  --inst_lit_activity_flag                true
% 7.75/1.52  --inst_restr_to_given                   false
% 7.75/1.52  --inst_activity_threshold               500
% 7.75/1.52  --inst_out_proof                        true
% 7.75/1.52  
% 7.75/1.52  ------ Resolution Options
% 7.75/1.52  
% 7.75/1.52  --resolution_flag                       false
% 7.75/1.52  --res_lit_sel                           adaptive
% 7.75/1.52  --res_lit_sel_side                      none
% 7.75/1.52  --res_ordering                          kbo
% 7.75/1.52  --res_to_prop_solver                    active
% 7.75/1.52  --res_prop_simpl_new                    false
% 7.75/1.52  --res_prop_simpl_given                  true
% 7.75/1.52  --res_passive_queue_type                priority_queues
% 7.75/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.75/1.52  --res_passive_queues_freq               [15;5]
% 7.75/1.52  --res_forward_subs                      full
% 7.75/1.52  --res_backward_subs                     full
% 7.75/1.52  --res_forward_subs_resolution           true
% 7.75/1.52  --res_backward_subs_resolution          true
% 7.75/1.52  --res_orphan_elimination                true
% 7.75/1.52  --res_time_limit                        2.
% 7.75/1.52  --res_out_proof                         true
% 7.75/1.52  
% 7.75/1.52  ------ Superposition Options
% 7.75/1.52  
% 7.75/1.52  --superposition_flag                    true
% 7.75/1.52  --sup_passive_queue_type                priority_queues
% 7.75/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.75/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.75/1.52  --demod_completeness_check              fast
% 7.75/1.52  --demod_use_ground                      true
% 7.75/1.52  --sup_to_prop_solver                    passive
% 7.75/1.52  --sup_prop_simpl_new                    true
% 7.75/1.52  --sup_prop_simpl_given                  true
% 7.75/1.52  --sup_fun_splitting                     true
% 7.75/1.52  --sup_smt_interval                      50000
% 7.75/1.52  
% 7.75/1.52  ------ Superposition Simplification Setup
% 7.75/1.52  
% 7.75/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.75/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.75/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.75/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.75/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.75/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.75/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.75/1.52  --sup_immed_triv                        [TrivRules]
% 7.75/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.52  --sup_immed_bw_main                     []
% 7.75/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.75/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.75/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.52  --sup_input_bw                          []
% 7.75/1.52  
% 7.75/1.52  ------ Combination Options
% 7.75/1.52  
% 7.75/1.52  --comb_res_mult                         3
% 7.75/1.52  --comb_sup_mult                         2
% 7.75/1.52  --comb_inst_mult                        10
% 7.75/1.52  
% 7.75/1.52  ------ Debug Options
% 7.75/1.52  
% 7.75/1.52  --dbg_backtrace                         false
% 7.75/1.52  --dbg_dump_prop_clauses                 false
% 7.75/1.52  --dbg_dump_prop_clauses_file            -
% 7.75/1.52  --dbg_out_stat                          false
% 7.75/1.52  
% 7.75/1.52  
% 7.75/1.52  
% 7.75/1.52  
% 7.75/1.52  ------ Proving...
% 7.75/1.52  
% 7.75/1.52  
% 7.75/1.52  % SZS status Theorem for theBenchmark.p
% 7.75/1.52  
% 7.75/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.75/1.52  
% 7.75/1.52  fof(f16,conjecture,(
% 7.75/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.75/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.52  
% 7.75/1.52  fof(f17,negated_conjecture,(
% 7.75/1.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.75/1.52    inference(negated_conjecture,[],[f16])).
% 7.75/1.52  
% 7.75/1.52  fof(f38,plain,(
% 7.75/1.52    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.75/1.52    inference(ennf_transformation,[],[f17])).
% 7.75/1.52  
% 7.75/1.52  fof(f39,plain,(
% 7.75/1.52    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.75/1.52    inference(flattening,[],[f38])).
% 7.75/1.52  
% 7.75/1.52  fof(f45,plain,(
% 7.75/1.52    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 7.75/1.52    introduced(choice_axiom,[])).
% 7.75/1.52  
% 7.75/1.52  fof(f46,plain,(
% 7.75/1.52    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 7.75/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f45])).
% 7.75/1.52  
% 7.75/1.52  fof(f74,plain,(
% 7.75/1.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.75/1.52    inference(cnf_transformation,[],[f46])).
% 7.75/1.52  
% 7.75/1.52  fof(f15,axiom,(
% 7.75/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.75/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.52  
% 7.75/1.52  fof(f36,plain,(
% 7.75/1.52    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.75/1.52    inference(ennf_transformation,[],[f15])).
% 7.75/1.52  
% 7.75/1.52  fof(f37,plain,(
% 7.75/1.52    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.75/1.52    inference(flattening,[],[f36])).
% 7.75/1.52  
% 7.75/1.52  fof(f71,plain,(
% 7.75/1.52    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.75/1.52    inference(cnf_transformation,[],[f37])).
% 7.75/1.52  
% 7.75/1.52  fof(f72,plain,(
% 7.75/1.52    v1_funct_1(sK3)),
% 7.75/1.52    inference(cnf_transformation,[],[f46])).
% 7.75/1.52  
% 7.75/1.52  fof(f14,axiom,(
% 7.75/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 7.75/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.52  
% 7.75/1.52  fof(f34,plain,(
% 7.75/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.75/1.52    inference(ennf_transformation,[],[f14])).
% 7.75/1.52  
% 7.75/1.52  fof(f35,plain,(
% 7.75/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.75/1.52    inference(flattening,[],[f34])).
% 7.75/1.52  
% 7.75/1.52  fof(f69,plain,(
% 7.75/1.52    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.75/1.52    inference(cnf_transformation,[],[f35])).
% 7.75/1.52  
% 7.75/1.52  fof(f7,axiom,(
% 7.75/1.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 7.75/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.52  
% 7.75/1.52  fof(f23,plain,(
% 7.75/1.52    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 7.75/1.52    inference(ennf_transformation,[],[f7])).
% 7.75/1.52  
% 7.75/1.52  fof(f57,plain,(
% 7.75/1.52    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 7.75/1.52    inference(cnf_transformation,[],[f23])).
% 7.75/1.52  
% 7.75/1.52  fof(f1,axiom,(
% 7.75/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.75/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.52  
% 7.75/1.52  fof(f40,plain,(
% 7.75/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.75/1.52    inference(nnf_transformation,[],[f1])).
% 7.75/1.52  
% 7.75/1.52  fof(f41,plain,(
% 7.75/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.75/1.52    inference(flattening,[],[f40])).
% 7.75/1.52  
% 7.75/1.52  fof(f47,plain,(
% 7.75/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.75/1.52    inference(cnf_transformation,[],[f41])).
% 7.75/1.52  
% 7.75/1.52  fof(f79,plain,(
% 7.75/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.75/1.52    inference(equality_resolution,[],[f47])).
% 7.75/1.52  
% 7.75/1.52  fof(f75,plain,(
% 7.75/1.52    r1_tarski(sK2,sK0)),
% 7.75/1.52    inference(cnf_transformation,[],[f46])).
% 7.75/1.52  
% 7.75/1.52  fof(f13,axiom,(
% 7.75/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.75/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.52  
% 7.75/1.52  fof(f32,plain,(
% 7.75/1.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.52    inference(ennf_transformation,[],[f13])).
% 7.75/1.52  
% 7.75/1.52  fof(f33,plain,(
% 7.75/1.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.52    inference(flattening,[],[f32])).
% 7.75/1.52  
% 7.75/1.52  fof(f44,plain,(
% 7.75/1.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.52    inference(nnf_transformation,[],[f33])).
% 7.75/1.52  
% 7.75/1.52  fof(f63,plain,(
% 7.75/1.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.52    inference(cnf_transformation,[],[f44])).
% 7.75/1.52  
% 7.75/1.52  fof(f73,plain,(
% 7.75/1.52    v1_funct_2(sK3,sK0,sK1)),
% 7.75/1.52    inference(cnf_transformation,[],[f46])).
% 7.75/1.52  
% 7.75/1.52  fof(f10,axiom,(
% 7.75/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.75/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.52  
% 7.75/1.52  fof(f27,plain,(
% 7.75/1.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.52    inference(ennf_transformation,[],[f10])).
% 7.75/1.52  
% 7.75/1.52  fof(f60,plain,(
% 7.75/1.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.52    inference(cnf_transformation,[],[f27])).
% 7.75/1.52  
% 7.75/1.52  fof(f8,axiom,(
% 7.75/1.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.75/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.52  
% 7.75/1.52  fof(f24,plain,(
% 7.75/1.52    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.75/1.52    inference(ennf_transformation,[],[f8])).
% 7.75/1.52  
% 7.75/1.52  fof(f25,plain,(
% 7.75/1.52    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.75/1.52    inference(flattening,[],[f24])).
% 7.75/1.52  
% 7.75/1.52  fof(f58,plain,(
% 7.75/1.52    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.75/1.52    inference(cnf_transformation,[],[f25])).
% 7.75/1.52  
% 7.75/1.52  fof(f5,axiom,(
% 7.75/1.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.75/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.52  
% 7.75/1.52  fof(f55,plain,(
% 7.75/1.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.75/1.52    inference(cnf_transformation,[],[f5])).
% 7.75/1.52  
% 7.75/1.52  fof(f4,axiom,(
% 7.75/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.75/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.52  
% 7.75/1.52  fof(f20,plain,(
% 7.75/1.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.75/1.52    inference(ennf_transformation,[],[f4])).
% 7.75/1.52  
% 7.75/1.52  fof(f54,plain,(
% 7.75/1.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.75/1.52    inference(cnf_transformation,[],[f20])).
% 7.75/1.52  
% 7.75/1.52  fof(f12,axiom,(
% 7.75/1.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 7.75/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.52  
% 7.75/1.52  fof(f30,plain,(
% 7.75/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 7.75/1.52    inference(ennf_transformation,[],[f12])).
% 7.75/1.52  
% 7.75/1.52  fof(f31,plain,(
% 7.75/1.52    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 7.75/1.52    inference(flattening,[],[f30])).
% 7.75/1.52  
% 7.75/1.52  fof(f62,plain,(
% 7.75/1.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 7.75/1.52    inference(cnf_transformation,[],[f31])).
% 7.75/1.52  
% 7.75/1.52  fof(f11,axiom,(
% 7.75/1.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 7.75/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.52  
% 7.75/1.52  fof(f28,plain,(
% 7.75/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 7.75/1.52    inference(ennf_transformation,[],[f11])).
% 7.75/1.52  
% 7.75/1.52  fof(f29,plain,(
% 7.75/1.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 7.75/1.52    inference(flattening,[],[f28])).
% 7.75/1.52  
% 7.75/1.52  fof(f61,plain,(
% 7.75/1.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 7.75/1.52    inference(cnf_transformation,[],[f29])).
% 7.75/1.52  
% 7.75/1.52  fof(f65,plain,(
% 7.75/1.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.52    inference(cnf_transformation,[],[f44])).
% 7.75/1.52  
% 7.75/1.52  fof(f77,plain,(
% 7.75/1.52    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 7.75/1.52    inference(cnf_transformation,[],[f46])).
% 7.75/1.52  
% 7.75/1.52  fof(f68,plain,(
% 7.75/1.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.52    inference(cnf_transformation,[],[f44])).
% 7.75/1.52  
% 7.75/1.52  fof(f82,plain,(
% 7.75/1.52    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.52    inference(equality_resolution,[],[f68])).
% 7.75/1.52  
% 7.75/1.52  fof(f83,plain,(
% 7.75/1.52    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.75/1.52    inference(equality_resolution,[],[f82])).
% 7.75/1.52  
% 7.75/1.52  fof(f3,axiom,(
% 7.75/1.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.75/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.52  
% 7.75/1.52  fof(f42,plain,(
% 7.75/1.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.75/1.52    inference(nnf_transformation,[],[f3])).
% 7.75/1.52  
% 7.75/1.52  fof(f43,plain,(
% 7.75/1.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.75/1.52    inference(flattening,[],[f42])).
% 7.75/1.52  
% 7.75/1.52  fof(f53,plain,(
% 7.75/1.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.75/1.52    inference(cnf_transformation,[],[f43])).
% 7.75/1.52  
% 7.75/1.52  fof(f80,plain,(
% 7.75/1.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.75/1.52    inference(equality_resolution,[],[f53])).
% 7.75/1.52  
% 7.75/1.52  fof(f76,plain,(
% 7.75/1.52    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 7.75/1.52    inference(cnf_transformation,[],[f46])).
% 7.75/1.52  
% 7.75/1.52  fof(f51,plain,(
% 7.75/1.52    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.75/1.52    inference(cnf_transformation,[],[f43])).
% 7.75/1.52  
% 7.75/1.52  fof(f52,plain,(
% 7.75/1.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.75/1.52    inference(cnf_transformation,[],[f43])).
% 7.75/1.52  
% 7.75/1.52  fof(f81,plain,(
% 7.75/1.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.75/1.52    inference(equality_resolution,[],[f52])).
% 7.75/1.52  
% 7.75/1.52  fof(f2,axiom,(
% 7.75/1.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 7.75/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.52  
% 7.75/1.52  fof(f19,plain,(
% 7.75/1.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 7.75/1.52    inference(ennf_transformation,[],[f2])).
% 7.75/1.52  
% 7.75/1.52  fof(f50,plain,(
% 7.75/1.52    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 7.75/1.52    inference(cnf_transformation,[],[f19])).
% 7.75/1.52  
% 7.75/1.52  fof(f64,plain,(
% 7.75/1.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.52    inference(cnf_transformation,[],[f44])).
% 7.75/1.52  
% 7.75/1.52  fof(f86,plain,(
% 7.75/1.52    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.75/1.52    inference(equality_resolution,[],[f64])).
% 7.75/1.52  
% 7.75/1.52  fof(f70,plain,(
% 7.75/1.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.75/1.52    inference(cnf_transformation,[],[f35])).
% 7.75/1.52  
% 7.75/1.52  fof(f9,axiom,(
% 7.75/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.75/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.52  
% 7.75/1.52  fof(f18,plain,(
% 7.75/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.75/1.52    inference(pure_predicate_removal,[],[f9])).
% 7.75/1.52  
% 7.75/1.52  fof(f26,plain,(
% 7.75/1.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.52    inference(ennf_transformation,[],[f18])).
% 7.75/1.52  
% 7.75/1.52  fof(f59,plain,(
% 7.75/1.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.52    inference(cnf_transformation,[],[f26])).
% 7.75/1.52  
% 7.75/1.52  fof(f6,axiom,(
% 7.75/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.75/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.52  
% 7.75/1.52  fof(f21,plain,(
% 7.75/1.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.75/1.52    inference(ennf_transformation,[],[f6])).
% 7.75/1.52  
% 7.75/1.52  fof(f22,plain,(
% 7.75/1.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.75/1.52    inference(flattening,[],[f21])).
% 7.75/1.52  
% 7.75/1.52  fof(f56,plain,(
% 7.75/1.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.75/1.52    inference(cnf_transformation,[],[f22])).
% 7.75/1.52  
% 7.75/1.52  cnf(c_28,negated_conjecture,
% 7.75/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.75/1.52      inference(cnf_transformation,[],[f74]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1027,plain,
% 7.75/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_24,plain,
% 7.75/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.52      | ~ v1_funct_1(X0)
% 7.75/1.52      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.75/1.52      inference(cnf_transformation,[],[f71]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1029,plain,
% 7.75/1.52      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.75/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.75/1.52      | v1_funct_1(X2) != iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_3165,plain,
% 7.75/1.52      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 7.75/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_1027,c_1029]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_30,negated_conjecture,
% 7.75/1.52      ( v1_funct_1(sK3) ),
% 7.75/1.52      inference(cnf_transformation,[],[f72]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_31,plain,
% 7.75/1.52      ( v1_funct_1(sK3) = iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_3316,plain,
% 7.75/1.52      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.75/1.52      inference(global_propositional_subsumption,
% 7.75/1.52                [status(thm)],
% 7.75/1.52                [c_3165,c_31]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_23,plain,
% 7.75/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.52      | ~ v1_funct_1(X0)
% 7.75/1.52      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 7.75/1.52      inference(cnf_transformation,[],[f69]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1030,plain,
% 7.75/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.75/1.52      | v1_funct_1(X0) != iProver_top
% 7.75/1.52      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1697,plain,
% 7.75/1.52      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 7.75/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_1027,c_1030]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1855,plain,
% 7.75/1.52      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 7.75/1.52      inference(global_propositional_subsumption,
% 7.75/1.52                [status(thm)],
% 7.75/1.52                [c_1697,c_31]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_3323,plain,
% 7.75/1.52      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_3316,c_1855]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_10,plain,
% 7.75/1.52      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 7.75/1.52      inference(cnf_transformation,[],[f57]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1036,plain,
% 7.75/1.52      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 7.75/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_2,plain,
% 7.75/1.52      ( r1_tarski(X0,X0) ),
% 7.75/1.52      inference(cnf_transformation,[],[f79]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1040,plain,
% 7.75/1.52      ( r1_tarski(X0,X0) = iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_27,negated_conjecture,
% 7.75/1.52      ( r1_tarski(sK2,sK0) ),
% 7.75/1.52      inference(cnf_transformation,[],[f75]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1028,plain,
% 7.75/1.52      ( r1_tarski(sK2,sK0) = iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_21,plain,
% 7.75/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.75/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.52      | k1_relset_1(X1,X2,X0) = X1
% 7.75/1.52      | k1_xboole_0 = X2 ),
% 7.75/1.52      inference(cnf_transformation,[],[f63]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_29,negated_conjecture,
% 7.75/1.52      ( v1_funct_2(sK3,sK0,sK1) ),
% 7.75/1.52      inference(cnf_transformation,[],[f73]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_416,plain,
% 7.75/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.52      | k1_relset_1(X1,X2,X0) = X1
% 7.75/1.52      | sK3 != X0
% 7.75/1.52      | sK1 != X2
% 7.75/1.52      | sK0 != X1
% 7.75/1.52      | k1_xboole_0 = X2 ),
% 7.75/1.52      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_417,plain,
% 7.75/1.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.75/1.52      | k1_relset_1(sK0,sK1,sK3) = sK0
% 7.75/1.52      | k1_xboole_0 = sK1 ),
% 7.75/1.52      inference(unflattening,[status(thm)],[c_416]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_419,plain,
% 7.75/1.52      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 7.75/1.52      inference(global_propositional_subsumption,
% 7.75/1.52                [status(thm)],
% 7.75/1.52                [c_417,c_28]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13,plain,
% 7.75/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.52      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.75/1.52      inference(cnf_transformation,[],[f60]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1034,plain,
% 7.75/1.52      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.75/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1784,plain,
% 7.75/1.52      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_1027,c_1034]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1852,plain,
% 7.75/1.52      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_419,c_1784]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_11,plain,
% 7.75/1.52      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.75/1.52      | ~ v1_relat_1(X1)
% 7.75/1.52      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 7.75/1.52      inference(cnf_transformation,[],[f58]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1035,plain,
% 7.75/1.52      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 7.75/1.52      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.75/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_2298,plain,
% 7.75/1.52      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.75/1.52      | sK1 = k1_xboole_0
% 7.75/1.52      | r1_tarski(X0,sK0) != iProver_top
% 7.75/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_1852,c_1035]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_8,plain,
% 7.75/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.75/1.52      inference(cnf_transformation,[],[f55]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1037,plain,
% 7.75/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_7,plain,
% 7.75/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.75/1.52      | ~ v1_relat_1(X1)
% 7.75/1.52      | v1_relat_1(X0) ),
% 7.75/1.52      inference(cnf_transformation,[],[f54]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1038,plain,
% 7.75/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.75/1.52      | v1_relat_1(X1) != iProver_top
% 7.75/1.52      | v1_relat_1(X0) = iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_2105,plain,
% 7.75/1.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.75/1.52      | v1_relat_1(sK3) = iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_1027,c_1038]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_2382,plain,
% 7.75/1.52      ( v1_relat_1(sK3) = iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_1037,c_2105]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_2442,plain,
% 7.75/1.52      ( r1_tarski(X0,sK0) != iProver_top
% 7.75/1.52      | sK1 = k1_xboole_0
% 7.75/1.52      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 7.75/1.52      inference(global_propositional_subsumption,
% 7.75/1.52                [status(thm)],
% 7.75/1.52                [c_2298,c_2382]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_2443,plain,
% 7.75/1.52      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.75/1.52      | sK1 = k1_xboole_0
% 7.75/1.52      | r1_tarski(X0,sK0) != iProver_top ),
% 7.75/1.52      inference(renaming,[status(thm)],[c_2442]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_2450,plain,
% 7.75/1.52      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_1028,c_2443]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_15,plain,
% 7.75/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.52      | ~ r1_tarski(X3,X0) ),
% 7.75/1.52      inference(cnf_transformation,[],[f62]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1032,plain,
% 7.75/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.75/1.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.75/1.52      | r1_tarski(X3,X0) != iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_2689,plain,
% 7.75/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 7.75/1.52      | r1_tarski(X0,sK3) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_1027,c_1032]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_14,plain,
% 7.75/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 7.75/1.52      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 7.75/1.52      inference(cnf_transformation,[],[f61]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1033,plain,
% 7.75/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.75/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 7.75/1.52      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_3097,plain,
% 7.75/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 7.75/1.52      | r1_tarski(X0,sK3) != iProver_top
% 7.75/1.52      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_2689,c_1033]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_4041,plain,
% 7.75/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 7.75/1.52      | r1_tarski(X0,X2) != iProver_top
% 7.75/1.52      | r1_tarski(X2,sK3) != iProver_top
% 7.75/1.52      | r1_tarski(k1_relat_1(X2),X1) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_3097,c_1032]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_8802,plain,
% 7.75/1.52      ( sK1 = k1_xboole_0
% 7.75/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 7.75/1.52      | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
% 7.75/1.52      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 7.75/1.52      | r1_tarski(sK2,X1) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_2450,c_4041]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_4039,plain,
% 7.75/1.52      ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
% 7.75/1.52      | r1_tarski(X1,sK3) != iProver_top
% 7.75/1.52      | r1_tarski(k1_relat_1(X1),X0) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_3097,c_1034]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_6779,plain,
% 7.75/1.52      ( k1_relset_1(k1_relat_1(X0),sK1,X0) = k1_relat_1(X0)
% 7.75/1.52      | r1_tarski(X0,sK3) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_1040,c_4039]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_6856,plain,
% 7.75/1.52      ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0))
% 7.75/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_1036,c_6779]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_11271,plain,
% 7.75/1.52      ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 7.75/1.52      inference(global_propositional_subsumption,
% 7.75/1.52                [status(thm)],
% 7.75/1.52                [c_6856,c_2382]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_11274,plain,
% 7.75/1.52      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 7.75/1.52      | sK1 = k1_xboole_0 ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_2450,c_11271]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_19,plain,
% 7.75/1.52      ( v1_funct_2(X0,X1,X2)
% 7.75/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.52      | k1_relset_1(X1,X2,X0) != X1
% 7.75/1.52      | k1_xboole_0 = X2 ),
% 7.75/1.52      inference(cnf_transformation,[],[f65]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_25,negated_conjecture,
% 7.75/1.52      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 7.75/1.52      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.75/1.52      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 7.75/1.52      inference(cnf_transformation,[],[f77]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_400,plain,
% 7.75/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.52      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.75/1.52      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.75/1.52      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 7.75/1.52      | k1_relset_1(X1,X2,X0) != X1
% 7.75/1.52      | sK2 != X1
% 7.75/1.52      | sK1 != X2
% 7.75/1.52      | k1_xboole_0 = X2 ),
% 7.75/1.52      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_401,plain,
% 7.75/1.52      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.75/1.52      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.75/1.52      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 7.75/1.52      | k1_xboole_0 = sK1 ),
% 7.75/1.52      inference(unflattening,[status(thm)],[c_400]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1020,plain,
% 7.75/1.52      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 7.75/1.52      | k1_xboole_0 = sK1
% 7.75/1.52      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.75/1.52      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_3322,plain,
% 7.75/1.52      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 7.75/1.52      | sK1 = k1_xboole_0
% 7.75/1.52      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.75/1.52      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_3316,c_1020]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_11447,plain,
% 7.75/1.52      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 7.75/1.52      | sK1 = k1_xboole_0
% 7.75/1.52      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.75/1.52      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_11274,c_3322]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_12067,plain,
% 7.75/1.52      ( sK1 = k1_xboole_0
% 7.75/1.52      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.75/1.52      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.75/1.52      inference(global_propositional_subsumption,
% 7.75/1.52                [status(thm)],
% 7.75/1.52                [c_11447,c_2450]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_12074,plain,
% 7.75/1.52      ( sK1 = k1_xboole_0
% 7.75/1.52      | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
% 7.75/1.52      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 7.75/1.52      | r1_tarski(sK2,sK2) != iProver_top
% 7.75/1.52      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_8802,c_12067]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1264,plain,
% 7.75/1.52      ( r1_tarski(sK2,sK2) ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_2]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1265,plain,
% 7.75/1.52      ( r1_tarski(sK2,sK2) = iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_1264]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13260,plain,
% 7.75/1.52      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 7.75/1.52      | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
% 7.75/1.52      | sK1 = k1_xboole_0
% 7.75/1.52      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.75/1.52      inference(global_propositional_subsumption,
% 7.75/1.52                [status(thm)],
% 7.75/1.52                [c_12074,c_1265]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13261,plain,
% 7.75/1.52      ( sK1 = k1_xboole_0
% 7.75/1.52      | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
% 7.75/1.52      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 7.75/1.52      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.75/1.52      inference(renaming,[status(thm)],[c_13260]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13264,plain,
% 7.75/1.52      ( sK1 = k1_xboole_0
% 7.75/1.52      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 7.75/1.52      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_1040,c_13261]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13405,plain,
% 7.75/1.52      ( sK1 = k1_xboole_0
% 7.75/1.52      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 7.75/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_1036,c_13264]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13442,plain,
% 7.75/1.52      ( v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 7.75/1.52      | sK1 = k1_xboole_0 ),
% 7.75/1.52      inference(global_propositional_subsumption,
% 7.75/1.52                [status(thm)],
% 7.75/1.52                [c_13405,c_2382]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13443,plain,
% 7.75/1.52      ( sK1 = k1_xboole_0
% 7.75/1.52      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.75/1.52      inference(renaming,[status(thm)],[c_13442]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13446,plain,
% 7.75/1.52      ( sK1 = k1_xboole_0 ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_3323,c_13443]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_16,plain,
% 7.75/1.52      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 7.75/1.52      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.75/1.52      | k1_xboole_0 = X0 ),
% 7.75/1.52      inference(cnf_transformation,[],[f83]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_322,plain,
% 7.75/1.52      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.75/1.52      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.75/1.52      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.75/1.52      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.75/1.52      | sK2 != X0
% 7.75/1.52      | sK1 != k1_xboole_0
% 7.75/1.52      | k1_xboole_0 = X0 ),
% 7.75/1.52      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_323,plain,
% 7.75/1.52      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.75/1.52      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 7.75/1.52      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.75/1.52      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.75/1.52      | sK1 != k1_xboole_0
% 7.75/1.52      | k1_xboole_0 = sK2 ),
% 7.75/1.52      inference(unflattening,[status(thm)],[c_322]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1024,plain,
% 7.75/1.52      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.75/1.52      | sK1 != k1_xboole_0
% 7.75/1.52      | k1_xboole_0 = sK2
% 7.75/1.52      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.75/1.52      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 7.75/1.52      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_4,plain,
% 7.75/1.52      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.75/1.52      inference(cnf_transformation,[],[f80]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1044,plain,
% 7.75/1.52      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.75/1.52      | sK2 = k1_xboole_0
% 7.75/1.52      | sK1 != k1_xboole_0
% 7.75/1.52      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.75/1.52      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.75/1.52      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_1024,c_4]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_33,plain,
% 7.75/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1251,plain,
% 7.75/1.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.75/1.52      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.75/1.52      | ~ v1_funct_1(sK3) ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_23]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1252,plain,
% 7.75/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.75/1.52      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 7.75/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_1251]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1449,plain,
% 7.75/1.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.75/1.52      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.75/1.52      | sK1 != k1_xboole_0
% 7.75/1.52      | sK2 = k1_xboole_0
% 7.75/1.52      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
% 7.75/1.52      inference(global_propositional_subsumption,
% 7.75/1.52                [status(thm)],
% 7.75/1.52                [c_1044,c_31,c_33,c_1252]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1450,plain,
% 7.75/1.52      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.75/1.52      | sK2 = k1_xboole_0
% 7.75/1.52      | sK1 != k1_xboole_0
% 7.75/1.52      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.75/1.52      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.75/1.52      inference(renaming,[status(thm)],[c_1449]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_3320,plain,
% 7.75/1.52      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 7.75/1.52      | sK2 = k1_xboole_0
% 7.75/1.52      | sK1 != k1_xboole_0
% 7.75/1.52      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.75/1.52      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_3316,c_1450]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_26,negated_conjecture,
% 7.75/1.52      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 7.75/1.52      inference(cnf_transformation,[],[f76]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_6,plain,
% 7.75/1.52      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.75/1.52      | k1_xboole_0 = X0
% 7.75/1.52      | k1_xboole_0 = X1 ),
% 7.75/1.52      inference(cnf_transformation,[],[f51]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_84,plain,
% 7.75/1.52      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.75/1.52      | k1_xboole_0 = k1_xboole_0 ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_6]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_5,plain,
% 7.75/1.52      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.75/1.52      inference(cnf_transformation,[],[f81]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_85,plain,
% 7.75/1.52      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_5]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_636,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1085,plain,
% 7.75/1.52      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_636]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1123,plain,
% 7.75/1.52      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_1085]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_3,plain,
% 7.75/1.52      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 7.75/1.52      inference(cnf_transformation,[],[f50]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1176,plain,
% 7.75/1.52      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1249,plain,
% 7.75/1.52      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_636]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1250,plain,
% 7.75/1.52      ( sK1 != k1_xboole_0
% 7.75/1.52      | k1_xboole_0 = sK1
% 7.75/1.52      | k1_xboole_0 != k1_xboole_0 ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_1249]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_635,plain,( X0 = X0 ),theory(equality) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1260,plain,
% 7.75/1.52      ( sK2 = sK2 ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_635]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_637,plain,
% 7.75/1.52      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.75/1.52      theory(equality) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1101,plain,
% 7.75/1.52      ( ~ r1_tarski(X0,X1)
% 7.75/1.52      | r1_tarski(sK2,k1_xboole_0)
% 7.75/1.52      | sK2 != X0
% 7.75/1.52      | k1_xboole_0 != X1 ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_637]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1160,plain,
% 7.75/1.52      ( ~ r1_tarski(sK2,X0)
% 7.75/1.52      | r1_tarski(sK2,k1_xboole_0)
% 7.75/1.52      | sK2 != sK2
% 7.75/1.52      | k1_xboole_0 != X0 ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_1101]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1458,plain,
% 7.75/1.52      ( ~ r1_tarski(sK2,sK0)
% 7.75/1.52      | r1_tarski(sK2,k1_xboole_0)
% 7.75/1.52      | sK2 != sK2
% 7.75/1.52      | k1_xboole_0 != sK0 ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_1160]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_6050,plain,
% 7.75/1.52      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 7.75/1.52      inference(global_propositional_subsumption,
% 7.75/1.52                [status(thm)],
% 7.75/1.52                [c_3320,c_27,c_26,c_84,c_85,c_1123,c_1176,c_1250,c_1260,
% 7.75/1.52                 c_1458]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13747,plain,
% 7.75/1.52      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_13446,c_6050]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13820,plain,
% 7.75/1.52      ( sK2 = k1_xboole_0 ),
% 7.75/1.52      inference(equality_resolution_simp,[status(thm)],[c_13747]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_427,plain,
% 7.75/1.52      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.75/1.52      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.75/1.52      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 7.75/1.52      | sK2 != sK0
% 7.75/1.52      | sK1 != sK1 ),
% 7.75/1.52      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_503,plain,
% 7.75/1.52      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.75/1.52      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.75/1.52      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 7.75/1.52      | sK2 != sK0 ),
% 7.75/1.52      inference(equality_resolution_simp,[status(thm)],[c_427]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1019,plain,
% 7.75/1.52      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 7.75/1.52      | sK2 != sK0
% 7.75/1.52      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.75/1.52      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_3321,plain,
% 7.75/1.52      ( k7_relat_1(sK3,sK2) != sK3
% 7.75/1.52      | sK2 != sK0
% 7.75/1.52      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.75/1.52      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_3316,c_1019]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13749,plain,
% 7.75/1.52      ( k7_relat_1(sK3,sK2) != sK3
% 7.75/1.52      | sK2 != sK0
% 7.75/1.52      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 7.75/1.52      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_13446,c_3321]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13781,plain,
% 7.75/1.52      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_13446,c_26]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13782,plain,
% 7.75/1.52      ( sK0 = k1_xboole_0 ),
% 7.75/1.52      inference(equality_resolution_simp,[status(thm)],[c_13781]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13817,plain,
% 7.75/1.52      ( k7_relat_1(sK3,sK2) != sK3
% 7.75/1.52      | sK2 != k1_xboole_0
% 7.75/1.52      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 7.75/1.52      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_13749,c_13782]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13818,plain,
% 7.75/1.52      ( k7_relat_1(sK3,sK2) != sK3
% 7.75/1.52      | sK2 != k1_xboole_0
% 7.75/1.52      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.75/1.52      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_13817,c_4]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13821,plain,
% 7.75/1.52      ( k7_relat_1(sK3,k1_xboole_0) != sK3
% 7.75/1.52      | k1_xboole_0 != k1_xboole_0
% 7.75/1.52      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.75/1.52      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_13820,c_13818]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13829,plain,
% 7.75/1.52      ( k7_relat_1(sK3,k1_xboole_0) != sK3
% 7.75/1.52      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.75/1.52      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 7.75/1.52      inference(equality_resolution_simp,[status(thm)],[c_13821]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13776,plain,
% 7.75/1.52      ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_13446,c_1784]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13788,plain,
% 7.75/1.52      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_13776,c_13782]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_20,plain,
% 7.75/1.52      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.75/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.75/1.52      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.75/1.52      inference(cnf_transformation,[],[f86]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_387,plain,
% 7.75/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.75/1.52      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 7.75/1.52      | sK3 != X0
% 7.75/1.52      | sK1 != X1
% 7.75/1.52      | sK0 != k1_xboole_0 ),
% 7.75/1.52      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_388,plain,
% 7.75/1.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 7.75/1.52      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 7.75/1.52      | sK0 != k1_xboole_0 ),
% 7.75/1.52      inference(unflattening,[status(thm)],[c_387]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1021,plain,
% 7.75/1.52      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 7.75/1.52      | sK0 != k1_xboole_0
% 7.75/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1042,plain,
% 7.75/1.52      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 7.75/1.52      | sK0 != k1_xboole_0
% 7.75/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_1021,c_5]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13778,plain,
% 7.75/1.52      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.75/1.52      | sK0 != k1_xboole_0
% 7.75/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_13446,c_1042]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13785,plain,
% 7.75/1.52      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.75/1.52      | k1_xboole_0 != k1_xboole_0
% 7.75/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_13778,c_13782]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13786,plain,
% 7.75/1.52      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.75/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.75/1.52      inference(equality_resolution_simp,[status(thm)],[c_13785]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13789,plain,
% 7.75/1.52      ( k1_relat_1(sK3) = k1_xboole_0
% 7.75/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_13788,c_13786]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13780,plain,
% 7.75/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_13446,c_1027]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13783,plain,
% 7.75/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_13780,c_13782]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13784,plain,
% 7.75/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_13783,c_5]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_4038,plain,
% 7.75/1.52      ( k2_partfun1(X0,sK1,X1,X2) = k7_relat_1(X1,X2)
% 7.75/1.52      | r1_tarski(X1,sK3) != iProver_top
% 7.75/1.52      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 7.75/1.52      | v1_funct_1(X1) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_3097,c_1029]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_8299,plain,
% 7.75/1.52      ( k2_partfun1(k1_relat_1(X0),sK1,X0,X1) = k7_relat_1(X0,X1)
% 7.75/1.52      | r1_tarski(X0,sK3) != iProver_top
% 7.75/1.52      | v1_funct_1(X0) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_1040,c_4038]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13448,plain,
% 7.75/1.52      ( k2_partfun1(k1_relat_1(X0),k1_xboole_0,X0,X1) = k7_relat_1(X0,X1)
% 7.75/1.52      | r1_tarski(X0,sK3) != iProver_top
% 7.75/1.52      | v1_funct_1(X0) != iProver_top ),
% 7.75/1.52      inference(light_normalisation,[status(thm)],[c_8299,c_13446]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13452,plain,
% 7.75/1.52      ( k2_partfun1(k1_relat_1(sK3),k1_xboole_0,sK3,X0) = k7_relat_1(sK3,X0)
% 7.75/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_1040,c_13448]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13652,plain,
% 7.75/1.52      ( k2_partfun1(k1_relat_1(sK3),k1_xboole_0,sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.75/1.52      inference(global_propositional_subsumption,
% 7.75/1.52                [status(thm)],
% 7.75/1.52                [c_13452,c_31]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_22,plain,
% 7.75/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.52      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.52      | ~ v1_funct_1(X0) ),
% 7.75/1.52      inference(cnf_transformation,[],[f70]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1031,plain,
% 7.75/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.75/1.52      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.75/1.52      | v1_funct_1(X0) != iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_2176,plain,
% 7.75/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top
% 7.75/1.52      | m1_subset_1(k2_partfun1(X1,k1_xboole_0,X0,X2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.75/1.52      | v1_funct_1(X0) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_4,c_1031]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_2183,plain,
% 7.75/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.75/1.52      | m1_subset_1(k2_partfun1(X1,k1_xboole_0,X0,X2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.75/1.52      | v1_funct_1(X0) != iProver_top ),
% 7.75/1.52      inference(demodulation,[status(thm)],[c_2176,c_4]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13659,plain,
% 7.75/1.52      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.75/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.75/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_13652,c_2183]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_13667,plain,
% 7.75/1.52      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.75/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.75/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_13659]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_3096,plain,
% 7.75/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 7.75/1.52      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_1027,c_1033]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_12,plain,
% 7.75/1.52      ( v4_relat_1(X0,X1)
% 7.75/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.75/1.52      inference(cnf_transformation,[],[f59]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_9,plain,
% 7.75/1.52      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.75/1.52      inference(cnf_transformation,[],[f56]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_296,plain,
% 7.75/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.52      | ~ v1_relat_1(X0)
% 7.75/1.52      | k7_relat_1(X0,X1) = X0 ),
% 7.75/1.52      inference(resolution,[status(thm)],[c_12,c_9]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1025,plain,
% 7.75/1.52      ( k7_relat_1(X0,X1) = X0
% 7.75/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.75/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.52      inference(predicate_to_equality,[status(thm)],[c_296]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_3344,plain,
% 7.75/1.52      ( k7_relat_1(sK3,X0) = sK3
% 7.75/1.52      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.75/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.75/1.52      inference(superposition,[status(thm)],[c_3096,c_1025]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_3358,plain,
% 7.75/1.52      ( ~ r1_tarski(k1_relat_1(sK3),X0)
% 7.75/1.52      | ~ v1_relat_1(sK3)
% 7.75/1.52      | k7_relat_1(sK3,X0) = sK3 ),
% 7.75/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_3344]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_3360,plain,
% 7.75/1.52      ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 7.75/1.52      | ~ v1_relat_1(sK3)
% 7.75/1.52      | k7_relat_1(sK3,k1_xboole_0) = sK3 ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_3358]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_3329,plain,
% 7.75/1.52      ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_3323]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_2383,plain,
% 7.75/1.52      ( v1_relat_1(sK3) ),
% 7.75/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_2382]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1377,plain,
% 7.75/1.52      ( ~ r1_tarski(X0,X1)
% 7.75/1.52      | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 7.75/1.52      | k1_relat_1(sK3) != X0
% 7.75/1.52      | k1_xboole_0 != X1 ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_637]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_1379,plain,
% 7.75/1.52      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 7.75/1.52      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.75/1.52      | k1_relat_1(sK3) != k1_xboole_0
% 7.75/1.52      | k1_xboole_0 != k1_xboole_0 ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_1377]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(c_90,plain,
% 7.75/1.52      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.75/1.52      inference(instantiation,[status(thm)],[c_2]) ).
% 7.75/1.52  
% 7.75/1.52  cnf(contradiction,plain,
% 7.75/1.52      ( $false ),
% 7.75/1.52      inference(minisat,
% 7.75/1.52                [status(thm)],
% 7.75/1.52                [c_13829,c_13789,c_13784,c_13667,c_3360,c_3329,c_2383,
% 7.75/1.52                 c_1379,c_90,c_85,c_84,c_31]) ).
% 7.75/1.52  
% 7.75/1.52  
% 7.75/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.75/1.52  
% 7.75/1.52  ------                               Statistics
% 7.75/1.52  
% 7.75/1.52  ------ General
% 7.75/1.52  
% 7.75/1.52  abstr_ref_over_cycles:                  0
% 7.75/1.52  abstr_ref_under_cycles:                 0
% 7.75/1.52  gc_basic_clause_elim:                   0
% 7.75/1.52  forced_gc_time:                         0
% 7.75/1.52  parsing_time:                           0.011
% 7.75/1.52  unif_index_cands_time:                  0.
% 7.75/1.52  unif_index_add_time:                    0.
% 7.75/1.52  orderings_time:                         0.
% 7.75/1.52  out_proof_time:                         0.021
% 7.75/1.52  total_time:                             0.596
% 7.75/1.52  num_of_symbols:                         48
% 7.75/1.52  num_of_terms:                           9242
% 7.75/1.52  
% 7.75/1.52  ------ Preprocessing
% 7.75/1.52  
% 7.75/1.52  num_of_splits:                          0
% 7.75/1.52  num_of_split_atoms:                     0
% 7.75/1.52  num_of_reused_defs:                     0
% 7.75/1.52  num_eq_ax_congr_red:                    10
% 7.75/1.52  num_of_sem_filtered_clauses:            1
% 7.75/1.52  num_of_subtypes:                        0
% 7.75/1.52  monotx_restored_types:                  0
% 7.75/1.52  sat_num_of_epr_types:                   0
% 7.75/1.52  sat_num_of_non_cyclic_types:            0
% 7.75/1.52  sat_guarded_non_collapsed_types:        0
% 7.75/1.52  num_pure_diseq_elim:                    0
% 7.75/1.52  simp_replaced_by:                       0
% 7.75/1.52  res_preprocessed:                       137
% 7.75/1.52  prep_upred:                             0
% 7.75/1.52  prep_unflattend:                        33
% 7.75/1.52  smt_new_axioms:                         0
% 7.75/1.52  pred_elim_cands:                        4
% 7.75/1.52  pred_elim:                              2
% 7.75/1.52  pred_elim_cl:                           2
% 7.75/1.52  pred_elim_cycles:                       4
% 7.75/1.52  merged_defs:                            0
% 7.75/1.52  merged_defs_ncl:                        0
% 7.75/1.52  bin_hyper_res:                          0
% 7.75/1.52  prep_cycles:                            4
% 7.75/1.52  pred_elim_time:                         0.006
% 7.75/1.52  splitting_time:                         0.
% 7.75/1.52  sem_filter_time:                        0.
% 7.75/1.52  monotx_time:                            0.
% 7.75/1.52  subtype_inf_time:                       0.
% 7.75/1.52  
% 7.75/1.52  ------ Problem properties
% 7.75/1.52  
% 7.75/1.52  clauses:                                28
% 7.75/1.52  conjectures:                            4
% 7.75/1.52  epr:                                    6
% 7.75/1.52  horn:                                   25
% 7.75/1.52  ground:                                 11
% 7.75/1.52  unary:                                  7
% 7.75/1.52  binary:                                 5
% 7.75/1.52  lits:                                   73
% 7.75/1.52  lits_eq:                                29
% 7.75/1.52  fd_pure:                                0
% 7.75/1.52  fd_pseudo:                              0
% 7.75/1.52  fd_cond:                                2
% 7.75/1.52  fd_pseudo_cond:                         1
% 7.75/1.52  ac_symbols:                             0
% 7.75/1.52  
% 7.75/1.52  ------ Propositional Solver
% 7.75/1.52  
% 7.75/1.52  prop_solver_calls:                      34
% 7.75/1.52  prop_fast_solver_calls:                 1600
% 7.75/1.52  smt_solver_calls:                       0
% 7.75/1.52  smt_fast_solver_calls:                  0
% 7.75/1.52  prop_num_of_clauses:                    6272
% 7.75/1.52  prop_preprocess_simplified:             12998
% 7.75/1.52  prop_fo_subsumed:                       54
% 7.75/1.52  prop_solver_time:                       0.
% 7.75/1.52  smt_solver_time:                        0.
% 7.75/1.52  smt_fast_solver_time:                   0.
% 7.75/1.52  prop_fast_solver_time:                  0.
% 7.75/1.52  prop_unsat_core_time:                   0.001
% 7.75/1.52  
% 7.75/1.52  ------ QBF
% 7.75/1.52  
% 7.75/1.52  qbf_q_res:                              0
% 7.75/1.52  qbf_num_tautologies:                    0
% 7.75/1.52  qbf_prep_cycles:                        0
% 7.75/1.52  
% 7.75/1.52  ------ BMC1
% 7.75/1.52  
% 7.75/1.52  bmc1_current_bound:                     -1
% 7.75/1.52  bmc1_last_solved_bound:                 -1
% 7.75/1.52  bmc1_unsat_core_size:                   -1
% 7.75/1.52  bmc1_unsat_core_parents_size:           -1
% 7.75/1.52  bmc1_merge_next_fun:                    0
% 7.75/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.75/1.52  
% 7.75/1.52  ------ Instantiation
% 7.75/1.52  
% 7.75/1.52  inst_num_of_clauses:                    1984
% 7.75/1.52  inst_num_in_passive:                    788
% 7.75/1.52  inst_num_in_active:                     955
% 7.75/1.52  inst_num_in_unprocessed:                241
% 7.75/1.52  inst_num_of_loops:                      1180
% 7.75/1.52  inst_num_of_learning_restarts:          0
% 7.75/1.52  inst_num_moves_active_passive:          220
% 7.75/1.52  inst_lit_activity:                      0
% 7.75/1.52  inst_lit_activity_moves:                0
% 7.75/1.52  inst_num_tautologies:                   0
% 7.75/1.52  inst_num_prop_implied:                  0
% 7.75/1.52  inst_num_existing_simplified:           0
% 7.75/1.52  inst_num_eq_res_simplified:             0
% 7.75/1.52  inst_num_child_elim:                    0
% 7.75/1.52  inst_num_of_dismatching_blockings:      368
% 7.75/1.52  inst_num_of_non_proper_insts:           2312
% 7.75/1.52  inst_num_of_duplicates:                 0
% 7.75/1.52  inst_inst_num_from_inst_to_res:         0
% 7.75/1.52  inst_dismatching_checking_time:         0.
% 7.75/1.52  
% 7.75/1.52  ------ Resolution
% 7.75/1.52  
% 7.75/1.52  res_num_of_clauses:                     0
% 7.75/1.52  res_num_in_passive:                     0
% 7.75/1.52  res_num_in_active:                      0
% 7.75/1.52  res_num_of_loops:                       141
% 7.75/1.52  res_forward_subset_subsumed:            123
% 7.75/1.52  res_backward_subset_subsumed:           0
% 7.75/1.52  res_forward_subsumed:                   0
% 7.75/1.52  res_backward_subsumed:                  0
% 7.75/1.52  res_forward_subsumption_resolution:     0
% 7.75/1.52  res_backward_subsumption_resolution:    0
% 7.75/1.52  res_clause_to_clause_subsumption:       1708
% 7.75/1.52  res_orphan_elimination:                 0
% 7.75/1.52  res_tautology_del:                      189
% 7.75/1.52  res_num_eq_res_simplified:              1
% 7.75/1.52  res_num_sel_changes:                    0
% 7.75/1.52  res_moves_from_active_to_pass:          0
% 7.75/1.52  
% 7.75/1.52  ------ Superposition
% 7.75/1.52  
% 7.75/1.52  sup_time_total:                         0.
% 7.75/1.52  sup_time_generating:                    0.
% 7.75/1.52  sup_time_sim_full:                      0.
% 7.75/1.52  sup_time_sim_immed:                     0.
% 7.75/1.52  
% 7.75/1.52  sup_num_of_clauses:                     273
% 7.75/1.52  sup_num_in_active:                      82
% 7.75/1.52  sup_num_in_passive:                     191
% 7.75/1.52  sup_num_of_loops:                       235
% 7.75/1.52  sup_fw_superposition:                   363
% 7.75/1.52  sup_bw_superposition:                   261
% 7.75/1.52  sup_immediate_simplified:               251
% 7.75/1.52  sup_given_eliminated:                   0
% 7.75/1.52  comparisons_done:                       0
% 7.75/1.52  comparisons_avoided:                    84
% 7.75/1.52  
% 7.75/1.52  ------ Simplifications
% 7.75/1.52  
% 7.75/1.52  
% 7.75/1.52  sim_fw_subset_subsumed:                 60
% 7.75/1.52  sim_bw_subset_subsumed:                 58
% 7.75/1.52  sim_fw_subsumed:                        70
% 7.75/1.52  sim_bw_subsumed:                        18
% 7.75/1.52  sim_fw_subsumption_res:                 0
% 7.75/1.52  sim_bw_subsumption_res:                 0
% 7.75/1.52  sim_tautology_del:                      2
% 7.75/1.52  sim_eq_tautology_del:                   39
% 7.75/1.52  sim_eq_res_simp:                        6
% 7.75/1.52  sim_fw_demodulated:                     106
% 7.75/1.52  sim_bw_demodulated:                     122
% 7.75/1.52  sim_light_normalised:                   32
% 7.75/1.52  sim_joinable_taut:                      0
% 7.75/1.52  sim_joinable_simp:                      0
% 7.75/1.52  sim_ac_normalised:                      0
% 7.75/1.52  sim_smt_subsumption:                    0
% 7.75/1.52  
%------------------------------------------------------------------------------
