%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:58 EST 2020

% Result     : Theorem 7.55s
% Output     : CNFRefutation 7.55s
% Verified   : 
% Statistics : Number of formulae       :  274 (26319 expanded)
%              Number of clauses        :  194 (10083 expanded)
%              Number of leaves         :   20 (4709 expanded)
%              Depth                    :   36
%              Number of atoms          :  813 (129335 expanded)
%              Number of equality atoms :  483 (37410 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f73,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
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

fof(f75,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

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

fof(f76,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f46])).

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
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

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

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f53])).

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

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_415,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_417,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_28])).

cnf(c_1037,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1044,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1934,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1037,c_1044])).

cnf(c_2203,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_417,c_1934])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1038,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1043,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4661,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1043])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1042,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5634,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4661,c_1042])).

cnf(c_8888,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5634,c_1042])).

cnf(c_21750,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1038,c_8888])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1041,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1048,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2585,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1041,c_1048])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1047,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6449,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2585,c_1047])).

cnf(c_21805,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK0,sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_partfun1(X0,sK1,sK2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21750,c_6449])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1050,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1045,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2739,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_relat_1(X0))) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1050,c_1045])).

cnf(c_22512,plain,
    ( k1_relat_1(k7_relat_1(k2_partfun1(X0,sK1,sK2,X1),k1_relat_1(k2_partfun1(X0,sK1,sK2,X1)))) = k1_relat_1(k2_partfun1(X0,sK1,sK2,X1))
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK0,sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_21805,c_2739])).

cnf(c_34,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
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

cnf(c_631,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1395,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1494,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1497,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1494])).

cnf(c_632,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1289,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_1516,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1289])).

cnf(c_1517,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_2180,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_2181,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2180])).

cnf(c_633,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1499,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK3)
    | X2 != X0
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_5240,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,sK3)
    | sK3 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1499])).

cnf(c_7398,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(sK0,sK3)
    | sK3 != sK3
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_5240])).

cnf(c_7399,plain,
    ( sK3 != sK3
    | sK0 != X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7398])).

cnf(c_7401,plain,
    ( sK3 != sK3
    | sK0 != k1_xboole_0
    | r1_tarski(sK0,sK3) = iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7399])).

cnf(c_2432,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1048])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1310,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1649,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1310])).

cnf(c_1650,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1649])).

cnf(c_1256,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1728,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1256])).

cnf(c_1737,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1728])).

cnf(c_1876,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1877,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1876])).

cnf(c_1311,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1881,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1311])).

cnf(c_1882,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1881])).

cnf(c_2435,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2432,c_33,c_1650,c_1737,c_1877,c_1882])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_294,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_12,c_10])).

cnf(c_1035,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_1470,plain,
    ( k7_relat_1(sK3,sK0) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1035])).

cnf(c_2440,plain,
    ( k7_relat_1(sK3,sK0) = sK3 ),
    inference(superposition,[status(thm)],[c_2435,c_1470])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1046,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3021,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2440,c_1046])).

cnf(c_3444,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3021,c_33,c_1650,c_1737,c_1877,c_1882])).

cnf(c_3445,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3444])).

cnf(c_2741,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2203,c_1045])).

cnf(c_3041,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2741,c_33,c_1650,c_1737,c_1877,c_1882])).

cnf(c_3042,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3041])).

cnf(c_3052,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1038,c_3042])).

cnf(c_3614,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1042])).

cnf(c_4662,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3614,c_1043])).

cnf(c_8243,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4662,c_1042])).

cnf(c_19671,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3052,c_8243])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1039,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5307,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1039])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1352,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_4071,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1352])).

cnf(c_5559,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5307,c_30,c_28,c_4071])).

cnf(c_5615,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5559,c_1041])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8967,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5615,c_31,c_33])).

cnf(c_8980,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8967,c_1043])).

cnf(c_13127,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X1)) = k1_relat_1(k7_relat_1(sK3,X1))
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8980,c_1044])).

cnf(c_33189,plain,
    ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_1050,c_13127])).

cnf(c_33588,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3052,c_33189])).

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

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_399,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_1030,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_5566,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5559,c_1030])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1040,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1955,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1040])).

cnf(c_1332,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1568,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1332])).

cnf(c_1569,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_2243,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1955,c_31,c_33,c_1569])).

cnf(c_5567,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5559,c_2243])).

cnf(c_5574,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5566,c_5567])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1273,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1290,plain,
    ( sK2 != X0
    | sK2 = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_1291,plain,
    ( sK2 = sK0
    | sK2 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1290])).

cnf(c_1511,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_1616,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,sK2)
    | sK2 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_2657,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(sK0,sK2)
    | sK2 != sK2
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1616])).

cnf(c_2659,plain,
    ( r1_tarski(sK0,sK2)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 != sK2
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2657])).

cnf(c_1441,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_2216,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1441])).

cnf(c_5140,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2216])).

cnf(c_5467,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_425,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_501,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_425])).

cnf(c_1029,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_5565,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5559,c_1029])).

cnf(c_5582,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5565,c_5567])).

cnf(c_3020,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,X0)) = iProver_top
    | r1_tarski(sK0,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2440,c_1046])).

cnf(c_3422,plain,
    ( r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(sK3,k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3020,c_33,c_1650,c_1737,c_1877,c_1882])).

cnf(c_3423,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,X0)) = iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3422])).

cnf(c_1051,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3431,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3423,c_1051])).

cnf(c_3547,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3445,c_3431])).

cnf(c_13522,plain,
    ( k7_relat_1(sK3,sK2) = sK3
    | r1_tarski(sK0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1038,c_3547])).

cnf(c_13532,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k7_relat_1(sK3,sK2) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13522])).

cnf(c_15915,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5574,c_27,c_26,c_84,c_85,c_1273,c_1291,c_1511,c_1516,c_1517,c_2181,c_2659,c_5140,c_5467,c_5582,c_13532])).

cnf(c_34071,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_33588,c_15915])).

cnf(c_16,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_320,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_321,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_1034,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1178,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1034,c_4])).

cnf(c_5564,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5559,c_1178])).

cnf(c_5592,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5564,c_5567])).

cnf(c_28271,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5592,c_27,c_26,c_84,c_85,c_1273,c_1291,c_1511,c_1516,c_1517,c_2181,c_2659,c_5140,c_5467,c_5582,c_13532])).

cnf(c_28272,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_28271])).

cnf(c_34342,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34071,c_3052,c_28272])).

cnf(c_34350,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_19671,c_34342])).

cnf(c_5135,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5138,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5135])).

cnf(c_36688,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_34350,c_5138])).

cnf(c_36689,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_36688])).

cnf(c_36695,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_36689,c_1050])).

cnf(c_36698,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3445,c_36695])).

cnf(c_38519,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | k1_relat_1(k7_relat_1(k2_partfun1(X0,sK1,sK2,X1),k1_relat_1(k2_partfun1(X0,sK1,sK2,X1)))) = k1_relat_1(k2_partfun1(X0,sK1,sK2,X1))
    | v1_funct_1(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22512,c_34,c_26,c_84,c_85,c_1395,c_1497,c_1516,c_1517,c_2181,c_7401,c_36698])).

cnf(c_38520,plain,
    ( k1_relat_1(k7_relat_1(k2_partfun1(X0,sK1,sK2,X1),k1_relat_1(k2_partfun1(X0,sK1,sK2,X1)))) = k1_relat_1(k2_partfun1(X0,sK1,sK2,X1))
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_38519])).

cnf(c_38529,plain,
    ( k1_relat_1(k7_relat_1(k2_partfun1(X0,sK1,sK2,X1),k1_relat_1(k2_partfun1(X0,sK1,sK2,X1)))) = k1_relat_1(k2_partfun1(X0,sK1,sK2,X1))
    | sK1 = k1_xboole_0
    | r1_tarski(sK0,X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2203,c_38520])).

cnf(c_38549,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_38529,c_34,c_36698])).

cnf(c_38667,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_38549,c_1934])).

cnf(c_38672,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_38549,c_26])).

cnf(c_38673,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_38672])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_386,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_1031,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_1104,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1031,c_5])).

cnf(c_38669,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_38549,c_1104])).

cnf(c_38680,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38669,c_38673])).

cnf(c_38681,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_38680])).

cnf(c_38671,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_38549,c_1037])).

cnf(c_38676,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38671,c_38673])).

cnf(c_38678,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_38676,c_5])).

cnf(c_38684,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_38681,c_38678])).

cnf(c_38687,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_38667,c_38673,c_38684])).

cnf(c_34353,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5634,c_34342])).

cnf(c_34398,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3445,c_34353])).

cnf(c_34408,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ r1_tarski(sK2,sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_34398])).

cnf(c_1337,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X2),X3)
    | X3 != X1
    | k1_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_28223,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK3),sK2)
    | k1_relat_1(sK3) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1337])).

cnf(c_28225,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK3) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_28223])).

cnf(c_87,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38687,c_36698,c_34408,c_28225,c_5467,c_5140,c_2181,c_1511,c_1273,c_87,c_85,c_84,c_26,c_34,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.55/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.55/1.48  
% 7.55/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.55/1.48  
% 7.55/1.48  ------  iProver source info
% 7.55/1.48  
% 7.55/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.55/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.55/1.48  git: non_committed_changes: false
% 7.55/1.48  git: last_make_outside_of_git: false
% 7.55/1.48  
% 7.55/1.48  ------ 
% 7.55/1.48  
% 7.55/1.48  ------ Input Options
% 7.55/1.48  
% 7.55/1.48  --out_options                           all
% 7.55/1.48  --tptp_safe_out                         true
% 7.55/1.48  --problem_path                          ""
% 7.55/1.48  --include_path                          ""
% 7.55/1.48  --clausifier                            res/vclausify_rel
% 7.55/1.48  --clausifier_options                    --mode clausify
% 7.55/1.48  --stdin                                 false
% 7.55/1.48  --stats_out                             all
% 7.55/1.48  
% 7.55/1.48  ------ General Options
% 7.55/1.48  
% 7.55/1.48  --fof                                   false
% 7.55/1.48  --time_out_real                         305.
% 7.55/1.48  --time_out_virtual                      -1.
% 7.55/1.48  --symbol_type_check                     false
% 7.55/1.48  --clausify_out                          false
% 7.55/1.48  --sig_cnt_out                           false
% 7.55/1.48  --trig_cnt_out                          false
% 7.55/1.48  --trig_cnt_out_tolerance                1.
% 7.55/1.48  --trig_cnt_out_sk_spl                   false
% 7.55/1.48  --abstr_cl_out                          false
% 7.55/1.48  
% 7.55/1.48  ------ Global Options
% 7.55/1.48  
% 7.55/1.48  --schedule                              default
% 7.55/1.48  --add_important_lit                     false
% 7.55/1.48  --prop_solver_per_cl                    1000
% 7.55/1.48  --min_unsat_core                        false
% 7.55/1.48  --soft_assumptions                      false
% 7.55/1.48  --soft_lemma_size                       3
% 7.55/1.48  --prop_impl_unit_size                   0
% 7.55/1.48  --prop_impl_unit                        []
% 7.55/1.48  --share_sel_clauses                     true
% 7.55/1.48  --reset_solvers                         false
% 7.55/1.48  --bc_imp_inh                            [conj_cone]
% 7.55/1.48  --conj_cone_tolerance                   3.
% 7.55/1.48  --extra_neg_conj                        none
% 7.55/1.48  --large_theory_mode                     true
% 7.55/1.48  --prolific_symb_bound                   200
% 7.55/1.48  --lt_threshold                          2000
% 7.55/1.48  --clause_weak_htbl                      true
% 7.55/1.48  --gc_record_bc_elim                     false
% 7.55/1.48  
% 7.55/1.48  ------ Preprocessing Options
% 7.55/1.48  
% 7.55/1.48  --preprocessing_flag                    true
% 7.55/1.48  --time_out_prep_mult                    0.1
% 7.55/1.48  --splitting_mode                        input
% 7.55/1.48  --splitting_grd                         true
% 7.55/1.48  --splitting_cvd                         false
% 7.55/1.48  --splitting_cvd_svl                     false
% 7.55/1.48  --splitting_nvd                         32
% 7.55/1.48  --sub_typing                            true
% 7.55/1.48  --prep_gs_sim                           true
% 7.55/1.48  --prep_unflatten                        true
% 7.55/1.48  --prep_res_sim                          true
% 7.55/1.48  --prep_upred                            true
% 7.55/1.48  --prep_sem_filter                       exhaustive
% 7.55/1.48  --prep_sem_filter_out                   false
% 7.55/1.48  --pred_elim                             true
% 7.55/1.48  --res_sim_input                         true
% 7.55/1.48  --eq_ax_congr_red                       true
% 7.55/1.48  --pure_diseq_elim                       true
% 7.55/1.48  --brand_transform                       false
% 7.55/1.48  --non_eq_to_eq                          false
% 7.55/1.48  --prep_def_merge                        true
% 7.55/1.48  --prep_def_merge_prop_impl              false
% 7.55/1.48  --prep_def_merge_mbd                    true
% 7.55/1.48  --prep_def_merge_tr_red                 false
% 7.55/1.48  --prep_def_merge_tr_cl                  false
% 7.55/1.48  --smt_preprocessing                     true
% 7.55/1.48  --smt_ac_axioms                         fast
% 7.55/1.48  --preprocessed_out                      false
% 7.55/1.48  --preprocessed_stats                    false
% 7.55/1.48  
% 7.55/1.48  ------ Abstraction refinement Options
% 7.55/1.48  
% 7.55/1.48  --abstr_ref                             []
% 7.55/1.48  --abstr_ref_prep                        false
% 7.55/1.48  --abstr_ref_until_sat                   false
% 7.55/1.48  --abstr_ref_sig_restrict                funpre
% 7.55/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.55/1.48  --abstr_ref_under                       []
% 7.55/1.48  
% 7.55/1.48  ------ SAT Options
% 7.55/1.48  
% 7.55/1.48  --sat_mode                              false
% 7.55/1.48  --sat_fm_restart_options                ""
% 7.55/1.48  --sat_gr_def                            false
% 7.55/1.48  --sat_epr_types                         true
% 7.55/1.48  --sat_non_cyclic_types                  false
% 7.55/1.48  --sat_finite_models                     false
% 7.55/1.48  --sat_fm_lemmas                         false
% 7.55/1.48  --sat_fm_prep                           false
% 7.55/1.48  --sat_fm_uc_incr                        true
% 7.55/1.48  --sat_out_model                         small
% 7.55/1.48  --sat_out_clauses                       false
% 7.55/1.48  
% 7.55/1.48  ------ QBF Options
% 7.55/1.48  
% 7.55/1.48  --qbf_mode                              false
% 7.55/1.48  --qbf_elim_univ                         false
% 7.55/1.48  --qbf_dom_inst                          none
% 7.55/1.48  --qbf_dom_pre_inst                      false
% 7.55/1.48  --qbf_sk_in                             false
% 7.55/1.48  --qbf_pred_elim                         true
% 7.55/1.48  --qbf_split                             512
% 7.55/1.48  
% 7.55/1.48  ------ BMC1 Options
% 7.55/1.48  
% 7.55/1.48  --bmc1_incremental                      false
% 7.55/1.48  --bmc1_axioms                           reachable_all
% 7.55/1.48  --bmc1_min_bound                        0
% 7.55/1.48  --bmc1_max_bound                        -1
% 7.55/1.48  --bmc1_max_bound_default                -1
% 7.55/1.48  --bmc1_symbol_reachability              true
% 7.55/1.48  --bmc1_property_lemmas                  false
% 7.55/1.48  --bmc1_k_induction                      false
% 7.55/1.48  --bmc1_non_equiv_states                 false
% 7.55/1.48  --bmc1_deadlock                         false
% 7.55/1.48  --bmc1_ucm                              false
% 7.55/1.48  --bmc1_add_unsat_core                   none
% 7.55/1.48  --bmc1_unsat_core_children              false
% 7.55/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.55/1.48  --bmc1_out_stat                         full
% 7.55/1.48  --bmc1_ground_init                      false
% 7.55/1.48  --bmc1_pre_inst_next_state              false
% 7.55/1.48  --bmc1_pre_inst_state                   false
% 7.55/1.48  --bmc1_pre_inst_reach_state             false
% 7.55/1.48  --bmc1_out_unsat_core                   false
% 7.55/1.48  --bmc1_aig_witness_out                  false
% 7.55/1.48  --bmc1_verbose                          false
% 7.55/1.48  --bmc1_dump_clauses_tptp                false
% 7.55/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.55/1.48  --bmc1_dump_file                        -
% 7.55/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.55/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.55/1.48  --bmc1_ucm_extend_mode                  1
% 7.55/1.48  --bmc1_ucm_init_mode                    2
% 7.55/1.48  --bmc1_ucm_cone_mode                    none
% 7.55/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.55/1.48  --bmc1_ucm_relax_model                  4
% 7.55/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.55/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.55/1.48  --bmc1_ucm_layered_model                none
% 7.55/1.48  --bmc1_ucm_max_lemma_size               10
% 7.55/1.48  
% 7.55/1.48  ------ AIG Options
% 7.55/1.48  
% 7.55/1.48  --aig_mode                              false
% 7.55/1.48  
% 7.55/1.48  ------ Instantiation Options
% 7.55/1.48  
% 7.55/1.48  --instantiation_flag                    true
% 7.55/1.48  --inst_sos_flag                         false
% 7.55/1.48  --inst_sos_phase                        true
% 7.55/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.55/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.55/1.48  --inst_lit_sel_side                     num_symb
% 7.55/1.48  --inst_solver_per_active                1400
% 7.55/1.48  --inst_solver_calls_frac                1.
% 7.55/1.48  --inst_passive_queue_type               priority_queues
% 7.55/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.55/1.48  --inst_passive_queues_freq              [25;2]
% 7.55/1.48  --inst_dismatching                      true
% 7.55/1.48  --inst_eager_unprocessed_to_passive     true
% 7.55/1.48  --inst_prop_sim_given                   true
% 7.55/1.48  --inst_prop_sim_new                     false
% 7.55/1.48  --inst_subs_new                         false
% 7.55/1.48  --inst_eq_res_simp                      false
% 7.55/1.48  --inst_subs_given                       false
% 7.55/1.48  --inst_orphan_elimination               true
% 7.55/1.48  --inst_learning_loop_flag               true
% 7.55/1.48  --inst_learning_start                   3000
% 7.55/1.48  --inst_learning_factor                  2
% 7.55/1.48  --inst_start_prop_sim_after_learn       3
% 7.55/1.48  --inst_sel_renew                        solver
% 7.55/1.48  --inst_lit_activity_flag                true
% 7.55/1.48  --inst_restr_to_given                   false
% 7.55/1.48  --inst_activity_threshold               500
% 7.55/1.48  --inst_out_proof                        true
% 7.55/1.48  
% 7.55/1.48  ------ Resolution Options
% 7.55/1.48  
% 7.55/1.48  --resolution_flag                       true
% 7.55/1.48  --res_lit_sel                           adaptive
% 7.55/1.48  --res_lit_sel_side                      none
% 7.55/1.48  --res_ordering                          kbo
% 7.55/1.48  --res_to_prop_solver                    active
% 7.55/1.48  --res_prop_simpl_new                    false
% 7.55/1.48  --res_prop_simpl_given                  true
% 7.55/1.48  --res_passive_queue_type                priority_queues
% 7.55/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.55/1.48  --res_passive_queues_freq               [15;5]
% 7.55/1.48  --res_forward_subs                      full
% 7.55/1.48  --res_backward_subs                     full
% 7.55/1.48  --res_forward_subs_resolution           true
% 7.55/1.48  --res_backward_subs_resolution          true
% 7.55/1.48  --res_orphan_elimination                true
% 7.55/1.48  --res_time_limit                        2.
% 7.55/1.48  --res_out_proof                         true
% 7.55/1.48  
% 7.55/1.48  ------ Superposition Options
% 7.55/1.48  
% 7.55/1.48  --superposition_flag                    true
% 7.55/1.48  --sup_passive_queue_type                priority_queues
% 7.55/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.55/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.55/1.48  --demod_completeness_check              fast
% 7.55/1.48  --demod_use_ground                      true
% 7.55/1.48  --sup_to_prop_solver                    passive
% 7.55/1.48  --sup_prop_simpl_new                    true
% 7.55/1.48  --sup_prop_simpl_given                  true
% 7.55/1.48  --sup_fun_splitting                     false
% 7.55/1.48  --sup_smt_interval                      50000
% 7.55/1.48  
% 7.55/1.48  ------ Superposition Simplification Setup
% 7.55/1.48  
% 7.55/1.48  --sup_indices_passive                   []
% 7.55/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.55/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.48  --sup_full_bw                           [BwDemod]
% 7.55/1.48  --sup_immed_triv                        [TrivRules]
% 7.55/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.55/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.48  --sup_immed_bw_main                     []
% 7.55/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.55/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.48  
% 7.55/1.48  ------ Combination Options
% 7.55/1.48  
% 7.55/1.48  --comb_res_mult                         3
% 7.55/1.48  --comb_sup_mult                         2
% 7.55/1.48  --comb_inst_mult                        10
% 7.55/1.48  
% 7.55/1.48  ------ Debug Options
% 7.55/1.48  
% 7.55/1.48  --dbg_backtrace                         false
% 7.55/1.48  --dbg_dump_prop_clauses                 false
% 7.55/1.48  --dbg_dump_prop_clauses_file            -
% 7.55/1.48  --dbg_out_stat                          false
% 7.55/1.48  ------ Parsing...
% 7.55/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.55/1.48  
% 7.55/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.55/1.48  
% 7.55/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.55/1.48  
% 7.55/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.55/1.48  ------ Proving...
% 7.55/1.48  ------ Problem Properties 
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  clauses                                 28
% 7.55/1.48  conjectures                             4
% 7.55/1.48  EPR                                     6
% 7.55/1.48  Horn                                    25
% 7.55/1.48  unary                                   8
% 7.55/1.48  binary                                  3
% 7.55/1.48  lits                                    73
% 7.55/1.48  lits eq                                 28
% 7.55/1.48  fd_pure                                 0
% 7.55/1.48  fd_pseudo                               0
% 7.55/1.48  fd_cond                                 1
% 7.55/1.48  fd_pseudo_cond                          1
% 7.55/1.48  AC symbols                              0
% 7.55/1.48  
% 7.55/1.48  ------ Schedule dynamic 5 is on 
% 7.55/1.48  
% 7.55/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  ------ 
% 7.55/1.48  Current options:
% 7.55/1.48  ------ 
% 7.55/1.48  
% 7.55/1.48  ------ Input Options
% 7.55/1.48  
% 7.55/1.48  --out_options                           all
% 7.55/1.48  --tptp_safe_out                         true
% 7.55/1.48  --problem_path                          ""
% 7.55/1.48  --include_path                          ""
% 7.55/1.48  --clausifier                            res/vclausify_rel
% 7.55/1.48  --clausifier_options                    --mode clausify
% 7.55/1.48  --stdin                                 false
% 7.55/1.48  --stats_out                             all
% 7.55/1.48  
% 7.55/1.48  ------ General Options
% 7.55/1.48  
% 7.55/1.48  --fof                                   false
% 7.55/1.48  --time_out_real                         305.
% 7.55/1.48  --time_out_virtual                      -1.
% 7.55/1.48  --symbol_type_check                     false
% 7.55/1.48  --clausify_out                          false
% 7.55/1.48  --sig_cnt_out                           false
% 7.55/1.48  --trig_cnt_out                          false
% 7.55/1.48  --trig_cnt_out_tolerance                1.
% 7.55/1.48  --trig_cnt_out_sk_spl                   false
% 7.55/1.48  --abstr_cl_out                          false
% 7.55/1.48  
% 7.55/1.48  ------ Global Options
% 7.55/1.48  
% 7.55/1.48  --schedule                              default
% 7.55/1.48  --add_important_lit                     false
% 7.55/1.48  --prop_solver_per_cl                    1000
% 7.55/1.48  --min_unsat_core                        false
% 7.55/1.48  --soft_assumptions                      false
% 7.55/1.48  --soft_lemma_size                       3
% 7.55/1.48  --prop_impl_unit_size                   0
% 7.55/1.48  --prop_impl_unit                        []
% 7.55/1.48  --share_sel_clauses                     true
% 7.55/1.48  --reset_solvers                         false
% 7.55/1.48  --bc_imp_inh                            [conj_cone]
% 7.55/1.48  --conj_cone_tolerance                   3.
% 7.55/1.48  --extra_neg_conj                        none
% 7.55/1.48  --large_theory_mode                     true
% 7.55/1.48  --prolific_symb_bound                   200
% 7.55/1.48  --lt_threshold                          2000
% 7.55/1.48  --clause_weak_htbl                      true
% 7.55/1.48  --gc_record_bc_elim                     false
% 7.55/1.48  
% 7.55/1.48  ------ Preprocessing Options
% 7.55/1.48  
% 7.55/1.48  --preprocessing_flag                    true
% 7.55/1.48  --time_out_prep_mult                    0.1
% 7.55/1.48  --splitting_mode                        input
% 7.55/1.48  --splitting_grd                         true
% 7.55/1.48  --splitting_cvd                         false
% 7.55/1.48  --splitting_cvd_svl                     false
% 7.55/1.48  --splitting_nvd                         32
% 7.55/1.48  --sub_typing                            true
% 7.55/1.48  --prep_gs_sim                           true
% 7.55/1.48  --prep_unflatten                        true
% 7.55/1.48  --prep_res_sim                          true
% 7.55/1.48  --prep_upred                            true
% 7.55/1.48  --prep_sem_filter                       exhaustive
% 7.55/1.48  --prep_sem_filter_out                   false
% 7.55/1.48  --pred_elim                             true
% 7.55/1.48  --res_sim_input                         true
% 7.55/1.48  --eq_ax_congr_red                       true
% 7.55/1.48  --pure_diseq_elim                       true
% 7.55/1.48  --brand_transform                       false
% 7.55/1.48  --non_eq_to_eq                          false
% 7.55/1.48  --prep_def_merge                        true
% 7.55/1.48  --prep_def_merge_prop_impl              false
% 7.55/1.48  --prep_def_merge_mbd                    true
% 7.55/1.48  --prep_def_merge_tr_red                 false
% 7.55/1.48  --prep_def_merge_tr_cl                  false
% 7.55/1.48  --smt_preprocessing                     true
% 7.55/1.48  --smt_ac_axioms                         fast
% 7.55/1.48  --preprocessed_out                      false
% 7.55/1.48  --preprocessed_stats                    false
% 7.55/1.48  
% 7.55/1.48  ------ Abstraction refinement Options
% 7.55/1.48  
% 7.55/1.48  --abstr_ref                             []
% 7.55/1.48  --abstr_ref_prep                        false
% 7.55/1.48  --abstr_ref_until_sat                   false
% 7.55/1.48  --abstr_ref_sig_restrict                funpre
% 7.55/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.55/1.48  --abstr_ref_under                       []
% 7.55/1.48  
% 7.55/1.48  ------ SAT Options
% 7.55/1.48  
% 7.55/1.48  --sat_mode                              false
% 7.55/1.48  --sat_fm_restart_options                ""
% 7.55/1.48  --sat_gr_def                            false
% 7.55/1.48  --sat_epr_types                         true
% 7.55/1.48  --sat_non_cyclic_types                  false
% 7.55/1.48  --sat_finite_models                     false
% 7.55/1.48  --sat_fm_lemmas                         false
% 7.55/1.48  --sat_fm_prep                           false
% 7.55/1.48  --sat_fm_uc_incr                        true
% 7.55/1.48  --sat_out_model                         small
% 7.55/1.48  --sat_out_clauses                       false
% 7.55/1.48  
% 7.55/1.48  ------ QBF Options
% 7.55/1.48  
% 7.55/1.48  --qbf_mode                              false
% 7.55/1.48  --qbf_elim_univ                         false
% 7.55/1.48  --qbf_dom_inst                          none
% 7.55/1.48  --qbf_dom_pre_inst                      false
% 7.55/1.48  --qbf_sk_in                             false
% 7.55/1.48  --qbf_pred_elim                         true
% 7.55/1.48  --qbf_split                             512
% 7.55/1.48  
% 7.55/1.48  ------ BMC1 Options
% 7.55/1.48  
% 7.55/1.48  --bmc1_incremental                      false
% 7.55/1.48  --bmc1_axioms                           reachable_all
% 7.55/1.48  --bmc1_min_bound                        0
% 7.55/1.48  --bmc1_max_bound                        -1
% 7.55/1.48  --bmc1_max_bound_default                -1
% 7.55/1.48  --bmc1_symbol_reachability              true
% 7.55/1.48  --bmc1_property_lemmas                  false
% 7.55/1.48  --bmc1_k_induction                      false
% 7.55/1.48  --bmc1_non_equiv_states                 false
% 7.55/1.48  --bmc1_deadlock                         false
% 7.55/1.48  --bmc1_ucm                              false
% 7.55/1.48  --bmc1_add_unsat_core                   none
% 7.55/1.48  --bmc1_unsat_core_children              false
% 7.55/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.55/1.48  --bmc1_out_stat                         full
% 7.55/1.48  --bmc1_ground_init                      false
% 7.55/1.48  --bmc1_pre_inst_next_state              false
% 7.55/1.48  --bmc1_pre_inst_state                   false
% 7.55/1.48  --bmc1_pre_inst_reach_state             false
% 7.55/1.48  --bmc1_out_unsat_core                   false
% 7.55/1.48  --bmc1_aig_witness_out                  false
% 7.55/1.48  --bmc1_verbose                          false
% 7.55/1.48  --bmc1_dump_clauses_tptp                false
% 7.55/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.55/1.48  --bmc1_dump_file                        -
% 7.55/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.55/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.55/1.48  --bmc1_ucm_extend_mode                  1
% 7.55/1.48  --bmc1_ucm_init_mode                    2
% 7.55/1.48  --bmc1_ucm_cone_mode                    none
% 7.55/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.55/1.48  --bmc1_ucm_relax_model                  4
% 7.55/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.55/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.55/1.48  --bmc1_ucm_layered_model                none
% 7.55/1.48  --bmc1_ucm_max_lemma_size               10
% 7.55/1.48  
% 7.55/1.48  ------ AIG Options
% 7.55/1.48  
% 7.55/1.48  --aig_mode                              false
% 7.55/1.48  
% 7.55/1.48  ------ Instantiation Options
% 7.55/1.48  
% 7.55/1.48  --instantiation_flag                    true
% 7.55/1.48  --inst_sos_flag                         false
% 7.55/1.48  --inst_sos_phase                        true
% 7.55/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.55/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.55/1.48  --inst_lit_sel_side                     none
% 7.55/1.48  --inst_solver_per_active                1400
% 7.55/1.48  --inst_solver_calls_frac                1.
% 7.55/1.48  --inst_passive_queue_type               priority_queues
% 7.55/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.55/1.48  --inst_passive_queues_freq              [25;2]
% 7.55/1.48  --inst_dismatching                      true
% 7.55/1.48  --inst_eager_unprocessed_to_passive     true
% 7.55/1.48  --inst_prop_sim_given                   true
% 7.55/1.48  --inst_prop_sim_new                     false
% 7.55/1.48  --inst_subs_new                         false
% 7.55/1.48  --inst_eq_res_simp                      false
% 7.55/1.48  --inst_subs_given                       false
% 7.55/1.48  --inst_orphan_elimination               true
% 7.55/1.48  --inst_learning_loop_flag               true
% 7.55/1.48  --inst_learning_start                   3000
% 7.55/1.48  --inst_learning_factor                  2
% 7.55/1.48  --inst_start_prop_sim_after_learn       3
% 7.55/1.48  --inst_sel_renew                        solver
% 7.55/1.48  --inst_lit_activity_flag                true
% 7.55/1.48  --inst_restr_to_given                   false
% 7.55/1.48  --inst_activity_threshold               500
% 7.55/1.48  --inst_out_proof                        true
% 7.55/1.48  
% 7.55/1.48  ------ Resolution Options
% 7.55/1.48  
% 7.55/1.48  --resolution_flag                       false
% 7.55/1.48  --res_lit_sel                           adaptive
% 7.55/1.48  --res_lit_sel_side                      none
% 7.55/1.48  --res_ordering                          kbo
% 7.55/1.48  --res_to_prop_solver                    active
% 7.55/1.48  --res_prop_simpl_new                    false
% 7.55/1.48  --res_prop_simpl_given                  true
% 7.55/1.48  --res_passive_queue_type                priority_queues
% 7.55/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.55/1.48  --res_passive_queues_freq               [15;5]
% 7.55/1.48  --res_forward_subs                      full
% 7.55/1.48  --res_backward_subs                     full
% 7.55/1.48  --res_forward_subs_resolution           true
% 7.55/1.48  --res_backward_subs_resolution          true
% 7.55/1.48  --res_orphan_elimination                true
% 7.55/1.48  --res_time_limit                        2.
% 7.55/1.48  --res_out_proof                         true
% 7.55/1.48  
% 7.55/1.48  ------ Superposition Options
% 7.55/1.48  
% 7.55/1.48  --superposition_flag                    true
% 7.55/1.48  --sup_passive_queue_type                priority_queues
% 7.55/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.55/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.55/1.48  --demod_completeness_check              fast
% 7.55/1.48  --demod_use_ground                      true
% 7.55/1.48  --sup_to_prop_solver                    passive
% 7.55/1.48  --sup_prop_simpl_new                    true
% 7.55/1.48  --sup_prop_simpl_given                  true
% 7.55/1.48  --sup_fun_splitting                     false
% 7.55/1.48  --sup_smt_interval                      50000
% 7.55/1.48  
% 7.55/1.48  ------ Superposition Simplification Setup
% 7.55/1.48  
% 7.55/1.48  --sup_indices_passive                   []
% 7.55/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.55/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.48  --sup_full_bw                           [BwDemod]
% 7.55/1.48  --sup_immed_triv                        [TrivRules]
% 7.55/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.55/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.48  --sup_immed_bw_main                     []
% 7.55/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.55/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.48  
% 7.55/1.48  ------ Combination Options
% 7.55/1.48  
% 7.55/1.48  --comb_res_mult                         3
% 7.55/1.48  --comb_sup_mult                         2
% 7.55/1.48  --comb_inst_mult                        10
% 7.55/1.48  
% 7.55/1.48  ------ Debug Options
% 7.55/1.48  
% 7.55/1.48  --dbg_backtrace                         false
% 7.55/1.48  --dbg_dump_prop_clauses                 false
% 7.55/1.48  --dbg_dump_prop_clauses_file            -
% 7.55/1.48  --dbg_out_stat                          false
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  ------ Proving...
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  % SZS status Theorem for theBenchmark.p
% 7.55/1.48  
% 7.55/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.55/1.48  
% 7.55/1.48  fof(f13,axiom,(
% 7.55/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.55/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f32,plain,(
% 7.55/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.55/1.48    inference(ennf_transformation,[],[f13])).
% 7.55/1.48  
% 7.55/1.48  fof(f33,plain,(
% 7.55/1.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.55/1.48    inference(flattening,[],[f32])).
% 7.55/1.48  
% 7.55/1.48  fof(f44,plain,(
% 7.55/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.55/1.48    inference(nnf_transformation,[],[f33])).
% 7.55/1.48  
% 7.55/1.48  fof(f63,plain,(
% 7.55/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.55/1.48    inference(cnf_transformation,[],[f44])).
% 7.55/1.48  
% 7.55/1.48  fof(f16,conjecture,(
% 7.55/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.55/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f17,negated_conjecture,(
% 7.55/1.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.55/1.48    inference(negated_conjecture,[],[f16])).
% 7.55/1.48  
% 7.55/1.48  fof(f38,plain,(
% 7.55/1.48    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.55/1.48    inference(ennf_transformation,[],[f17])).
% 7.55/1.48  
% 7.55/1.48  fof(f39,plain,(
% 7.55/1.48    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.55/1.48    inference(flattening,[],[f38])).
% 7.55/1.48  
% 7.55/1.48  fof(f45,plain,(
% 7.55/1.48    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 7.55/1.48    introduced(choice_axiom,[])).
% 7.55/1.48  
% 7.55/1.48  fof(f46,plain,(
% 7.55/1.48    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 7.55/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f45])).
% 7.55/1.48  
% 7.55/1.48  fof(f73,plain,(
% 7.55/1.48    v1_funct_2(sK3,sK0,sK1)),
% 7.55/1.48    inference(cnf_transformation,[],[f46])).
% 7.55/1.48  
% 7.55/1.48  fof(f74,plain,(
% 7.55/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.55/1.48    inference(cnf_transformation,[],[f46])).
% 7.55/1.48  
% 7.55/1.48  fof(f10,axiom,(
% 7.55/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.55/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f27,plain,(
% 7.55/1.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.55/1.48    inference(ennf_transformation,[],[f10])).
% 7.55/1.48  
% 7.55/1.48  fof(f60,plain,(
% 7.55/1.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.55/1.48    inference(cnf_transformation,[],[f27])).
% 7.55/1.48  
% 7.55/1.48  fof(f75,plain,(
% 7.55/1.48    r1_tarski(sK2,sK0)),
% 7.55/1.48    inference(cnf_transformation,[],[f46])).
% 7.55/1.48  
% 7.55/1.48  fof(f11,axiom,(
% 7.55/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 7.55/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f28,plain,(
% 7.55/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 7.55/1.48    inference(ennf_transformation,[],[f11])).
% 7.55/1.48  
% 7.55/1.48  fof(f29,plain,(
% 7.55/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 7.55/1.48    inference(flattening,[],[f28])).
% 7.55/1.48  
% 7.55/1.48  fof(f61,plain,(
% 7.55/1.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 7.55/1.48    inference(cnf_transformation,[],[f29])).
% 7.55/1.48  
% 7.55/1.48  fof(f12,axiom,(
% 7.55/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 7.55/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f30,plain,(
% 7.55/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 7.55/1.48    inference(ennf_transformation,[],[f12])).
% 7.55/1.48  
% 7.55/1.48  fof(f31,plain,(
% 7.55/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 7.55/1.48    inference(flattening,[],[f30])).
% 7.55/1.48  
% 7.55/1.48  fof(f62,plain,(
% 7.55/1.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 7.55/1.48    inference(cnf_transformation,[],[f31])).
% 7.55/1.48  
% 7.55/1.48  fof(f14,axiom,(
% 7.55/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 7.55/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f34,plain,(
% 7.55/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.55/1.48    inference(ennf_transformation,[],[f14])).
% 7.55/1.48  
% 7.55/1.48  fof(f35,plain,(
% 7.55/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.55/1.48    inference(flattening,[],[f34])).
% 7.55/1.48  
% 7.55/1.48  fof(f70,plain,(
% 7.55/1.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f35])).
% 7.55/1.48  
% 7.55/1.48  fof(f4,axiom,(
% 7.55/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.55/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f19,plain,(
% 7.55/1.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.55/1.48    inference(ennf_transformation,[],[f4])).
% 7.55/1.48  
% 7.55/1.48  fof(f54,plain,(
% 7.55/1.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f19])).
% 7.55/1.48  
% 7.55/1.48  fof(f5,axiom,(
% 7.55/1.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.55/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f55,plain,(
% 7.55/1.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.55/1.48    inference(cnf_transformation,[],[f5])).
% 7.55/1.48  
% 7.55/1.48  fof(f1,axiom,(
% 7.55/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.55/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f40,plain,(
% 7.55/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.55/1.48    inference(nnf_transformation,[],[f1])).
% 7.55/1.48  
% 7.55/1.48  fof(f41,plain,(
% 7.55/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.55/1.48    inference(flattening,[],[f40])).
% 7.55/1.48  
% 7.55/1.48  fof(f47,plain,(
% 7.55/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.55/1.48    inference(cnf_transformation,[],[f41])).
% 7.55/1.48  
% 7.55/1.48  fof(f79,plain,(
% 7.55/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.55/1.48    inference(equality_resolution,[],[f47])).
% 7.55/1.48  
% 7.55/1.48  fof(f8,axiom,(
% 7.55/1.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.55/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f24,plain,(
% 7.55/1.48    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.55/1.48    inference(ennf_transformation,[],[f8])).
% 7.55/1.48  
% 7.55/1.48  fof(f25,plain,(
% 7.55/1.48    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.55/1.48    inference(flattening,[],[f24])).
% 7.55/1.48  
% 7.55/1.48  fof(f58,plain,(
% 7.55/1.48    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f25])).
% 7.55/1.48  
% 7.55/1.48  fof(f76,plain,(
% 7.55/1.48    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 7.55/1.48    inference(cnf_transformation,[],[f46])).
% 7.55/1.48  
% 7.55/1.48  fof(f3,axiom,(
% 7.55/1.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.55/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f42,plain,(
% 7.55/1.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.55/1.48    inference(nnf_transformation,[],[f3])).
% 7.55/1.48  
% 7.55/1.48  fof(f43,plain,(
% 7.55/1.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.55/1.48    inference(flattening,[],[f42])).
% 7.55/1.48  
% 7.55/1.48  fof(f51,plain,(
% 7.55/1.48    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f43])).
% 7.55/1.48  
% 7.55/1.48  fof(f52,plain,(
% 7.55/1.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.55/1.48    inference(cnf_transformation,[],[f43])).
% 7.55/1.48  
% 7.55/1.48  fof(f81,plain,(
% 7.55/1.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.55/1.48    inference(equality_resolution,[],[f52])).
% 7.55/1.48  
% 7.55/1.48  fof(f2,axiom,(
% 7.55/1.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.55/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f50,plain,(
% 7.55/1.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f2])).
% 7.55/1.48  
% 7.55/1.48  fof(f9,axiom,(
% 7.55/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.55/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f18,plain,(
% 7.55/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.55/1.48    inference(pure_predicate_removal,[],[f9])).
% 7.55/1.48  
% 7.55/1.48  fof(f26,plain,(
% 7.55/1.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.55/1.48    inference(ennf_transformation,[],[f18])).
% 7.55/1.48  
% 7.55/1.48  fof(f59,plain,(
% 7.55/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.55/1.48    inference(cnf_transformation,[],[f26])).
% 7.55/1.48  
% 7.55/1.48  fof(f7,axiom,(
% 7.55/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.55/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f22,plain,(
% 7.55/1.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.55/1.48    inference(ennf_transformation,[],[f7])).
% 7.55/1.48  
% 7.55/1.48  fof(f23,plain,(
% 7.55/1.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.55/1.48    inference(flattening,[],[f22])).
% 7.55/1.48  
% 7.55/1.48  fof(f57,plain,(
% 7.55/1.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f23])).
% 7.55/1.48  
% 7.55/1.48  fof(f6,axiom,(
% 7.55/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))))),
% 7.55/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f20,plain,(
% 7.55/1.48    ! [X0,X1,X2] : ((r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 7.55/1.48    inference(ennf_transformation,[],[f6])).
% 7.55/1.48  
% 7.55/1.48  fof(f21,plain,(
% 7.55/1.48    ! [X0,X1,X2] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 7.55/1.48    inference(flattening,[],[f20])).
% 7.55/1.48  
% 7.55/1.48  fof(f56,plain,(
% 7.55/1.48    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f21])).
% 7.55/1.48  
% 7.55/1.48  fof(f15,axiom,(
% 7.55/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.55/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f36,plain,(
% 7.55/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.55/1.48    inference(ennf_transformation,[],[f15])).
% 7.55/1.48  
% 7.55/1.48  fof(f37,plain,(
% 7.55/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.55/1.48    inference(flattening,[],[f36])).
% 7.55/1.48  
% 7.55/1.48  fof(f71,plain,(
% 7.55/1.48    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f37])).
% 7.55/1.48  
% 7.55/1.48  fof(f72,plain,(
% 7.55/1.48    v1_funct_1(sK3)),
% 7.55/1.48    inference(cnf_transformation,[],[f46])).
% 7.55/1.48  
% 7.55/1.48  fof(f65,plain,(
% 7.55/1.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.55/1.48    inference(cnf_transformation,[],[f44])).
% 7.55/1.48  
% 7.55/1.48  fof(f77,plain,(
% 7.55/1.48    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 7.55/1.48    inference(cnf_transformation,[],[f46])).
% 7.55/1.48  
% 7.55/1.48  fof(f69,plain,(
% 7.55/1.48    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f35])).
% 7.55/1.48  
% 7.55/1.48  fof(f49,plain,(
% 7.55/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f41])).
% 7.55/1.48  
% 7.55/1.48  fof(f68,plain,(
% 7.55/1.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.55/1.48    inference(cnf_transformation,[],[f44])).
% 7.55/1.48  
% 7.55/1.48  fof(f82,plain,(
% 7.55/1.48    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.55/1.48    inference(equality_resolution,[],[f68])).
% 7.55/1.48  
% 7.55/1.48  fof(f83,plain,(
% 7.55/1.48    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.55/1.48    inference(equality_resolution,[],[f82])).
% 7.55/1.48  
% 7.55/1.48  fof(f53,plain,(
% 7.55/1.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.55/1.48    inference(cnf_transformation,[],[f43])).
% 7.55/1.48  
% 7.55/1.48  fof(f80,plain,(
% 7.55/1.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.55/1.48    inference(equality_resolution,[],[f53])).
% 7.55/1.48  
% 7.55/1.48  fof(f64,plain,(
% 7.55/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.55/1.48    inference(cnf_transformation,[],[f44])).
% 7.55/1.48  
% 7.55/1.48  fof(f86,plain,(
% 7.55/1.48    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.55/1.48    inference(equality_resolution,[],[f64])).
% 7.55/1.48  
% 7.55/1.48  cnf(c_21,plain,
% 7.55/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.55/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.55/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.55/1.48      | k1_xboole_0 = X2 ),
% 7.55/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_29,negated_conjecture,
% 7.55/1.48      ( v1_funct_2(sK3,sK0,sK1) ),
% 7.55/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_414,plain,
% 7.55/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.55/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.55/1.48      | sK3 != X0
% 7.55/1.48      | sK1 != X2
% 7.55/1.48      | sK0 != X1
% 7.55/1.48      | k1_xboole_0 = X2 ),
% 7.55/1.48      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_415,plain,
% 7.55/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.55/1.48      | k1_relset_1(sK0,sK1,sK3) = sK0
% 7.55/1.48      | k1_xboole_0 = sK1 ),
% 7.55/1.48      inference(unflattening,[status(thm)],[c_414]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_28,negated_conjecture,
% 7.55/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.55/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_417,plain,
% 7.55/1.48      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 7.55/1.48      inference(global_propositional_subsumption,
% 7.55/1.48                [status(thm)],
% 7.55/1.48                [c_415,c_28]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1037,plain,
% 7.55/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_13,plain,
% 7.55/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.55/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.55/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1044,plain,
% 7.55/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.55/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1934,plain,
% 7.55/1.48      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_1037,c_1044]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_2203,plain,
% 7.55/1.48      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_417,c_1934]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_27,negated_conjecture,
% 7.55/1.48      ( r1_tarski(sK2,sK0) ),
% 7.55/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1038,plain,
% 7.55/1.48      ( r1_tarski(sK2,sK0) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_14,plain,
% 7.55/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.55/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 7.55/1.48      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 7.55/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1043,plain,
% 7.55/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.55/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 7.55/1.48      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_4661,plain,
% 7.55/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 7.55/1.48      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_1037,c_1043]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_15,plain,
% 7.55/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.55/1.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.55/1.48      | ~ r1_tarski(X3,X0) ),
% 7.55/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1042,plain,
% 7.55/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.55/1.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.55/1.48      | r1_tarski(X3,X0) != iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_5634,plain,
% 7.55/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 7.55/1.48      | r1_tarski(X0,sK3) != iProver_top
% 7.55/1.48      | r1_tarski(k1_relat_1(sK3),X1) != iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_4661,c_1042]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_8888,plain,
% 7.55/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 7.55/1.48      | r1_tarski(X0,X2) != iProver_top
% 7.55/1.48      | r1_tarski(X2,sK3) != iProver_top
% 7.55/1.48      | r1_tarski(k1_relat_1(sK3),X1) != iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_5634,c_1042]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_21750,plain,
% 7.55/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 7.55/1.48      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.55/1.48      | r1_tarski(sK0,sK3) != iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_1038,c_8888]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_22,plain,
% 7.55/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.55/1.48      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.55/1.48      | ~ v1_funct_1(X0) ),
% 7.55/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1041,plain,
% 7.55/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.55/1.48      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.55/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_7,plain,
% 7.55/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.55/1.48      | ~ v1_relat_1(X1)
% 7.55/1.48      | v1_relat_1(X0) ),
% 7.55/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1048,plain,
% 7.55/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.55/1.48      | v1_relat_1(X1) != iProver_top
% 7.55/1.48      | v1_relat_1(X0) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_2585,plain,
% 7.55/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.55/1.48      | v1_funct_1(X0) != iProver_top
% 7.55/1.48      | v1_relat_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top
% 7.55/1.48      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_1041,c_1048]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_8,plain,
% 7.55/1.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.55/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1047,plain,
% 7.55/1.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_6449,plain,
% 7.55/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.55/1.48      | v1_funct_1(X0) != iProver_top
% 7.55/1.48      | v1_relat_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 7.55/1.48      inference(forward_subsumption_resolution,
% 7.55/1.48                [status(thm)],
% 7.55/1.48                [c_2585,c_1047]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_21805,plain,
% 7.55/1.48      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.55/1.48      | r1_tarski(sK0,sK3) != iProver_top
% 7.55/1.48      | v1_funct_1(sK2) != iProver_top
% 7.55/1.48      | v1_relat_1(k2_partfun1(X0,sK1,sK2,X1)) = iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_21750,c_6449]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_2,plain,
% 7.55/1.48      ( r1_tarski(X0,X0) ),
% 7.55/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1050,plain,
% 7.55/1.48      ( r1_tarski(X0,X0) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_11,plain,
% 7.55/1.48      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.55/1.48      | ~ v1_relat_1(X1)
% 7.55/1.48      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 7.55/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1045,plain,
% 7.55/1.48      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 7.55/1.48      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.55/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_2739,plain,
% 7.55/1.48      ( k1_relat_1(k7_relat_1(X0,k1_relat_1(X0))) = k1_relat_1(X0)
% 7.55/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_1050,c_1045]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_22512,plain,
% 7.55/1.48      ( k1_relat_1(k7_relat_1(k2_partfun1(X0,sK1,sK2,X1),k1_relat_1(k2_partfun1(X0,sK1,sK2,X1)))) = k1_relat_1(k2_partfun1(X0,sK1,sK2,X1))
% 7.55/1.48      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.55/1.48      | r1_tarski(sK0,sK3) != iProver_top
% 7.55/1.48      | v1_funct_1(sK2) != iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_21805,c_2739]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_34,plain,
% 7.55/1.48      ( r1_tarski(sK2,sK0) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_26,negated_conjecture,
% 7.55/1.48      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 7.55/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_6,plain,
% 7.55/1.48      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.55/1.48      | k1_xboole_0 = X1
% 7.55/1.48      | k1_xboole_0 = X0 ),
% 7.55/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_84,plain,
% 7.55/1.48      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.55/1.48      | k1_xboole_0 = k1_xboole_0 ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_5,plain,
% 7.55/1.48      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.55/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_85,plain,
% 7.55/1.48      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_5]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_631,plain,( X0 = X0 ),theory(equality) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1395,plain,
% 7.55/1.48      ( sK3 = sK3 ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_631]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_3,plain,
% 7.55/1.48      ( r1_tarski(k1_xboole_0,X0) ),
% 7.55/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1494,plain,
% 7.55/1.48      ( r1_tarski(k1_xboole_0,sK3) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1497,plain,
% 7.55/1.48      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_1494]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_632,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1289,plain,
% 7.55/1.48      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_632]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1516,plain,
% 7.55/1.48      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_1289]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1517,plain,
% 7.55/1.48      ( sK0 = sK0 ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_631]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_2180,plain,
% 7.55/1.48      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_632]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_2181,plain,
% 7.55/1.48      ( sK1 != k1_xboole_0
% 7.55/1.48      | k1_xboole_0 = sK1
% 7.55/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_2180]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_633,plain,
% 7.55/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.55/1.48      theory(equality) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1499,plain,
% 7.55/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK3) | X2 != X0 | sK3 != X1 ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_633]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_5240,plain,
% 7.55/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(sK0,sK3) | sK3 != X1 | sK0 != X0 ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_1499]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_7398,plain,
% 7.55/1.48      ( ~ r1_tarski(X0,sK3)
% 7.55/1.48      | r1_tarski(sK0,sK3)
% 7.55/1.48      | sK3 != sK3
% 7.55/1.48      | sK0 != X0 ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_5240]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_7399,plain,
% 7.55/1.48      ( sK3 != sK3
% 7.55/1.48      | sK0 != X0
% 7.55/1.48      | r1_tarski(X0,sK3) != iProver_top
% 7.55/1.48      | r1_tarski(sK0,sK3) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_7398]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_7401,plain,
% 7.55/1.48      ( sK3 != sK3
% 7.55/1.48      | sK0 != k1_xboole_0
% 7.55/1.48      | r1_tarski(sK0,sK3) = iProver_top
% 7.55/1.48      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_7399]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_2432,plain,
% 7.55/1.48      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.55/1.48      | v1_relat_1(sK3) = iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_1037,c_1048]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_33,plain,
% 7.55/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1310,plain,
% 7.55/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.55/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
% 7.55/1.48      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_14]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1649,plain,
% 7.55/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
% 7.55/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.55/1.48      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_1310]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1650,plain,
% 7.55/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top
% 7.55/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.55/1.48      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_1649]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1256,plain,
% 7.55/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.55/1.48      | v1_relat_1(X0)
% 7.55/1.48      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_7]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1728,plain,
% 7.55/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
% 7.55/1.48      | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))
% 7.55/1.48      | v1_relat_1(sK3) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_1256]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1737,plain,
% 7.55/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) != iProver_top
% 7.55/1.48      | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) != iProver_top
% 7.55/1.48      | v1_relat_1(sK3) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_1728]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1876,plain,
% 7.55/1.48      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1877,plain,
% 7.55/1.48      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_1876]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1311,plain,
% 7.55/1.48      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1881,plain,
% 7.55/1.48      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_1311]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1882,plain,
% 7.55/1.48      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_1881]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_2435,plain,
% 7.55/1.48      ( v1_relat_1(sK3) = iProver_top ),
% 7.55/1.48      inference(global_propositional_subsumption,
% 7.55/1.48                [status(thm)],
% 7.55/1.48                [c_2432,c_33,c_1650,c_1737,c_1877,c_1882]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_12,plain,
% 7.55/1.48      ( v4_relat_1(X0,X1)
% 7.55/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.55/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_10,plain,
% 7.55/1.48      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.55/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_294,plain,
% 7.55/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.55/1.48      | ~ v1_relat_1(X0)
% 7.55/1.48      | k7_relat_1(X0,X1) = X0 ),
% 7.55/1.48      inference(resolution,[status(thm)],[c_12,c_10]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1035,plain,
% 7.55/1.48      ( k7_relat_1(X0,X1) = X0
% 7.55/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.55/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1470,plain,
% 7.55/1.48      ( k7_relat_1(sK3,sK0) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_1037,c_1035]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_2440,plain,
% 7.55/1.48      ( k7_relat_1(sK3,sK0) = sK3 ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_2435,c_1470]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_9,plain,
% 7.55/1.48      ( ~ r1_tarski(X0,X1)
% 7.55/1.48      | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
% 7.55/1.48      | ~ v1_relat_1(X2) ),
% 7.55/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1046,plain,
% 7.55/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.55/1.48      | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = iProver_top
% 7.55/1.48      | v1_relat_1(X2) != iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_3021,plain,
% 7.55/1.48      ( r1_tarski(X0,sK0) != iProver_top
% 7.55/1.48      | r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
% 7.55/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_2440,c_1046]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_3444,plain,
% 7.55/1.48      ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
% 7.55/1.48      | r1_tarski(X0,sK0) != iProver_top ),
% 7.55/1.48      inference(global_propositional_subsumption,
% 7.55/1.48                [status(thm)],
% 7.55/1.48                [c_3021,c_33,c_1650,c_1737,c_1877,c_1882]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_3445,plain,
% 7.55/1.48      ( r1_tarski(X0,sK0) != iProver_top
% 7.55/1.48      | r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top ),
% 7.55/1.48      inference(renaming,[status(thm)],[c_3444]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_2741,plain,
% 7.55/1.48      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.55/1.48      | sK1 = k1_xboole_0
% 7.55/1.48      | r1_tarski(X0,sK0) != iProver_top
% 7.55/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_2203,c_1045]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_3041,plain,
% 7.55/1.48      ( r1_tarski(X0,sK0) != iProver_top
% 7.55/1.48      | sK1 = k1_xboole_0
% 7.55/1.48      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 7.55/1.48      inference(global_propositional_subsumption,
% 7.55/1.48                [status(thm)],
% 7.55/1.48                [c_2741,c_33,c_1650,c_1737,c_1877,c_1882]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_3042,plain,
% 7.55/1.48      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.55/1.48      | sK1 = k1_xboole_0
% 7.55/1.48      | r1_tarski(X0,sK0) != iProver_top ),
% 7.55/1.48      inference(renaming,[status(thm)],[c_3041]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_3052,plain,
% 7.55/1.48      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_1038,c_3042]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_3614,plain,
% 7.55/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 7.55/1.48      | r1_tarski(X0,sK3) != iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_1037,c_1042]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_4662,plain,
% 7.55/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 7.55/1.48      | r1_tarski(X0,sK3) != iProver_top
% 7.55/1.48      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_3614,c_1043]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_8243,plain,
% 7.55/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 7.55/1.48      | r1_tarski(X0,X2) != iProver_top
% 7.55/1.48      | r1_tarski(X2,sK3) != iProver_top
% 7.55/1.48      | r1_tarski(k1_relat_1(X2),X1) != iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_4662,c_1042]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_19671,plain,
% 7.55/1.48      ( sK1 = k1_xboole_0
% 7.55/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 7.55/1.48      | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
% 7.55/1.48      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 7.55/1.49      | r1_tarski(sK2,X1) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_3052,c_8243]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_24,plain,
% 7.55/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.55/1.49      | ~ v1_funct_1(X0)
% 7.55/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.55/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1039,plain,
% 7.55/1.49      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.55/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.55/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5307,plain,
% 7.55/1.49      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 7.55/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1037,c_1039]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_30,negated_conjecture,
% 7.55/1.49      ( v1_funct_1(sK3) ),
% 7.55/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1352,plain,
% 7.55/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.55/1.49      | ~ v1_funct_1(sK3)
% 7.55/1.49      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_24]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_4071,plain,
% 7.55/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.55/1.49      | ~ v1_funct_1(sK3)
% 7.55/1.49      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_1352]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5559,plain,
% 7.55/1.49      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.55/1.49      inference(global_propositional_subsumption,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_5307,c_30,c_28,c_4071]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5615,plain,
% 7.55/1.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 7.55/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.55/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_5559,c_1041]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_31,plain,
% 7.55/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_8967,plain,
% 7.55/1.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.55/1.49      inference(global_propositional_subsumption,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_5615,c_31,c_33]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_8980,plain,
% 7.55/1.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 7.55/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_8967,c_1043]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_13127,plain,
% 7.55/1.49      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X1)) = k1_relat_1(k7_relat_1(sK3,X1))
% 7.55/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X0) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_8980,c_1044]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_33189,plain,
% 7.55/1.49      ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1050,c_13127]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_33588,plain,
% 7.55/1.49      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 7.55/1.49      | sK1 = k1_xboole_0 ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_3052,c_33189]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_19,plain,
% 7.55/1.49      ( v1_funct_2(X0,X1,X2)
% 7.55/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.55/1.49      | k1_relset_1(X1,X2,X0) != X1
% 7.55/1.49      | k1_xboole_0 = X2 ),
% 7.55/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_25,negated_conjecture,
% 7.55/1.49      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 7.55/1.49      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.55/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 7.55/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_398,plain,
% 7.55/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.55/1.49      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.55/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.55/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 7.55/1.49      | k1_relset_1(X1,X2,X0) != X1
% 7.55/1.49      | sK2 != X1
% 7.55/1.49      | sK1 != X2
% 7.55/1.49      | k1_xboole_0 = X2 ),
% 7.55/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_399,plain,
% 7.55/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.55/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.55/1.49      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 7.55/1.49      | k1_xboole_0 = sK1 ),
% 7.55/1.49      inference(unflattening,[status(thm)],[c_398]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1030,plain,
% 7.55/1.49      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 7.55/1.49      | k1_xboole_0 = sK1
% 7.55/1.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.55/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5566,plain,
% 7.55/1.49      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 7.55/1.49      | sK1 = k1_xboole_0
% 7.55/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.55/1.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_5559,c_1030]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_23,plain,
% 7.55/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.55/1.49      | ~ v1_funct_1(X0)
% 7.55/1.49      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 7.55/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1040,plain,
% 7.55/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.55/1.49      | v1_funct_1(X0) != iProver_top
% 7.55/1.49      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1955,plain,
% 7.55/1.49      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 7.55/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1037,c_1040]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1332,plain,
% 7.55/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.55/1.49      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 7.55/1.49      | ~ v1_funct_1(sK3) ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_23]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1568,plain,
% 7.55/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.55/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 7.55/1.49      | ~ v1_funct_1(sK3) ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_1332]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1569,plain,
% 7.55/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.55/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 7.55/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_1568]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2243,plain,
% 7.55/1.49      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 7.55/1.49      inference(global_propositional_subsumption,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_1955,c_31,c_33,c_1569]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5567,plain,
% 7.55/1.49      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_5559,c_2243]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5574,plain,
% 7.55/1.49      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 7.55/1.49      | sK1 = k1_xboole_0
% 7.55/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.55/1.49      inference(forward_subsumption_resolution,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_5566,c_5567]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_0,plain,
% 7.55/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.55/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1273,plain,
% 7.55/1.49      ( ~ r1_tarski(sK2,k1_xboole_0)
% 7.55/1.49      | ~ r1_tarski(k1_xboole_0,sK2)
% 7.55/1.49      | sK2 = k1_xboole_0 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1290,plain,
% 7.55/1.49      ( sK2 != X0 | sK2 = sK0 | sK0 != X0 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_632]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1291,plain,
% 7.55/1.49      ( sK2 = sK0 | sK2 != k1_xboole_0 | sK0 != k1_xboole_0 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_1290]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1511,plain,
% 7.55/1.49      ( sK2 = sK2 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_631]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1616,plain,
% 7.55/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(sK0,sK2) | sK2 != X1 | sK0 != X0 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_633]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2657,plain,
% 7.55/1.49      ( ~ r1_tarski(X0,sK2)
% 7.55/1.49      | r1_tarski(sK0,sK2)
% 7.55/1.49      | sK2 != sK2
% 7.55/1.49      | sK0 != X0 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_1616]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2659,plain,
% 7.55/1.49      ( r1_tarski(sK0,sK2)
% 7.55/1.49      | ~ r1_tarski(k1_xboole_0,sK2)
% 7.55/1.49      | sK2 != sK2
% 7.55/1.49      | sK0 != k1_xboole_0 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_2657]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1441,plain,
% 7.55/1.49      ( ~ r1_tarski(X0,X1)
% 7.55/1.49      | r1_tarski(sK2,k1_xboole_0)
% 7.55/1.49      | sK2 != X0
% 7.55/1.49      | k1_xboole_0 != X1 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_633]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2216,plain,
% 7.55/1.49      ( ~ r1_tarski(sK2,X0)
% 7.55/1.49      | r1_tarski(sK2,k1_xboole_0)
% 7.55/1.49      | sK2 != sK2
% 7.55/1.49      | k1_xboole_0 != X0 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_1441]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5140,plain,
% 7.55/1.49      ( ~ r1_tarski(sK2,sK0)
% 7.55/1.49      | r1_tarski(sK2,k1_xboole_0)
% 7.55/1.49      | sK2 != sK2
% 7.55/1.49      | k1_xboole_0 != sK0 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_2216]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5467,plain,
% 7.55/1.49      ( r1_tarski(k1_xboole_0,sK2) ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_425,plain,
% 7.55/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.55/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.55/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 7.55/1.49      | sK2 != sK0
% 7.55/1.49      | sK1 != sK1 ),
% 7.55/1.49      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_501,plain,
% 7.55/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.55/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.55/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 7.55/1.49      | sK2 != sK0 ),
% 7.55/1.49      inference(equality_resolution_simp,[status(thm)],[c_425]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1029,plain,
% 7.55/1.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 7.55/1.49      | sK2 != sK0
% 7.55/1.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.55/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5565,plain,
% 7.55/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.55/1.49      | sK2 != sK0
% 7.55/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.55/1.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_5559,c_1029]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5582,plain,
% 7.55/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.55/1.49      | sK2 != sK0
% 7.55/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.55/1.49      inference(forward_subsumption_resolution,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_5565,c_5567]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_3020,plain,
% 7.55/1.49      ( r1_tarski(sK3,k7_relat_1(sK3,X0)) = iProver_top
% 7.55/1.49      | r1_tarski(sK0,X0) != iProver_top
% 7.55/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_2440,c_1046]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_3422,plain,
% 7.55/1.49      ( r1_tarski(sK0,X0) != iProver_top
% 7.55/1.49      | r1_tarski(sK3,k7_relat_1(sK3,X0)) = iProver_top ),
% 7.55/1.49      inference(global_propositional_subsumption,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_3020,c_33,c_1650,c_1737,c_1877,c_1882]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_3423,plain,
% 7.55/1.49      ( r1_tarski(sK3,k7_relat_1(sK3,X0)) = iProver_top
% 7.55/1.49      | r1_tarski(sK0,X0) != iProver_top ),
% 7.55/1.49      inference(renaming,[status(thm)],[c_3422]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1051,plain,
% 7.55/1.49      ( X0 = X1
% 7.55/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.55/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_3431,plain,
% 7.55/1.49      ( k7_relat_1(sK3,X0) = sK3
% 7.55/1.49      | r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top
% 7.55/1.49      | r1_tarski(sK0,X0) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_3423,c_1051]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_3547,plain,
% 7.55/1.49      ( k7_relat_1(sK3,X0) = sK3
% 7.55/1.49      | r1_tarski(X0,sK0) != iProver_top
% 7.55/1.49      | r1_tarski(sK0,X0) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_3445,c_3431]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_13522,plain,
% 7.55/1.49      ( k7_relat_1(sK3,sK2) = sK3 | r1_tarski(sK0,sK2) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1038,c_3547]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_13532,plain,
% 7.55/1.49      ( ~ r1_tarski(sK0,sK2) | k7_relat_1(sK3,sK2) = sK3 ),
% 7.55/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_13522]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_15915,plain,
% 7.55/1.49      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 7.55/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.55/1.49      inference(global_propositional_subsumption,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_5574,c_27,c_26,c_84,c_85,c_1273,c_1291,c_1511,c_1516,
% 7.55/1.49                 c_1517,c_2181,c_2659,c_5140,c_5467,c_5582,c_13532]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_34071,plain,
% 7.55/1.49      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 7.55/1.49      | sK1 = k1_xboole_0
% 7.55/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_33588,c_15915]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_16,plain,
% 7.55/1.49      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 7.55/1.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.55/1.49      | k1_xboole_0 = X0 ),
% 7.55/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_320,plain,
% 7.55/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.55/1.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.55/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.55/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.55/1.49      | sK2 != X0
% 7.55/1.49      | sK1 != k1_xboole_0
% 7.55/1.49      | k1_xboole_0 = X0 ),
% 7.55/1.49      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_321,plain,
% 7.55/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.55/1.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 7.55/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.55/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.55/1.49      | sK1 != k1_xboole_0
% 7.55/1.49      | k1_xboole_0 = sK2 ),
% 7.55/1.49      inference(unflattening,[status(thm)],[c_320]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1034,plain,
% 7.55/1.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.55/1.49      | sK1 != k1_xboole_0
% 7.55/1.49      | k1_xboole_0 = sK2
% 7.55/1.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.55/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 7.55/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_321]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_4,plain,
% 7.55/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.55/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1178,plain,
% 7.55/1.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.55/1.49      | sK2 = k1_xboole_0
% 7.55/1.49      | sK1 != k1_xboole_0
% 7.55/1.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.55/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.55/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_1034,c_4]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5564,plain,
% 7.55/1.49      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 7.55/1.49      | sK2 = k1_xboole_0
% 7.55/1.49      | sK1 != k1_xboole_0
% 7.55/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.55/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.55/1.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_5559,c_1178]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5592,plain,
% 7.55/1.49      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 7.55/1.49      | sK2 = k1_xboole_0
% 7.55/1.49      | sK1 != k1_xboole_0
% 7.55/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.55/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.55/1.49      inference(forward_subsumption_resolution,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_5564,c_5567]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_28271,plain,
% 7.55/1.49      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.55/1.49      | sK1 != k1_xboole_0 ),
% 7.55/1.49      inference(global_propositional_subsumption,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_5592,c_27,c_26,c_84,c_85,c_1273,c_1291,c_1511,c_1516,
% 7.55/1.49                 c_1517,c_2181,c_2659,c_5140,c_5467,c_5582,c_13532]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_28272,plain,
% 7.55/1.49      ( sK1 != k1_xboole_0
% 7.55/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.55/1.49      inference(renaming,[status(thm)],[c_28271]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_34342,plain,
% 7.55/1.49      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.55/1.49      inference(global_propositional_subsumption,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_34071,c_3052,c_28272]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_34350,plain,
% 7.55/1.49      ( sK1 = k1_xboole_0
% 7.55/1.49      | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
% 7.55/1.49      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 7.55/1.49      | r1_tarski(sK2,sK2) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_19671,c_34342]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5135,plain,
% 7.55/1.49      ( r1_tarski(sK2,sK2) ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5138,plain,
% 7.55/1.49      ( r1_tarski(sK2,sK2) = iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_5135]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_36688,plain,
% 7.55/1.49      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 7.55/1.49      | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
% 7.55/1.49      | sK1 = k1_xboole_0 ),
% 7.55/1.49      inference(global_propositional_subsumption,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_34350,c_5138]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_36689,plain,
% 7.55/1.49      ( sK1 = k1_xboole_0
% 7.55/1.49      | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
% 7.55/1.49      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top ),
% 7.55/1.49      inference(renaming,[status(thm)],[c_36688]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_36695,plain,
% 7.55/1.49      ( sK1 = k1_xboole_0
% 7.55/1.49      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top ),
% 7.55/1.49      inference(forward_subsumption_resolution,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_36689,c_1050]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_36698,plain,
% 7.55/1.49      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK0) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_3445,c_36695]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38519,plain,
% 7.55/1.49      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.55/1.49      | k1_relat_1(k7_relat_1(k2_partfun1(X0,sK1,sK2,X1),k1_relat_1(k2_partfun1(X0,sK1,sK2,X1)))) = k1_relat_1(k2_partfun1(X0,sK1,sK2,X1))
% 7.55/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.55/1.49      inference(global_propositional_subsumption,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_22512,c_34,c_26,c_84,c_85,c_1395,c_1497,c_1516,c_1517,
% 7.55/1.49                 c_2181,c_7401,c_36698]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38520,plain,
% 7.55/1.49      ( k1_relat_1(k7_relat_1(k2_partfun1(X0,sK1,sK2,X1),k1_relat_1(k2_partfun1(X0,sK1,sK2,X1)))) = k1_relat_1(k2_partfun1(X0,sK1,sK2,X1))
% 7.55/1.49      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.55/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.55/1.49      inference(renaming,[status(thm)],[c_38519]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38529,plain,
% 7.55/1.49      ( k1_relat_1(k7_relat_1(k2_partfun1(X0,sK1,sK2,X1),k1_relat_1(k2_partfun1(X0,sK1,sK2,X1)))) = k1_relat_1(k2_partfun1(X0,sK1,sK2,X1))
% 7.55/1.49      | sK1 = k1_xboole_0
% 7.55/1.49      | r1_tarski(sK0,X0) != iProver_top
% 7.55/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_2203,c_38520]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38549,plain,
% 7.55/1.49      ( sK1 = k1_xboole_0 ),
% 7.55/1.49      inference(global_propositional_subsumption,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_38529,c_34,c_36698]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38667,plain,
% 7.55/1.49      ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_38549,c_1934]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38672,plain,
% 7.55/1.49      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_38549,c_26]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38673,plain,
% 7.55/1.49      ( sK0 = k1_xboole_0 ),
% 7.55/1.49      inference(equality_resolution_simp,[status(thm)],[c_38672]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_20,plain,
% 7.55/1.49      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.55/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.55/1.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.55/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_385,plain,
% 7.55/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.55/1.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 7.55/1.49      | sK3 != X0
% 7.55/1.49      | sK1 != X1
% 7.55/1.49      | sK0 != k1_xboole_0 ),
% 7.55/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_386,plain,
% 7.55/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 7.55/1.49      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 7.55/1.49      | sK0 != k1_xboole_0 ),
% 7.55/1.49      inference(unflattening,[status(thm)],[c_385]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1031,plain,
% 7.55/1.49      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 7.55/1.49      | sK0 != k1_xboole_0
% 7.55/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1104,plain,
% 7.55/1.49      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 7.55/1.49      | sK0 != k1_xboole_0
% 7.55/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_1031,c_5]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38669,plain,
% 7.55/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.55/1.49      | sK0 != k1_xboole_0
% 7.55/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_38549,c_1104]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38680,plain,
% 7.55/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.55/1.49      | k1_xboole_0 != k1_xboole_0
% 7.55/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.55/1.49      inference(light_normalisation,[status(thm)],[c_38669,c_38673]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38681,plain,
% 7.55/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.55/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.55/1.49      inference(equality_resolution_simp,[status(thm)],[c_38680]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38671,plain,
% 7.55/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_38549,c_1037]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38676,plain,
% 7.55/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.55/1.49      inference(light_normalisation,[status(thm)],[c_38671,c_38673]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38678,plain,
% 7.55/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_38676,c_5]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38684,plain,
% 7.55/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 7.55/1.49      inference(forward_subsumption_resolution,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_38681,c_38678]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38687,plain,
% 7.55/1.49      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 7.55/1.49      inference(light_normalisation,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_38667,c_38673,c_38684]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_34353,plain,
% 7.55/1.49      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 7.55/1.49      | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_5634,c_34342]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_34398,plain,
% 7.55/1.49      ( r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
% 7.55/1.49      | r1_tarski(sK2,sK0) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_3445,c_34353]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_34408,plain,
% 7.55/1.49      ( ~ r1_tarski(k1_relat_1(sK3),sK2) | ~ r1_tarski(sK2,sK0) ),
% 7.55/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_34398]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1337,plain,
% 7.55/1.49      ( ~ r1_tarski(X0,X1)
% 7.55/1.49      | r1_tarski(k1_relat_1(X2),X3)
% 7.55/1.49      | X3 != X1
% 7.55/1.49      | k1_relat_1(X2) != X0 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_633]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_28223,plain,
% 7.55/1.49      ( ~ r1_tarski(X0,X1)
% 7.55/1.49      | r1_tarski(k1_relat_1(sK3),sK2)
% 7.55/1.49      | k1_relat_1(sK3) != X0
% 7.55/1.49      | sK2 != X1 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_1337]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_28225,plain,
% 7.55/1.49      ( r1_tarski(k1_relat_1(sK3),sK2)
% 7.55/1.49      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.55/1.49      | k1_relat_1(sK3) != k1_xboole_0
% 7.55/1.49      | sK2 != k1_xboole_0 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_28223]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_87,plain,
% 7.55/1.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(contradiction,plain,
% 7.55/1.49      ( $false ),
% 7.55/1.49      inference(minisat,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_38687,c_36698,c_34408,c_28225,c_5467,c_5140,c_2181,
% 7.55/1.49                 c_1511,c_1273,c_87,c_85,c_84,c_26,c_34,c_27]) ).
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.55/1.49  
% 7.55/1.49  ------                               Statistics
% 7.55/1.49  
% 7.55/1.49  ------ General
% 7.55/1.49  
% 7.55/1.49  abstr_ref_over_cycles:                  0
% 7.55/1.49  abstr_ref_under_cycles:                 0
% 7.55/1.49  gc_basic_clause_elim:                   0
% 7.55/1.49  forced_gc_time:                         0
% 7.55/1.49  parsing_time:                           0.013
% 7.55/1.49  unif_index_cands_time:                  0.
% 7.55/1.49  unif_index_add_time:                    0.
% 7.55/1.49  orderings_time:                         0.
% 7.55/1.49  out_proof_time:                         0.029
% 7.55/1.49  total_time:                             0.99
% 7.55/1.49  num_of_symbols:                         48
% 7.55/1.49  num_of_terms:                           34956
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing
% 7.55/1.49  
% 7.55/1.49  num_of_splits:                          0
% 7.55/1.49  num_of_split_atoms:                     0
% 7.55/1.49  num_of_reused_defs:                     0
% 7.55/1.49  num_eq_ax_congr_red:                    10
% 7.55/1.49  num_of_sem_filtered_clauses:            1
% 7.55/1.49  num_of_subtypes:                        0
% 7.55/1.49  monotx_restored_types:                  0
% 7.55/1.49  sat_num_of_epr_types:                   0
% 7.55/1.49  sat_num_of_non_cyclic_types:            0
% 7.55/1.49  sat_guarded_non_collapsed_types:        0
% 7.55/1.49  num_pure_diseq_elim:                    0
% 7.55/1.49  simp_replaced_by:                       0
% 7.55/1.49  res_preprocessed:                       137
% 7.55/1.49  prep_upred:                             0
% 7.55/1.49  prep_unflattend:                        33
% 7.55/1.49  smt_new_axioms:                         0
% 7.55/1.49  pred_elim_cands:                        4
% 7.55/1.49  pred_elim:                              2
% 7.55/1.49  pred_elim_cl:                           2
% 7.55/1.49  pred_elim_cycles:                       4
% 7.55/1.49  merged_defs:                            0
% 7.55/1.49  merged_defs_ncl:                        0
% 7.55/1.49  bin_hyper_res:                          0
% 7.55/1.49  prep_cycles:                            4
% 7.55/1.49  pred_elim_time:                         0.007
% 7.55/1.49  splitting_time:                         0.
% 7.55/1.49  sem_filter_time:                        0.
% 7.55/1.49  monotx_time:                            0.
% 7.55/1.49  subtype_inf_time:                       0.
% 7.55/1.49  
% 7.55/1.49  ------ Problem properties
% 7.55/1.49  
% 7.55/1.49  clauses:                                28
% 7.55/1.49  conjectures:                            4
% 7.55/1.49  epr:                                    6
% 7.55/1.49  horn:                                   25
% 7.55/1.49  ground:                                 11
% 7.55/1.49  unary:                                  8
% 7.55/1.49  binary:                                 3
% 7.55/1.49  lits:                                   73
% 7.55/1.49  lits_eq:                                28
% 7.55/1.49  fd_pure:                                0
% 7.55/1.49  fd_pseudo:                              0
% 7.55/1.49  fd_cond:                                1
% 7.55/1.49  fd_pseudo_cond:                         1
% 7.55/1.49  ac_symbols:                             0
% 7.55/1.49  
% 7.55/1.49  ------ Propositional Solver
% 7.55/1.49  
% 7.55/1.49  prop_solver_calls:                      31
% 7.55/1.49  prop_fast_solver_calls:                 1810
% 7.55/1.49  smt_solver_calls:                       0
% 7.55/1.49  smt_fast_solver_calls:                  0
% 7.55/1.49  prop_num_of_clauses:                    14882
% 7.55/1.49  prop_preprocess_simplified:             27810
% 7.55/1.49  prop_fo_subsumed:                       79
% 7.55/1.49  prop_solver_time:                       0.
% 7.55/1.49  smt_solver_time:                        0.
% 7.55/1.49  smt_fast_solver_time:                   0.
% 7.55/1.49  prop_fast_solver_time:                  0.
% 7.55/1.49  prop_unsat_core_time:                   0.001
% 7.55/1.49  
% 7.55/1.49  ------ QBF
% 7.55/1.49  
% 7.55/1.49  qbf_q_res:                              0
% 7.55/1.49  qbf_num_tautologies:                    0
% 7.55/1.49  qbf_prep_cycles:                        0
% 7.55/1.49  
% 7.55/1.49  ------ BMC1
% 7.55/1.49  
% 7.55/1.49  bmc1_current_bound:                     -1
% 7.55/1.49  bmc1_last_solved_bound:                 -1
% 7.55/1.49  bmc1_unsat_core_size:                   -1
% 7.55/1.49  bmc1_unsat_core_parents_size:           -1
% 7.55/1.49  bmc1_merge_next_fun:                    0
% 7.55/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.55/1.49  
% 7.55/1.49  ------ Instantiation
% 7.55/1.49  
% 7.55/1.49  inst_num_of_clauses:                    4426
% 7.55/1.49  inst_num_in_passive:                    1410
% 7.55/1.49  inst_num_in_active:                     1368
% 7.55/1.49  inst_num_in_unprocessed:                1648
% 7.55/1.49  inst_num_of_loops:                      1510
% 7.55/1.49  inst_num_of_learning_restarts:          0
% 7.55/1.49  inst_num_moves_active_passive:          140
% 7.55/1.49  inst_lit_activity:                      0
% 7.55/1.49  inst_lit_activity_moves:                0
% 7.55/1.49  inst_num_tautologies:                   0
% 7.55/1.49  inst_num_prop_implied:                  0
% 7.55/1.49  inst_num_existing_simplified:           0
% 7.55/1.49  inst_num_eq_res_simplified:             0
% 7.55/1.49  inst_num_child_elim:                    0
% 7.55/1.49  inst_num_of_dismatching_blockings:      2917
% 7.55/1.49  inst_num_of_non_proper_insts:           4684
% 7.55/1.49  inst_num_of_duplicates:                 0
% 7.55/1.49  inst_inst_num_from_inst_to_res:         0
% 7.55/1.49  inst_dismatching_checking_time:         0.
% 7.55/1.49  
% 7.55/1.49  ------ Resolution
% 7.55/1.49  
% 7.55/1.49  res_num_of_clauses:                     0
% 7.55/1.49  res_num_in_passive:                     0
% 7.55/1.49  res_num_in_active:                      0
% 7.55/1.49  res_num_of_loops:                       141
% 7.55/1.49  res_forward_subset_subsumed:            166
% 7.55/1.49  res_backward_subset_subsumed:           4
% 7.55/1.49  res_forward_subsumed:                   0
% 7.55/1.49  res_backward_subsumed:                  0
% 7.55/1.49  res_forward_subsumption_resolution:     0
% 7.55/1.49  res_backward_subsumption_resolution:    0
% 7.55/1.49  res_clause_to_clause_subsumption:       3255
% 7.55/1.49  res_orphan_elimination:                 0
% 7.55/1.49  res_tautology_del:                      345
% 7.55/1.49  res_num_eq_res_simplified:              1
% 7.55/1.49  res_num_sel_changes:                    0
% 7.55/1.49  res_moves_from_active_to_pass:          0
% 7.55/1.49  
% 7.55/1.49  ------ Superposition
% 7.55/1.49  
% 7.55/1.49  sup_time_total:                         0.
% 7.55/1.49  sup_time_generating:                    0.
% 7.55/1.49  sup_time_sim_full:                      0.
% 7.55/1.49  sup_time_sim_immed:                     0.
% 7.55/1.49  
% 7.55/1.49  sup_num_of_clauses:                     447
% 7.55/1.49  sup_num_in_active:                      155
% 7.55/1.49  sup_num_in_passive:                     292
% 7.55/1.49  sup_num_of_loops:                       301
% 7.55/1.49  sup_fw_superposition:                   525
% 7.55/1.49  sup_bw_superposition:                   414
% 7.55/1.49  sup_immediate_simplified:               340
% 7.55/1.49  sup_given_eliminated:                   0
% 7.55/1.49  comparisons_done:                       0
% 7.55/1.49  comparisons_avoided:                    78
% 7.55/1.49  
% 7.55/1.49  ------ Simplifications
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  sim_fw_subset_subsumed:                 96
% 7.55/1.49  sim_bw_subset_subsumed:                 57
% 7.55/1.49  sim_fw_subsumed:                        84
% 7.55/1.49  sim_bw_subsumed:                        10
% 7.55/1.49  sim_fw_subsumption_res:                 10
% 7.55/1.49  sim_bw_subsumption_res:                 0
% 7.55/1.49  sim_tautology_del:                      21
% 7.55/1.49  sim_eq_tautology_del:                   55
% 7.55/1.49  sim_eq_res_simp:                        4
% 7.55/1.49  sim_fw_demodulated:                     58
% 7.55/1.49  sim_bw_demodulated:                     133
% 7.55/1.49  sim_light_normalised:                   150
% 7.55/1.49  sim_joinable_taut:                      0
% 7.55/1.49  sim_joinable_simp:                      0
% 7.55/1.49  sim_ac_normalised:                      0
% 7.55/1.49  sim_smt_subsumption:                    0
% 7.55/1.49  
%------------------------------------------------------------------------------
