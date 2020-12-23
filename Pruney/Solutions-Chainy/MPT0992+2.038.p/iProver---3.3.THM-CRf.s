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
% DateTime   : Thu Dec  3 12:03:54 EST 2020

% Result     : Theorem 7.53s
% Output     : CNFRefutation 7.53s
% Verified   : 
% Statistics : Number of formulae       :  232 (6150 expanded)
%              Number of clauses        :  155 (2141 expanded)
%              Number of leaves         :   19 (1105 expanded)
%              Depth                    :   31
%              Number of atoms          :  691 (33160 expanded)
%              Number of equality atoms :  393 (10183 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f43,plain,
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

fof(f44,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f43])).

fof(f72,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f80,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f73,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_8,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1072,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1063,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_440,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_442,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_27])).

cnf(c_1062,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1069,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2244,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1062,c_1069])).

cnf(c_2296,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_442,c_2244])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1071,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2935,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2296,c_1071])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1269,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1270,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1269])).

cnf(c_3153,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2935,c_32,c_1270])).

cnf(c_3154,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3153])).

cnf(c_3165,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1063,c_3154])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1067,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3570,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1062,c_1067])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1068,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5361,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3570,c_1068])).

cnf(c_7195,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5361,c_1067])).

cnf(c_16576,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3165,c_7195])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1074,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7193,plain,
    ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
    | r1_tarski(X1,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5361,c_1069])).

cnf(c_12265,plain,
    ( k1_relset_1(k1_relat_1(X0),sK1,X0) = k1_relat_1(X0)
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1074,c_7193])).

cnf(c_16277,plain,
    ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0))
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_12265])).

cnf(c_30534,plain,
    ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16277,c_32,c_1270])).

cnf(c_30539,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3165,c_30534])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1064,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4103,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1062,c_1064])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1346,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1459,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1346])).

cnf(c_4409,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4103,c_29,c_27,c_1459])).

cnf(c_18,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_423,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_424,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_1055,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_4416,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4409,c_1055])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1065,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2022,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1062,c_1065])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1319,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1656,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1319])).

cnf(c_1657,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1656])).

cnf(c_2374,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2022,c_30,c_32,c_1657])).

cnf(c_4417,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4409,c_2374])).

cnf(c_4424,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4416,c_4417])).

cnf(c_31197,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_30539,c_4424])).

cnf(c_32861,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31197,c_3165])).

cnf(c_32870,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_16576,c_32861])).

cnf(c_9033,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_9036,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9033])).

cnf(c_33997,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32870,c_9036])).

cnf(c_33998,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_33997])).

cnf(c_34004,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_33998,c_1074])).

cnf(c_34006,plain,
    ( sK1 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_34004])).

cnf(c_34889,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_34006,c_32,c_1270])).

cnf(c_15,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_345,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_346,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_1059,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1194,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1059,c_4])).

cnf(c_4414,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4409,c_1194])).

cnf(c_4442,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4414,c_4417])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_82,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_83,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1284,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_679,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1558,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_680,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1841,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_1842,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1841])).

cnf(c_681,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1484,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_2536,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1484])).

cnf(c_9038,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2536])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_10367,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_23043,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4442,c_26,c_25,c_82,c_83,c_1284,c_1558,c_1842,c_9038,c_10367])).

cnf(c_34928,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_34889,c_23043])).

cnf(c_35533,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_34928])).

cnf(c_450,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_525,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_450])).

cnf(c_1054,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_4415,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4409,c_1054])).

cnf(c_4432,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4415,c_4417])).

cnf(c_34980,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_34889,c_4432])).

cnf(c_35036,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_34889,c_25])).

cnf(c_35037,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_35036])).

cnf(c_35251,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34980,c_35037])).

cnf(c_35255,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_35251,c_4])).

cnf(c_35555,plain,
    ( k7_relat_1(sK3,k1_xboole_0) != sK3
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_35533,c_35255])).

cnf(c_35569,plain,
    ( k7_relat_1(sK3,k1_xboole_0) != sK3
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_35555])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1066,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4465,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4409,c_1066])).

cnf(c_1356,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1357,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1356])).

cnf(c_1314,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1543,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r1_tarski(k7_relat_1(sK3,X0),sK3) ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_1544,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1543])).

cnf(c_8516,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4465,c_32,c_1270,c_1357,c_1544])).

cnf(c_35004,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_34889,c_8516])).

cnf(c_35182,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_35004,c_35037])).

cnf(c_35184,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_35182,c_5])).

cnf(c_35572,plain,
    ( k7_relat_1(sK3,k1_xboole_0) != sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_35569,c_35184])).

cnf(c_35031,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_34889,c_2244])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_411,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_1056,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_1132,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1056,c_5])).

cnf(c_35033,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_34889,c_1132])).

cnf(c_35044,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_35033,c_35037])).

cnf(c_35045,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_35044])).

cnf(c_35035,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_34889,c_1062])).

cnf(c_35040,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_35035,c_35037])).

cnf(c_35042,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_35040,c_5])).

cnf(c_35048,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_35045,c_35042])).

cnf(c_35051,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_35031,c_35037,c_35048])).

cnf(c_1331,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X2),X3)
    | X3 != X1
    | k1_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_11530,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK3),X2)
    | X2 != X1
    | k1_relat_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_11532,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11530])).

cnf(c_5360,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1062,c_1068])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_286,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_11,c_7])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_286,c_11,c_10,c_7])).

cnf(c_1060,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_5763,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5360,c_1060])).

cnf(c_5807,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0)
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5763])).

cnf(c_5809,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k7_relat_1(sK3,k1_xboole_0) = sK3 ),
    inference(instantiation,[status(thm)],[c_5807])).

cnf(c_85,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35572,c_35051,c_11532,c_5809,c_85,c_83,c_82])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.53/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.53/1.49  
% 7.53/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.53/1.49  
% 7.53/1.49  ------  iProver source info
% 7.53/1.49  
% 7.53/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.53/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.53/1.49  git: non_committed_changes: false
% 7.53/1.49  git: last_make_outside_of_git: false
% 7.53/1.49  
% 7.53/1.49  ------ 
% 7.53/1.49  
% 7.53/1.49  ------ Input Options
% 7.53/1.49  
% 7.53/1.49  --out_options                           all
% 7.53/1.49  --tptp_safe_out                         true
% 7.53/1.49  --problem_path                          ""
% 7.53/1.49  --include_path                          ""
% 7.53/1.49  --clausifier                            res/vclausify_rel
% 7.53/1.49  --clausifier_options                    --mode clausify
% 7.53/1.49  --stdin                                 false
% 7.53/1.49  --stats_out                             all
% 7.53/1.49  
% 7.53/1.49  ------ General Options
% 7.53/1.49  
% 7.53/1.49  --fof                                   false
% 7.53/1.49  --time_out_real                         305.
% 7.53/1.49  --time_out_virtual                      -1.
% 7.53/1.49  --symbol_type_check                     false
% 7.53/1.49  --clausify_out                          false
% 7.53/1.49  --sig_cnt_out                           false
% 7.53/1.49  --trig_cnt_out                          false
% 7.53/1.49  --trig_cnt_out_tolerance                1.
% 7.53/1.49  --trig_cnt_out_sk_spl                   false
% 7.53/1.49  --abstr_cl_out                          false
% 7.53/1.49  
% 7.53/1.49  ------ Global Options
% 7.53/1.49  
% 7.53/1.49  --schedule                              default
% 7.53/1.49  --add_important_lit                     false
% 7.53/1.49  --prop_solver_per_cl                    1000
% 7.53/1.49  --min_unsat_core                        false
% 7.53/1.49  --soft_assumptions                      false
% 7.53/1.49  --soft_lemma_size                       3
% 7.53/1.49  --prop_impl_unit_size                   0
% 7.53/1.49  --prop_impl_unit                        []
% 7.53/1.49  --share_sel_clauses                     true
% 7.53/1.49  --reset_solvers                         false
% 7.53/1.49  --bc_imp_inh                            [conj_cone]
% 7.53/1.49  --conj_cone_tolerance                   3.
% 7.53/1.49  --extra_neg_conj                        none
% 7.53/1.49  --large_theory_mode                     true
% 7.53/1.49  --prolific_symb_bound                   200
% 7.53/1.49  --lt_threshold                          2000
% 7.53/1.49  --clause_weak_htbl                      true
% 7.53/1.49  --gc_record_bc_elim                     false
% 7.53/1.49  
% 7.53/1.49  ------ Preprocessing Options
% 7.53/1.49  
% 7.53/1.49  --preprocessing_flag                    true
% 7.53/1.49  --time_out_prep_mult                    0.1
% 7.53/1.49  --splitting_mode                        input
% 7.53/1.49  --splitting_grd                         true
% 7.53/1.49  --splitting_cvd                         false
% 7.53/1.49  --splitting_cvd_svl                     false
% 7.53/1.49  --splitting_nvd                         32
% 7.53/1.49  --sub_typing                            true
% 7.53/1.49  --prep_gs_sim                           true
% 7.53/1.49  --prep_unflatten                        true
% 7.53/1.49  --prep_res_sim                          true
% 7.53/1.49  --prep_upred                            true
% 7.53/1.49  --prep_sem_filter                       exhaustive
% 7.53/1.49  --prep_sem_filter_out                   false
% 7.53/1.49  --pred_elim                             true
% 7.53/1.49  --res_sim_input                         true
% 7.53/1.49  --eq_ax_congr_red                       true
% 7.53/1.49  --pure_diseq_elim                       true
% 7.53/1.49  --brand_transform                       false
% 7.53/1.49  --non_eq_to_eq                          false
% 7.53/1.49  --prep_def_merge                        true
% 7.53/1.49  --prep_def_merge_prop_impl              false
% 7.53/1.49  --prep_def_merge_mbd                    true
% 7.53/1.49  --prep_def_merge_tr_red                 false
% 7.53/1.49  --prep_def_merge_tr_cl                  false
% 7.53/1.49  --smt_preprocessing                     true
% 7.53/1.49  --smt_ac_axioms                         fast
% 7.53/1.49  --preprocessed_out                      false
% 7.53/1.49  --preprocessed_stats                    false
% 7.53/1.49  
% 7.53/1.49  ------ Abstraction refinement Options
% 7.53/1.49  
% 7.53/1.49  --abstr_ref                             []
% 7.53/1.49  --abstr_ref_prep                        false
% 7.53/1.49  --abstr_ref_until_sat                   false
% 7.53/1.49  --abstr_ref_sig_restrict                funpre
% 7.53/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.53/1.49  --abstr_ref_under                       []
% 7.53/1.49  
% 7.53/1.49  ------ SAT Options
% 7.53/1.49  
% 7.53/1.49  --sat_mode                              false
% 7.53/1.49  --sat_fm_restart_options                ""
% 7.53/1.49  --sat_gr_def                            false
% 7.53/1.49  --sat_epr_types                         true
% 7.53/1.49  --sat_non_cyclic_types                  false
% 7.53/1.49  --sat_finite_models                     false
% 7.53/1.49  --sat_fm_lemmas                         false
% 7.53/1.49  --sat_fm_prep                           false
% 7.53/1.49  --sat_fm_uc_incr                        true
% 7.53/1.49  --sat_out_model                         small
% 7.53/1.49  --sat_out_clauses                       false
% 7.53/1.49  
% 7.53/1.49  ------ QBF Options
% 7.53/1.49  
% 7.53/1.49  --qbf_mode                              false
% 7.53/1.49  --qbf_elim_univ                         false
% 7.53/1.49  --qbf_dom_inst                          none
% 7.53/1.49  --qbf_dom_pre_inst                      false
% 7.53/1.49  --qbf_sk_in                             false
% 7.53/1.49  --qbf_pred_elim                         true
% 7.53/1.49  --qbf_split                             512
% 7.53/1.49  
% 7.53/1.49  ------ BMC1 Options
% 7.53/1.49  
% 7.53/1.49  --bmc1_incremental                      false
% 7.53/1.49  --bmc1_axioms                           reachable_all
% 7.53/1.49  --bmc1_min_bound                        0
% 7.53/1.49  --bmc1_max_bound                        -1
% 7.53/1.49  --bmc1_max_bound_default                -1
% 7.53/1.49  --bmc1_symbol_reachability              true
% 7.53/1.49  --bmc1_property_lemmas                  false
% 7.53/1.49  --bmc1_k_induction                      false
% 7.53/1.49  --bmc1_non_equiv_states                 false
% 7.53/1.49  --bmc1_deadlock                         false
% 7.53/1.49  --bmc1_ucm                              false
% 7.53/1.49  --bmc1_add_unsat_core                   none
% 7.53/1.49  --bmc1_unsat_core_children              false
% 7.53/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.53/1.49  --bmc1_out_stat                         full
% 7.53/1.49  --bmc1_ground_init                      false
% 7.53/1.49  --bmc1_pre_inst_next_state              false
% 7.53/1.49  --bmc1_pre_inst_state                   false
% 7.53/1.49  --bmc1_pre_inst_reach_state             false
% 7.53/1.49  --bmc1_out_unsat_core                   false
% 7.53/1.49  --bmc1_aig_witness_out                  false
% 7.53/1.49  --bmc1_verbose                          false
% 7.53/1.49  --bmc1_dump_clauses_tptp                false
% 7.53/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.53/1.49  --bmc1_dump_file                        -
% 7.53/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.53/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.53/1.49  --bmc1_ucm_extend_mode                  1
% 7.53/1.49  --bmc1_ucm_init_mode                    2
% 7.53/1.49  --bmc1_ucm_cone_mode                    none
% 7.53/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.53/1.49  --bmc1_ucm_relax_model                  4
% 7.53/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.53/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.53/1.49  --bmc1_ucm_layered_model                none
% 7.53/1.49  --bmc1_ucm_max_lemma_size               10
% 7.53/1.49  
% 7.53/1.49  ------ AIG Options
% 7.53/1.49  
% 7.53/1.49  --aig_mode                              false
% 7.53/1.49  
% 7.53/1.49  ------ Instantiation Options
% 7.53/1.49  
% 7.53/1.49  --instantiation_flag                    true
% 7.53/1.49  --inst_sos_flag                         false
% 7.53/1.49  --inst_sos_phase                        true
% 7.53/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.53/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.53/1.49  --inst_lit_sel_side                     num_symb
% 7.53/1.49  --inst_solver_per_active                1400
% 7.53/1.49  --inst_solver_calls_frac                1.
% 7.53/1.49  --inst_passive_queue_type               priority_queues
% 7.53/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.53/1.49  --inst_passive_queues_freq              [25;2]
% 7.53/1.49  --inst_dismatching                      true
% 7.53/1.49  --inst_eager_unprocessed_to_passive     true
% 7.53/1.49  --inst_prop_sim_given                   true
% 7.53/1.49  --inst_prop_sim_new                     false
% 7.53/1.49  --inst_subs_new                         false
% 7.53/1.49  --inst_eq_res_simp                      false
% 7.53/1.49  --inst_subs_given                       false
% 7.53/1.49  --inst_orphan_elimination               true
% 7.53/1.49  --inst_learning_loop_flag               true
% 7.53/1.49  --inst_learning_start                   3000
% 7.53/1.49  --inst_learning_factor                  2
% 7.53/1.49  --inst_start_prop_sim_after_learn       3
% 7.53/1.49  --inst_sel_renew                        solver
% 7.53/1.49  --inst_lit_activity_flag                true
% 7.53/1.49  --inst_restr_to_given                   false
% 7.53/1.49  --inst_activity_threshold               500
% 7.53/1.49  --inst_out_proof                        true
% 7.53/1.49  
% 7.53/1.49  ------ Resolution Options
% 7.53/1.49  
% 7.53/1.49  --resolution_flag                       true
% 7.53/1.49  --res_lit_sel                           adaptive
% 7.53/1.49  --res_lit_sel_side                      none
% 7.53/1.49  --res_ordering                          kbo
% 7.53/1.49  --res_to_prop_solver                    active
% 7.53/1.49  --res_prop_simpl_new                    false
% 7.53/1.49  --res_prop_simpl_given                  true
% 7.53/1.49  --res_passive_queue_type                priority_queues
% 7.53/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.53/1.49  --res_passive_queues_freq               [15;5]
% 7.53/1.49  --res_forward_subs                      full
% 7.53/1.49  --res_backward_subs                     full
% 7.53/1.49  --res_forward_subs_resolution           true
% 7.53/1.49  --res_backward_subs_resolution          true
% 7.53/1.49  --res_orphan_elimination                true
% 7.53/1.49  --res_time_limit                        2.
% 7.53/1.49  --res_out_proof                         true
% 7.53/1.49  
% 7.53/1.49  ------ Superposition Options
% 7.53/1.49  
% 7.53/1.49  --superposition_flag                    true
% 7.53/1.49  --sup_passive_queue_type                priority_queues
% 7.53/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.53/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.53/1.49  --demod_completeness_check              fast
% 7.53/1.49  --demod_use_ground                      true
% 7.53/1.49  --sup_to_prop_solver                    passive
% 7.53/1.49  --sup_prop_simpl_new                    true
% 7.53/1.49  --sup_prop_simpl_given                  true
% 7.53/1.49  --sup_fun_splitting                     false
% 7.53/1.49  --sup_smt_interval                      50000
% 7.53/1.49  
% 7.53/1.49  ------ Superposition Simplification Setup
% 7.53/1.49  
% 7.53/1.49  --sup_indices_passive                   []
% 7.53/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.53/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.49  --sup_full_bw                           [BwDemod]
% 7.53/1.49  --sup_immed_triv                        [TrivRules]
% 7.53/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.53/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.49  --sup_immed_bw_main                     []
% 7.53/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.53/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.53/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.53/1.49  
% 7.53/1.49  ------ Combination Options
% 7.53/1.49  
% 7.53/1.49  --comb_res_mult                         3
% 7.53/1.49  --comb_sup_mult                         2
% 7.53/1.49  --comb_inst_mult                        10
% 7.53/1.49  
% 7.53/1.49  ------ Debug Options
% 7.53/1.49  
% 7.53/1.49  --dbg_backtrace                         false
% 7.53/1.49  --dbg_dump_prop_clauses                 false
% 7.53/1.49  --dbg_dump_prop_clauses_file            -
% 7.53/1.49  --dbg_out_stat                          false
% 7.53/1.49  ------ Parsing...
% 7.53/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.53/1.49  
% 7.53/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.53/1.49  
% 7.53/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.53/1.49  
% 7.53/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.53/1.49  ------ Proving...
% 7.53/1.49  ------ Problem Properties 
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  clauses                                 27
% 7.53/1.49  conjectures                             4
% 7.53/1.49  EPR                                     6
% 7.53/1.49  Horn                                    24
% 7.53/1.49  unary                                   7
% 7.53/1.49  binary                                  6
% 7.53/1.49  lits                                    69
% 7.53/1.49  lits eq                                 28
% 7.53/1.49  fd_pure                                 0
% 7.53/1.49  fd_pseudo                               0
% 7.53/1.49  fd_cond                                 1
% 7.53/1.49  fd_pseudo_cond                          1
% 7.53/1.49  AC symbols                              0
% 7.53/1.49  
% 7.53/1.49  ------ Schedule dynamic 5 is on 
% 7.53/1.49  
% 7.53/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  ------ 
% 7.53/1.49  Current options:
% 7.53/1.49  ------ 
% 7.53/1.49  
% 7.53/1.49  ------ Input Options
% 7.53/1.49  
% 7.53/1.49  --out_options                           all
% 7.53/1.49  --tptp_safe_out                         true
% 7.53/1.49  --problem_path                          ""
% 7.53/1.49  --include_path                          ""
% 7.53/1.49  --clausifier                            res/vclausify_rel
% 7.53/1.49  --clausifier_options                    --mode clausify
% 7.53/1.49  --stdin                                 false
% 7.53/1.49  --stats_out                             all
% 7.53/1.49  
% 7.53/1.49  ------ General Options
% 7.53/1.49  
% 7.53/1.49  --fof                                   false
% 7.53/1.49  --time_out_real                         305.
% 7.53/1.49  --time_out_virtual                      -1.
% 7.53/1.49  --symbol_type_check                     false
% 7.53/1.49  --clausify_out                          false
% 7.53/1.49  --sig_cnt_out                           false
% 7.53/1.49  --trig_cnt_out                          false
% 7.53/1.49  --trig_cnt_out_tolerance                1.
% 7.53/1.49  --trig_cnt_out_sk_spl                   false
% 7.53/1.49  --abstr_cl_out                          false
% 7.53/1.49  
% 7.53/1.49  ------ Global Options
% 7.53/1.49  
% 7.53/1.49  --schedule                              default
% 7.53/1.49  --add_important_lit                     false
% 7.53/1.49  --prop_solver_per_cl                    1000
% 7.53/1.49  --min_unsat_core                        false
% 7.53/1.49  --soft_assumptions                      false
% 7.53/1.49  --soft_lemma_size                       3
% 7.53/1.49  --prop_impl_unit_size                   0
% 7.53/1.49  --prop_impl_unit                        []
% 7.53/1.49  --share_sel_clauses                     true
% 7.53/1.49  --reset_solvers                         false
% 7.53/1.49  --bc_imp_inh                            [conj_cone]
% 7.53/1.49  --conj_cone_tolerance                   3.
% 7.53/1.49  --extra_neg_conj                        none
% 7.53/1.49  --large_theory_mode                     true
% 7.53/1.49  --prolific_symb_bound                   200
% 7.53/1.49  --lt_threshold                          2000
% 7.53/1.49  --clause_weak_htbl                      true
% 7.53/1.49  --gc_record_bc_elim                     false
% 7.53/1.49  
% 7.53/1.49  ------ Preprocessing Options
% 7.53/1.49  
% 7.53/1.49  --preprocessing_flag                    true
% 7.53/1.49  --time_out_prep_mult                    0.1
% 7.53/1.49  --splitting_mode                        input
% 7.53/1.49  --splitting_grd                         true
% 7.53/1.49  --splitting_cvd                         false
% 7.53/1.49  --splitting_cvd_svl                     false
% 7.53/1.49  --splitting_nvd                         32
% 7.53/1.49  --sub_typing                            true
% 7.53/1.49  --prep_gs_sim                           true
% 7.53/1.49  --prep_unflatten                        true
% 7.53/1.49  --prep_res_sim                          true
% 7.53/1.49  --prep_upred                            true
% 7.53/1.49  --prep_sem_filter                       exhaustive
% 7.53/1.49  --prep_sem_filter_out                   false
% 7.53/1.49  --pred_elim                             true
% 7.53/1.49  --res_sim_input                         true
% 7.53/1.49  --eq_ax_congr_red                       true
% 7.53/1.49  --pure_diseq_elim                       true
% 7.53/1.49  --brand_transform                       false
% 7.53/1.49  --non_eq_to_eq                          false
% 7.53/1.49  --prep_def_merge                        true
% 7.53/1.49  --prep_def_merge_prop_impl              false
% 7.53/1.49  --prep_def_merge_mbd                    true
% 7.53/1.49  --prep_def_merge_tr_red                 false
% 7.53/1.49  --prep_def_merge_tr_cl                  false
% 7.53/1.49  --smt_preprocessing                     true
% 7.53/1.49  --smt_ac_axioms                         fast
% 7.53/1.49  --preprocessed_out                      false
% 7.53/1.49  --preprocessed_stats                    false
% 7.53/1.49  
% 7.53/1.49  ------ Abstraction refinement Options
% 7.53/1.49  
% 7.53/1.49  --abstr_ref                             []
% 7.53/1.49  --abstr_ref_prep                        false
% 7.53/1.49  --abstr_ref_until_sat                   false
% 7.53/1.49  --abstr_ref_sig_restrict                funpre
% 7.53/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.53/1.49  --abstr_ref_under                       []
% 7.53/1.49  
% 7.53/1.49  ------ SAT Options
% 7.53/1.49  
% 7.53/1.49  --sat_mode                              false
% 7.53/1.49  --sat_fm_restart_options                ""
% 7.53/1.49  --sat_gr_def                            false
% 7.53/1.49  --sat_epr_types                         true
% 7.53/1.49  --sat_non_cyclic_types                  false
% 7.53/1.49  --sat_finite_models                     false
% 7.53/1.49  --sat_fm_lemmas                         false
% 7.53/1.49  --sat_fm_prep                           false
% 7.53/1.49  --sat_fm_uc_incr                        true
% 7.53/1.49  --sat_out_model                         small
% 7.53/1.49  --sat_out_clauses                       false
% 7.53/1.49  
% 7.53/1.49  ------ QBF Options
% 7.53/1.49  
% 7.53/1.49  --qbf_mode                              false
% 7.53/1.49  --qbf_elim_univ                         false
% 7.53/1.49  --qbf_dom_inst                          none
% 7.53/1.49  --qbf_dom_pre_inst                      false
% 7.53/1.49  --qbf_sk_in                             false
% 7.53/1.49  --qbf_pred_elim                         true
% 7.53/1.49  --qbf_split                             512
% 7.53/1.49  
% 7.53/1.49  ------ BMC1 Options
% 7.53/1.49  
% 7.53/1.49  --bmc1_incremental                      false
% 7.53/1.49  --bmc1_axioms                           reachable_all
% 7.53/1.49  --bmc1_min_bound                        0
% 7.53/1.49  --bmc1_max_bound                        -1
% 7.53/1.49  --bmc1_max_bound_default                -1
% 7.53/1.49  --bmc1_symbol_reachability              true
% 7.53/1.49  --bmc1_property_lemmas                  false
% 7.53/1.49  --bmc1_k_induction                      false
% 7.53/1.49  --bmc1_non_equiv_states                 false
% 7.53/1.49  --bmc1_deadlock                         false
% 7.53/1.49  --bmc1_ucm                              false
% 7.53/1.49  --bmc1_add_unsat_core                   none
% 7.53/1.49  --bmc1_unsat_core_children              false
% 7.53/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.53/1.49  --bmc1_out_stat                         full
% 7.53/1.49  --bmc1_ground_init                      false
% 7.53/1.49  --bmc1_pre_inst_next_state              false
% 7.53/1.49  --bmc1_pre_inst_state                   false
% 7.53/1.49  --bmc1_pre_inst_reach_state             false
% 7.53/1.49  --bmc1_out_unsat_core                   false
% 7.53/1.49  --bmc1_aig_witness_out                  false
% 7.53/1.49  --bmc1_verbose                          false
% 7.53/1.49  --bmc1_dump_clauses_tptp                false
% 7.53/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.53/1.49  --bmc1_dump_file                        -
% 7.53/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.53/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.53/1.49  --bmc1_ucm_extend_mode                  1
% 7.53/1.49  --bmc1_ucm_init_mode                    2
% 7.53/1.49  --bmc1_ucm_cone_mode                    none
% 7.53/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.53/1.49  --bmc1_ucm_relax_model                  4
% 7.53/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.53/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.53/1.49  --bmc1_ucm_layered_model                none
% 7.53/1.49  --bmc1_ucm_max_lemma_size               10
% 7.53/1.49  
% 7.53/1.49  ------ AIG Options
% 7.53/1.49  
% 7.53/1.49  --aig_mode                              false
% 7.53/1.49  
% 7.53/1.49  ------ Instantiation Options
% 7.53/1.49  
% 7.53/1.49  --instantiation_flag                    true
% 7.53/1.49  --inst_sos_flag                         false
% 7.53/1.49  --inst_sos_phase                        true
% 7.53/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.53/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.53/1.49  --inst_lit_sel_side                     none
% 7.53/1.49  --inst_solver_per_active                1400
% 7.53/1.49  --inst_solver_calls_frac                1.
% 7.53/1.49  --inst_passive_queue_type               priority_queues
% 7.53/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.53/1.49  --inst_passive_queues_freq              [25;2]
% 7.53/1.49  --inst_dismatching                      true
% 7.53/1.49  --inst_eager_unprocessed_to_passive     true
% 7.53/1.49  --inst_prop_sim_given                   true
% 7.53/1.49  --inst_prop_sim_new                     false
% 7.53/1.49  --inst_subs_new                         false
% 7.53/1.49  --inst_eq_res_simp                      false
% 7.53/1.49  --inst_subs_given                       false
% 7.53/1.49  --inst_orphan_elimination               true
% 7.53/1.49  --inst_learning_loop_flag               true
% 7.53/1.49  --inst_learning_start                   3000
% 7.53/1.49  --inst_learning_factor                  2
% 7.53/1.49  --inst_start_prop_sim_after_learn       3
% 7.53/1.49  --inst_sel_renew                        solver
% 7.53/1.49  --inst_lit_activity_flag                true
% 7.53/1.49  --inst_restr_to_given                   false
% 7.53/1.49  --inst_activity_threshold               500
% 7.53/1.49  --inst_out_proof                        true
% 7.53/1.49  
% 7.53/1.49  ------ Resolution Options
% 7.53/1.49  
% 7.53/1.49  --resolution_flag                       false
% 7.53/1.49  --res_lit_sel                           adaptive
% 7.53/1.49  --res_lit_sel_side                      none
% 7.53/1.49  --res_ordering                          kbo
% 7.53/1.49  --res_to_prop_solver                    active
% 7.53/1.49  --res_prop_simpl_new                    false
% 7.53/1.49  --res_prop_simpl_given                  true
% 7.53/1.49  --res_passive_queue_type                priority_queues
% 7.53/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.53/1.49  --res_passive_queues_freq               [15;5]
% 7.53/1.49  --res_forward_subs                      full
% 7.53/1.49  --res_backward_subs                     full
% 7.53/1.49  --res_forward_subs_resolution           true
% 7.53/1.49  --res_backward_subs_resolution          true
% 7.53/1.49  --res_orphan_elimination                true
% 7.53/1.49  --res_time_limit                        2.
% 7.53/1.49  --res_out_proof                         true
% 7.53/1.49  
% 7.53/1.49  ------ Superposition Options
% 7.53/1.49  
% 7.53/1.49  --superposition_flag                    true
% 7.53/1.49  --sup_passive_queue_type                priority_queues
% 7.53/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.53/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.53/1.49  --demod_completeness_check              fast
% 7.53/1.49  --demod_use_ground                      true
% 7.53/1.49  --sup_to_prop_solver                    passive
% 7.53/1.49  --sup_prop_simpl_new                    true
% 7.53/1.49  --sup_prop_simpl_given                  true
% 7.53/1.49  --sup_fun_splitting                     false
% 7.53/1.49  --sup_smt_interval                      50000
% 7.53/1.49  
% 7.53/1.49  ------ Superposition Simplification Setup
% 7.53/1.49  
% 7.53/1.49  --sup_indices_passive                   []
% 7.53/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.53/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.53/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.49  --sup_full_bw                           [BwDemod]
% 7.53/1.49  --sup_immed_triv                        [TrivRules]
% 7.53/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.53/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.49  --sup_immed_bw_main                     []
% 7.53/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.53/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.53/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.53/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.53/1.49  
% 7.53/1.49  ------ Combination Options
% 7.53/1.49  
% 7.53/1.49  --comb_res_mult                         3
% 7.53/1.49  --comb_sup_mult                         2
% 7.53/1.49  --comb_inst_mult                        10
% 7.53/1.49  
% 7.53/1.49  ------ Debug Options
% 7.53/1.49  
% 7.53/1.49  --dbg_backtrace                         false
% 7.53/1.49  --dbg_dump_prop_clauses                 false
% 7.53/1.49  --dbg_dump_prop_clauses_file            -
% 7.53/1.49  --dbg_out_stat                          false
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  ------ Proving...
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  % SZS status Theorem for theBenchmark.p
% 7.53/1.49  
% 7.53/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.53/1.49  
% 7.53/1.49  fof(f5,axiom,(
% 7.53/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 7.53/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f20,plain,(
% 7.53/1.49    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 7.53/1.49    inference(ennf_transformation,[],[f5])).
% 7.53/1.49  
% 7.53/1.49  fof(f53,plain,(
% 7.53/1.49    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f20])).
% 7.53/1.49  
% 7.53/1.49  fof(f15,conjecture,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.53/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f16,negated_conjecture,(
% 7.53/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.53/1.49    inference(negated_conjecture,[],[f15])).
% 7.53/1.49  
% 7.53/1.49  fof(f36,plain,(
% 7.53/1.49    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.53/1.49    inference(ennf_transformation,[],[f16])).
% 7.53/1.49  
% 7.53/1.49  fof(f37,plain,(
% 7.53/1.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.53/1.49    inference(flattening,[],[f36])).
% 7.53/1.49  
% 7.53/1.49  fof(f43,plain,(
% 7.53/1.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 7.53/1.49    introduced(choice_axiom,[])).
% 7.53/1.49  
% 7.53/1.49  fof(f44,plain,(
% 7.53/1.49    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 7.53/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f43])).
% 7.53/1.49  
% 7.53/1.49  fof(f72,plain,(
% 7.53/1.49    r1_tarski(sK2,sK0)),
% 7.53/1.49    inference(cnf_transformation,[],[f44])).
% 7.53/1.49  
% 7.53/1.49  fof(f12,axiom,(
% 7.53/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.53/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f30,plain,(
% 7.53/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.49    inference(ennf_transformation,[],[f12])).
% 7.53/1.49  
% 7.53/1.49  fof(f31,plain,(
% 7.53/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.49    inference(flattening,[],[f30])).
% 7.53/1.49  
% 7.53/1.49  fof(f42,plain,(
% 7.53/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.49    inference(nnf_transformation,[],[f31])).
% 7.53/1.49  
% 7.53/1.49  fof(f60,plain,(
% 7.53/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f42])).
% 7.53/1.49  
% 7.53/1.49  fof(f70,plain,(
% 7.53/1.49    v1_funct_2(sK3,sK0,sK1)),
% 7.53/1.49    inference(cnf_transformation,[],[f44])).
% 7.53/1.49  
% 7.53/1.49  fof(f71,plain,(
% 7.53/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.53/1.49    inference(cnf_transformation,[],[f44])).
% 7.53/1.49  
% 7.53/1.49  fof(f9,axiom,(
% 7.53/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.53/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f25,plain,(
% 7.53/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.49    inference(ennf_transformation,[],[f9])).
% 7.53/1.49  
% 7.53/1.49  fof(f57,plain,(
% 7.53/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f25])).
% 7.53/1.49  
% 7.53/1.49  fof(f6,axiom,(
% 7.53/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.53/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f21,plain,(
% 7.53/1.49    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.53/1.49    inference(ennf_transformation,[],[f6])).
% 7.53/1.49  
% 7.53/1.49  fof(f22,plain,(
% 7.53/1.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.53/1.49    inference(flattening,[],[f21])).
% 7.53/1.49  
% 7.53/1.49  fof(f54,plain,(
% 7.53/1.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f22])).
% 7.53/1.49  
% 7.53/1.49  fof(f7,axiom,(
% 7.53/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.53/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f23,plain,(
% 7.53/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.49    inference(ennf_transformation,[],[f7])).
% 7.53/1.49  
% 7.53/1.49  fof(f55,plain,(
% 7.53/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f23])).
% 7.53/1.49  
% 7.53/1.49  fof(f11,axiom,(
% 7.53/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 7.53/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f28,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 7.53/1.49    inference(ennf_transformation,[],[f11])).
% 7.53/1.49  
% 7.53/1.49  fof(f29,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 7.53/1.49    inference(flattening,[],[f28])).
% 7.53/1.49  
% 7.53/1.49  fof(f59,plain,(
% 7.53/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f29])).
% 7.53/1.49  
% 7.53/1.49  fof(f10,axiom,(
% 7.53/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 7.53/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f26,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 7.53/1.49    inference(ennf_transformation,[],[f10])).
% 7.53/1.49  
% 7.53/1.49  fof(f27,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 7.53/1.49    inference(flattening,[],[f26])).
% 7.53/1.49  
% 7.53/1.49  fof(f58,plain,(
% 7.53/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f27])).
% 7.53/1.49  
% 7.53/1.49  fof(f1,axiom,(
% 7.53/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.53/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f38,plain,(
% 7.53/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.53/1.49    inference(nnf_transformation,[],[f1])).
% 7.53/1.49  
% 7.53/1.49  fof(f39,plain,(
% 7.53/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.53/1.49    inference(flattening,[],[f38])).
% 7.53/1.49  
% 7.53/1.49  fof(f45,plain,(
% 7.53/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.53/1.49    inference(cnf_transformation,[],[f39])).
% 7.53/1.49  
% 7.53/1.49  fof(f76,plain,(
% 7.53/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.53/1.49    inference(equality_resolution,[],[f45])).
% 7.53/1.49  
% 7.53/1.49  fof(f14,axiom,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.53/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f34,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.53/1.49    inference(ennf_transformation,[],[f14])).
% 7.53/1.49  
% 7.53/1.49  fof(f35,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.53/1.49    inference(flattening,[],[f34])).
% 7.53/1.49  
% 7.53/1.49  fof(f68,plain,(
% 7.53/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f35])).
% 7.53/1.49  
% 7.53/1.49  fof(f69,plain,(
% 7.53/1.49    v1_funct_1(sK3)),
% 7.53/1.49    inference(cnf_transformation,[],[f44])).
% 7.53/1.49  
% 7.53/1.49  fof(f62,plain,(
% 7.53/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f42])).
% 7.53/1.49  
% 7.53/1.49  fof(f74,plain,(
% 7.53/1.49    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 7.53/1.49    inference(cnf_transformation,[],[f44])).
% 7.53/1.49  
% 7.53/1.49  fof(f13,axiom,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 7.53/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f32,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.53/1.49    inference(ennf_transformation,[],[f13])).
% 7.53/1.49  
% 7.53/1.49  fof(f33,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.53/1.49    inference(flattening,[],[f32])).
% 7.53/1.49  
% 7.53/1.49  fof(f66,plain,(
% 7.53/1.49    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f33])).
% 7.53/1.49  
% 7.53/1.49  fof(f65,plain,(
% 7.53/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f42])).
% 7.53/1.49  
% 7.53/1.49  fof(f79,plain,(
% 7.53/1.49    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.49    inference(equality_resolution,[],[f65])).
% 7.53/1.49  
% 7.53/1.49  fof(f80,plain,(
% 7.53/1.49    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.53/1.49    inference(equality_resolution,[],[f79])).
% 7.53/1.49  
% 7.53/1.49  fof(f3,axiom,(
% 7.53/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.53/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f40,plain,(
% 7.53/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.53/1.49    inference(nnf_transformation,[],[f3])).
% 7.53/1.49  
% 7.53/1.49  fof(f41,plain,(
% 7.53/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.53/1.49    inference(flattening,[],[f40])).
% 7.53/1.49  
% 7.53/1.49  fof(f51,plain,(
% 7.53/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.53/1.49    inference(cnf_transformation,[],[f41])).
% 7.53/1.49  
% 7.53/1.49  fof(f77,plain,(
% 7.53/1.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.53/1.49    inference(equality_resolution,[],[f51])).
% 7.53/1.49  
% 7.53/1.49  fof(f73,plain,(
% 7.53/1.49    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 7.53/1.49    inference(cnf_transformation,[],[f44])).
% 7.53/1.49  
% 7.53/1.49  fof(f49,plain,(
% 7.53/1.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f41])).
% 7.53/1.49  
% 7.53/1.49  fof(f50,plain,(
% 7.53/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.53/1.49    inference(cnf_transformation,[],[f41])).
% 7.53/1.49  
% 7.53/1.49  fof(f78,plain,(
% 7.53/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.53/1.49    inference(equality_resolution,[],[f50])).
% 7.53/1.49  
% 7.53/1.49  fof(f47,plain,(
% 7.53/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f39])).
% 7.53/1.49  
% 7.53/1.49  fof(f2,axiom,(
% 7.53/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.53/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f48,plain,(
% 7.53/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f2])).
% 7.53/1.49  
% 7.53/1.49  fof(f67,plain,(
% 7.53/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f33])).
% 7.53/1.49  
% 7.53/1.49  fof(f61,plain,(
% 7.53/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f42])).
% 7.53/1.49  
% 7.53/1.49  fof(f83,plain,(
% 7.53/1.49    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.53/1.49    inference(equality_resolution,[],[f61])).
% 7.53/1.49  
% 7.53/1.49  fof(f8,axiom,(
% 7.53/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.53/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f17,plain,(
% 7.53/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.53/1.49    inference(pure_predicate_removal,[],[f8])).
% 7.53/1.49  
% 7.53/1.49  fof(f24,plain,(
% 7.53/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.53/1.49    inference(ennf_transformation,[],[f17])).
% 7.53/1.49  
% 7.53/1.49  fof(f56,plain,(
% 7.53/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f24])).
% 7.53/1.49  
% 7.53/1.49  fof(f4,axiom,(
% 7.53/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.53/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f18,plain,(
% 7.53/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.53/1.49    inference(ennf_transformation,[],[f4])).
% 7.53/1.49  
% 7.53/1.49  fof(f19,plain,(
% 7.53/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.53/1.49    inference(flattening,[],[f18])).
% 7.53/1.49  
% 7.53/1.49  fof(f52,plain,(
% 7.53/1.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f19])).
% 7.53/1.49  
% 7.53/1.49  cnf(c_8,plain,
% 7.53/1.49      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1072,plain,
% 7.53/1.49      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 7.53/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_26,negated_conjecture,
% 7.53/1.49      ( r1_tarski(sK2,sK0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1063,plain,
% 7.53/1.49      ( r1_tarski(sK2,sK0) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_20,plain,
% 7.53/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.53/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.53/1.49      | k1_xboole_0 = X2 ),
% 7.53/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_28,negated_conjecture,
% 7.53/1.49      ( v1_funct_2(sK3,sK0,sK1) ),
% 7.53/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_439,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.53/1.49      | sK3 != X0
% 7.53/1.49      | sK1 != X2
% 7.53/1.49      | sK0 != X1
% 7.53/1.49      | k1_xboole_0 = X2 ),
% 7.53/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_440,plain,
% 7.53/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.53/1.49      | k1_relset_1(sK0,sK1,sK3) = sK0
% 7.53/1.49      | k1_xboole_0 = sK1 ),
% 7.53/1.49      inference(unflattening,[status(thm)],[c_439]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_27,negated_conjecture,
% 7.53/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.53/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_442,plain,
% 7.53/1.49      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_440,c_27]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1062,plain,
% 7.53/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_12,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1069,plain,
% 7.53/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.53/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2244,plain,
% 7.53/1.49      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1062,c_1069]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2296,plain,
% 7.53/1.49      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_442,c_2244]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9,plain,
% 7.53/1.49      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.53/1.49      | ~ v1_relat_1(X1)
% 7.53/1.49      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 7.53/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1071,plain,
% 7.53/1.49      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 7.53/1.49      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.53/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2935,plain,
% 7.53/1.49      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.53/1.49      | sK1 = k1_xboole_0
% 7.53/1.49      | r1_tarski(X0,sK0) != iProver_top
% 7.53/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_2296,c_1071]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_32,plain,
% 7.53/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_10,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | v1_relat_1(X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1269,plain,
% 7.53/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.53/1.49      | v1_relat_1(sK3) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1270,plain,
% 7.53/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.53/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1269]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3153,plain,
% 7.53/1.49      ( r1_tarski(X0,sK0) != iProver_top
% 7.53/1.49      | sK1 = k1_xboole_0
% 7.53/1.49      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_2935,c_32,c_1270]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3154,plain,
% 7.53/1.49      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.53/1.49      | sK1 = k1_xboole_0
% 7.53/1.49      | r1_tarski(X0,sK0) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_3153]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3165,plain,
% 7.53/1.49      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1063,c_3154]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_14,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | ~ r1_tarski(X3,X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1067,plain,
% 7.53/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.53/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.53/1.49      | r1_tarski(X3,X0) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3570,plain,
% 7.53/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 7.53/1.49      | r1_tarski(X0,sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1062,c_1067]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_13,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 7.53/1.49      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 7.53/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1068,plain,
% 7.53/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.53/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 7.53/1.49      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5361,plain,
% 7.53/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 7.53/1.49      | r1_tarski(X0,sK3) != iProver_top
% 7.53/1.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_3570,c_1068]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7195,plain,
% 7.53/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 7.53/1.49      | r1_tarski(X0,X2) != iProver_top
% 7.53/1.49      | r1_tarski(X2,sK3) != iProver_top
% 7.53/1.49      | r1_tarski(k1_relat_1(X2),X1) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_5361,c_1067]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_16576,plain,
% 7.53/1.49      ( sK1 = k1_xboole_0
% 7.53/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 7.53/1.49      | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
% 7.53/1.49      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 7.53/1.49      | r1_tarski(sK2,X1) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_3165,c_7195]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2,plain,
% 7.53/1.49      ( r1_tarski(X0,X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1074,plain,
% 7.53/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7193,plain,
% 7.53/1.49      ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
% 7.53/1.49      | r1_tarski(X1,sK3) != iProver_top
% 7.53/1.49      | r1_tarski(k1_relat_1(X1),X0) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_5361,c_1069]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_12265,plain,
% 7.53/1.49      ( k1_relset_1(k1_relat_1(X0),sK1,X0) = k1_relat_1(X0)
% 7.53/1.49      | r1_tarski(X0,sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1074,c_7193]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_16277,plain,
% 7.53/1.49      ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0))
% 7.53/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1072,c_12265]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_30534,plain,
% 7.53/1.49      ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_16277,c_32,c_1270]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_30539,plain,
% 7.53/1.49      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 7.53/1.49      | sK1 = k1_xboole_0 ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_3165,c_30534]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_23,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | ~ v1_funct_1(X0)
% 7.53/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.53/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1064,plain,
% 7.53/1.49      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.53/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.53/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4103,plain,
% 7.53/1.49      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1062,c_1064]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_29,negated_conjecture,
% 7.53/1.49      ( v1_funct_1(sK3) ),
% 7.53/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1346,plain,
% 7.53/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.53/1.49      | ~ v1_funct_1(sK3)
% 7.53/1.49      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_23]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1459,plain,
% 7.53/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.53/1.49      | ~ v1_funct_1(sK3)
% 7.53/1.49      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1346]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4409,plain,
% 7.53/1.49      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_4103,c_29,c_27,c_1459]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_18,plain,
% 7.53/1.49      ( v1_funct_2(X0,X1,X2)
% 7.53/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | k1_relset_1(X1,X2,X0) != X1
% 7.53/1.49      | k1_xboole_0 = X2 ),
% 7.53/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_24,negated_conjecture,
% 7.53/1.49      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 7.53/1.49      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.53/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 7.53/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_423,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.53/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.53/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 7.53/1.49      | k1_relset_1(X1,X2,X0) != X1
% 7.53/1.49      | sK2 != X1
% 7.53/1.49      | sK1 != X2
% 7.53/1.49      | k1_xboole_0 = X2 ),
% 7.53/1.49      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_424,plain,
% 7.53/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.53/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.53/1.49      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 7.53/1.49      | k1_xboole_0 = sK1 ),
% 7.53/1.49      inference(unflattening,[status(thm)],[c_423]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1055,plain,
% 7.53/1.49      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 7.53/1.49      | k1_xboole_0 = sK1
% 7.53/1.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4416,plain,
% 7.53/1.49      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 7.53/1.49      | sK1 = k1_xboole_0
% 7.53/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.53/1.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_4409,c_1055]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_22,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | ~ v1_funct_1(X0)
% 7.53/1.49      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 7.53/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1065,plain,
% 7.53/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.53/1.49      | v1_funct_1(X0) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2022,plain,
% 7.53/1.49      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1062,c_1065]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_30,plain,
% 7.53/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1319,plain,
% 7.53/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.53/1.49      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 7.53/1.49      | ~ v1_funct_1(sK3) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_22]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1656,plain,
% 7.53/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.53/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 7.53/1.49      | ~ v1_funct_1(sK3) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1319]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1657,plain,
% 7.53/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1656]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2374,plain,
% 7.53/1.49      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_2022,c_30,c_32,c_1657]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4417,plain,
% 7.53/1.49      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_4409,c_2374]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4424,plain,
% 7.53/1.49      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 7.53/1.49      | sK1 = k1_xboole_0
% 7.53/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.53/1.49      inference(forward_subsumption_resolution,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_4416,c_4417]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_31197,plain,
% 7.53/1.49      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 7.53/1.49      | sK1 = k1_xboole_0
% 7.53/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_30539,c_4424]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_32861,plain,
% 7.53/1.49      ( sK1 = k1_xboole_0
% 7.53/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_31197,c_3165]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_32870,plain,
% 7.53/1.49      ( sK1 = k1_xboole_0
% 7.53/1.49      | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
% 7.53/1.49      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 7.53/1.49      | r1_tarski(sK2,sK2) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_16576,c_32861]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9033,plain,
% 7.53/1.49      ( r1_tarski(sK2,sK2) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9036,plain,
% 7.53/1.49      ( r1_tarski(sK2,sK2) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_9033]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_33997,plain,
% 7.53/1.49      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 7.53/1.49      | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
% 7.53/1.49      | sK1 = k1_xboole_0 ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_32870,c_9036]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_33998,plain,
% 7.53/1.49      ( sK1 = k1_xboole_0
% 7.53/1.49      | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
% 7.53/1.49      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_33997]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_34004,plain,
% 7.53/1.49      ( sK1 = k1_xboole_0
% 7.53/1.49      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top ),
% 7.53/1.49      inference(forward_subsumption_resolution,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_33998,c_1074]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_34006,plain,
% 7.53/1.49      ( sK1 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1072,c_34004]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_34889,plain,
% 7.53/1.49      ( sK1 = k1_xboole_0 ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_34006,c_32,c_1270]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_15,plain,
% 7.53/1.49      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 7.53/1.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.53/1.49      | k1_xboole_0 = X0 ),
% 7.53/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_345,plain,
% 7.53/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.53/1.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 7.53/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.53/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.53/1.49      | sK2 != X0
% 7.53/1.49      | sK1 != k1_xboole_0
% 7.53/1.49      | k1_xboole_0 = X0 ),
% 7.53/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_346,plain,
% 7.53/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.53/1.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 7.53/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.53/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.53/1.49      | sK1 != k1_xboole_0
% 7.53/1.49      | k1_xboole_0 = sK2 ),
% 7.53/1.49      inference(unflattening,[status(thm)],[c_345]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1059,plain,
% 7.53/1.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.53/1.49      | sK1 != k1_xboole_0
% 7.53/1.49      | k1_xboole_0 = sK2
% 7.53/1.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.53/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4,plain,
% 7.53/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.53/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1194,plain,
% 7.53/1.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 7.53/1.49      | sK2 = k1_xboole_0
% 7.53/1.49      | sK1 != k1_xboole_0
% 7.53/1.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.53/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_1059,c_4]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4414,plain,
% 7.53/1.49      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 7.53/1.49      | sK2 = k1_xboole_0
% 7.53/1.49      | sK1 != k1_xboole_0
% 7.53/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.53/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.53/1.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_4409,c_1194]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4442,plain,
% 7.53/1.49      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 7.53/1.49      | sK2 = k1_xboole_0
% 7.53/1.49      | sK1 != k1_xboole_0
% 7.53/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.53/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.53/1.49      inference(forward_subsumption_resolution,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_4414,c_4417]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_25,negated_conjecture,
% 7.53/1.49      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 7.53/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_6,plain,
% 7.53/1.49      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.53/1.49      | k1_xboole_0 = X1
% 7.53/1.49      | k1_xboole_0 = X0 ),
% 7.53/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_82,plain,
% 7.53/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.53/1.49      | k1_xboole_0 = k1_xboole_0 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5,plain,
% 7.53/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.53/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_83,plain,
% 7.53/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_0,plain,
% 7.53/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.53/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1284,plain,
% 7.53/1.49      ( ~ r1_tarski(sK2,k1_xboole_0)
% 7.53/1.49      | ~ r1_tarski(k1_xboole_0,sK2)
% 7.53/1.49      | sK2 = k1_xboole_0 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_679,plain,( X0 = X0 ),theory(equality) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1558,plain,
% 7.53/1.49      ( sK2 = sK2 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_679]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_680,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1841,plain,
% 7.53/1.49      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_680]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1842,plain,
% 7.53/1.49      ( sK1 != k1_xboole_0
% 7.53/1.49      | k1_xboole_0 = sK1
% 7.53/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1841]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_681,plain,
% 7.53/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.53/1.49      theory(equality) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1484,plain,
% 7.53/1.49      ( ~ r1_tarski(X0,X1)
% 7.53/1.49      | r1_tarski(sK2,k1_xboole_0)
% 7.53/1.49      | sK2 != X0
% 7.53/1.49      | k1_xboole_0 != X1 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_681]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2536,plain,
% 7.53/1.49      ( ~ r1_tarski(sK2,X0)
% 7.53/1.49      | r1_tarski(sK2,k1_xboole_0)
% 7.53/1.49      | sK2 != sK2
% 7.53/1.49      | k1_xboole_0 != X0 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1484]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9038,plain,
% 7.53/1.49      ( ~ r1_tarski(sK2,sK0)
% 7.53/1.49      | r1_tarski(sK2,k1_xboole_0)
% 7.53/1.49      | sK2 != sK2
% 7.53/1.49      | k1_xboole_0 != sK0 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_2536]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3,plain,
% 7.53/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_10367,plain,
% 7.53/1.49      ( r1_tarski(k1_xboole_0,sK2) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_23043,plain,
% 7.53/1.49      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_4442,c_26,c_25,c_82,c_83,c_1284,c_1558,c_1842,c_9038,
% 7.53/1.49                 c_10367]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_34928,plain,
% 7.53/1.49      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_34889,c_23043]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35533,plain,
% 7.53/1.49      ( sK2 = k1_xboole_0 ),
% 7.53/1.49      inference(equality_resolution_simp,[status(thm)],[c_34928]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_450,plain,
% 7.53/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.53/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.53/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 7.53/1.49      | sK2 != sK0
% 7.53/1.49      | sK1 != sK1 ),
% 7.53/1.49      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_525,plain,
% 7.53/1.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.53/1.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 7.53/1.49      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 7.53/1.49      | sK2 != sK0 ),
% 7.53/1.49      inference(equality_resolution_simp,[status(thm)],[c_450]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1054,plain,
% 7.53/1.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 7.53/1.49      | sK2 != sK0
% 7.53/1.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4415,plain,
% 7.53/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.53/1.49      | sK2 != sK0
% 7.53/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.53/1.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_4409,c_1054]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4432,plain,
% 7.53/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.53/1.49      | sK2 != sK0
% 7.53/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.53/1.49      inference(forward_subsumption_resolution,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_4415,c_4417]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_34980,plain,
% 7.53/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.53/1.49      | sK2 != sK0
% 7.53/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_34889,c_4432]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35036,plain,
% 7.53/1.49      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_34889,c_25]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35037,plain,
% 7.53/1.49      ( sK0 = k1_xboole_0 ),
% 7.53/1.49      inference(equality_resolution_simp,[status(thm)],[c_35036]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35251,plain,
% 7.53/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.53/1.49      | sK2 != k1_xboole_0
% 7.53/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 7.53/1.49      inference(light_normalisation,[status(thm)],[c_34980,c_35037]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35255,plain,
% 7.53/1.49      ( k7_relat_1(sK3,sK2) != sK3
% 7.53/1.49      | sK2 != k1_xboole_0
% 7.53/1.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_35251,c_4]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35555,plain,
% 7.53/1.49      ( k7_relat_1(sK3,k1_xboole_0) != sK3
% 7.53/1.49      | k1_xboole_0 != k1_xboole_0
% 7.53/1.49      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_35533,c_35255]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35569,plain,
% 7.53/1.49      ( k7_relat_1(sK3,k1_xboole_0) != sK3
% 7.53/1.49      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.53/1.49      inference(equality_resolution_simp,[status(thm)],[c_35555]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_21,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | ~ v1_funct_1(X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1066,plain,
% 7.53/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.53/1.49      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.53/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4465,plain,
% 7.53/1.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_4409,c_1066]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1356,plain,
% 7.53/1.49      ( r1_tarski(k7_relat_1(sK3,X0),sK3) | ~ v1_relat_1(sK3) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1357,plain,
% 7.53/1.49      ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
% 7.53/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1356]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1314,plain,
% 7.53/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.53/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.53/1.49      | ~ r1_tarski(X0,sK3) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1543,plain,
% 7.53/1.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.53/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.53/1.49      | ~ r1_tarski(k7_relat_1(sK3,X0),sK3) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1314]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1544,plain,
% 7.53/1.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.53/1.49      | r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1543]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_8516,plain,
% 7.53/1.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_4465,c_32,c_1270,c_1357,c_1544]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35004,plain,
% 7.53/1.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_34889,c_8516]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35182,plain,
% 7.53/1.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.53/1.49      inference(light_normalisation,[status(thm)],[c_35004,c_35037]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35184,plain,
% 7.53/1.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_35182,c_5]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35572,plain,
% 7.53/1.49      ( k7_relat_1(sK3,k1_xboole_0) != sK3 ),
% 7.53/1.49      inference(forward_subsumption_resolution,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_35569,c_35184]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35031,plain,
% 7.53/1.49      ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_34889,c_2244]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_19,plain,
% 7.53/1.49      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.53/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.53/1.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.53/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_410,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.53/1.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 7.53/1.49      | sK3 != X0
% 7.53/1.49      | sK1 != X1
% 7.53/1.49      | sK0 != k1_xboole_0 ),
% 7.53/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_411,plain,
% 7.53/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 7.53/1.49      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 7.53/1.49      | sK0 != k1_xboole_0 ),
% 7.53/1.49      inference(unflattening,[status(thm)],[c_410]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1056,plain,
% 7.53/1.49      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 7.53/1.49      | sK0 != k1_xboole_0
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1132,plain,
% 7.53/1.49      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 7.53/1.49      | sK0 != k1_xboole_0
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_1056,c_5]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35033,plain,
% 7.53/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.53/1.49      | sK0 != k1_xboole_0
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_34889,c_1132]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35044,plain,
% 7.53/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.53/1.49      | k1_xboole_0 != k1_xboole_0
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.53/1.49      inference(light_normalisation,[status(thm)],[c_35033,c_35037]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35045,plain,
% 7.53/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.53/1.49      inference(equality_resolution_simp,[status(thm)],[c_35044]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35035,plain,
% 7.53/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_34889,c_1062]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35040,plain,
% 7.53/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.53/1.49      inference(light_normalisation,[status(thm)],[c_35035,c_35037]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35042,plain,
% 7.53/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.53/1.49      inference(demodulation,[status(thm)],[c_35040,c_5]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35048,plain,
% 7.53/1.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 7.53/1.49      inference(forward_subsumption_resolution,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_35045,c_35042]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35051,plain,
% 7.53/1.49      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 7.53/1.49      inference(light_normalisation,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_35031,c_35037,c_35048]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1331,plain,
% 7.53/1.49      ( ~ r1_tarski(X0,X1)
% 7.53/1.49      | r1_tarski(k1_relat_1(X2),X3)
% 7.53/1.49      | X3 != X1
% 7.53/1.49      | k1_relat_1(X2) != X0 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_681]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11530,plain,
% 7.53/1.49      ( ~ r1_tarski(X0,X1)
% 7.53/1.49      | r1_tarski(k1_relat_1(sK3),X2)
% 7.53/1.49      | X2 != X1
% 7.53/1.49      | k1_relat_1(sK3) != X0 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1331]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11532,plain,
% 7.53/1.49      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 7.53/1.49      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.53/1.49      | k1_relat_1(sK3) != k1_xboole_0
% 7.53/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_11530]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5360,plain,
% 7.53/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 7.53/1.49      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1062,c_1068]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | v4_relat_1(X0,X1) ),
% 7.53/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7,plain,
% 7.53/1.49      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.53/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_286,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | ~ v1_relat_1(X0)
% 7.53/1.49      | k7_relat_1(X0,X1) = X0 ),
% 7.53/1.49      inference(resolution,[status(thm)],[c_11,c_7]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_290,plain,
% 7.53/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | k7_relat_1(X0,X1) = X0 ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_286,c_11,c_10,c_7]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1060,plain,
% 7.53/1.49      ( k7_relat_1(X0,X1) = X0
% 7.53/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5763,plain,
% 7.53/1.49      ( k7_relat_1(sK3,X0) = sK3
% 7.53/1.49      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_5360,c_1060]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5807,plain,
% 7.53/1.49      ( ~ r1_tarski(k1_relat_1(sK3),X0) | k7_relat_1(sK3,X0) = sK3 ),
% 7.53/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_5763]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5809,plain,
% 7.53/1.49      ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 7.53/1.49      | k7_relat_1(sK3,k1_xboole_0) = sK3 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_5807]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_85,plain,
% 7.53/1.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(contradiction,plain,
% 7.53/1.49      ( $false ),
% 7.53/1.49      inference(minisat,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_35572,c_35051,c_11532,c_5809,c_85,c_83,c_82]) ).
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.53/1.49  
% 7.53/1.49  ------                               Statistics
% 7.53/1.49  
% 7.53/1.49  ------ General
% 7.53/1.49  
% 7.53/1.49  abstr_ref_over_cycles:                  0
% 7.53/1.49  abstr_ref_under_cycles:                 0
% 7.53/1.49  gc_basic_clause_elim:                   0
% 7.53/1.49  forced_gc_time:                         0
% 7.53/1.49  parsing_time:                           0.01
% 7.53/1.49  unif_index_cands_time:                  0.
% 7.53/1.49  unif_index_add_time:                    0.
% 7.53/1.49  orderings_time:                         0.
% 7.53/1.49  out_proof_time:                         0.024
% 7.53/1.49  total_time:                             0.867
% 7.53/1.49  num_of_symbols:                         48
% 7.53/1.49  num_of_terms:                           26628
% 7.53/1.49  
% 7.53/1.49  ------ Preprocessing
% 7.53/1.49  
% 7.53/1.49  num_of_splits:                          0
% 7.53/1.49  num_of_split_atoms:                     0
% 7.53/1.49  num_of_reused_defs:                     0
% 7.53/1.49  num_eq_ax_congr_red:                    13
% 7.53/1.49  num_of_sem_filtered_clauses:            1
% 7.53/1.49  num_of_subtypes:                        0
% 7.53/1.49  monotx_restored_types:                  0
% 7.53/1.49  sat_num_of_epr_types:                   0
% 7.53/1.49  sat_num_of_non_cyclic_types:            0
% 7.53/1.49  sat_guarded_non_collapsed_types:        0
% 7.53/1.49  num_pure_diseq_elim:                    0
% 7.53/1.49  simp_replaced_by:                       0
% 7.53/1.49  res_preprocessed:                       131
% 7.53/1.49  prep_upred:                             0
% 7.53/1.49  prep_unflattend:                        35
% 7.53/1.49  smt_new_axioms:                         0
% 7.53/1.49  pred_elim_cands:                        4
% 7.53/1.49  pred_elim:                              2
% 7.53/1.49  pred_elim_cl:                           2
% 7.53/1.49  pred_elim_cycles:                       5
% 7.53/1.49  merged_defs:                            0
% 7.53/1.49  merged_defs_ncl:                        0
% 7.53/1.49  bin_hyper_res:                          0
% 7.53/1.49  prep_cycles:                            4
% 7.53/1.49  pred_elim_time:                         0.006
% 7.53/1.49  splitting_time:                         0.
% 7.53/1.49  sem_filter_time:                        0.
% 7.53/1.49  monotx_time:                            0.
% 7.53/1.49  subtype_inf_time:                       0.
% 7.53/1.49  
% 7.53/1.49  ------ Problem properties
% 7.53/1.49  
% 7.53/1.49  clauses:                                27
% 7.53/1.49  conjectures:                            4
% 7.53/1.49  epr:                                    6
% 7.53/1.49  horn:                                   24
% 7.53/1.49  ground:                                 11
% 7.53/1.49  unary:                                  7
% 7.53/1.49  binary:                                 6
% 7.53/1.49  lits:                                   69
% 7.53/1.49  lits_eq:                                28
% 7.53/1.49  fd_pure:                                0
% 7.53/1.49  fd_pseudo:                              0
% 7.53/1.49  fd_cond:                                1
% 7.53/1.49  fd_pseudo_cond:                         1
% 7.53/1.49  ac_symbols:                             0
% 7.53/1.49  
% 7.53/1.49  ------ Propositional Solver
% 7.53/1.49  
% 7.53/1.49  prop_solver_calls:                      30
% 7.53/1.49  prop_fast_solver_calls:                 1728
% 7.53/1.49  smt_solver_calls:                       0
% 7.53/1.49  smt_fast_solver_calls:                  0
% 7.53/1.49  prop_num_of_clauses:                    13286
% 7.53/1.49  prop_preprocess_simplified:             24297
% 7.53/1.49  prop_fo_subsumed:                       45
% 7.53/1.49  prop_solver_time:                       0.
% 7.53/1.49  smt_solver_time:                        0.
% 7.53/1.49  smt_fast_solver_time:                   0.
% 7.53/1.49  prop_fast_solver_time:                  0.
% 7.53/1.49  prop_unsat_core_time:                   0.001
% 7.53/1.49  
% 7.53/1.49  ------ QBF
% 7.53/1.49  
% 7.53/1.49  qbf_q_res:                              0
% 7.53/1.49  qbf_num_tautologies:                    0
% 7.53/1.49  qbf_prep_cycles:                        0
% 7.53/1.49  
% 7.53/1.49  ------ BMC1
% 7.53/1.49  
% 7.53/1.49  bmc1_current_bound:                     -1
% 7.53/1.49  bmc1_last_solved_bound:                 -1
% 7.53/1.49  bmc1_unsat_core_size:                   -1
% 7.53/1.49  bmc1_unsat_core_parents_size:           -1
% 7.53/1.49  bmc1_merge_next_fun:                    0
% 7.53/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.53/1.49  
% 7.53/1.49  ------ Instantiation
% 7.53/1.49  
% 7.53/1.49  inst_num_of_clauses:                    4052
% 7.53/1.49  inst_num_in_passive:                    1088
% 7.53/1.49  inst_num_in_active:                     1436
% 7.53/1.49  inst_num_in_unprocessed:                1528
% 7.53/1.49  inst_num_of_loops:                      1570
% 7.53/1.49  inst_num_of_learning_restarts:          0
% 7.53/1.49  inst_num_moves_active_passive:          131
% 7.53/1.49  inst_lit_activity:                      0
% 7.53/1.49  inst_lit_activity_moves:                0
% 7.53/1.49  inst_num_tautologies:                   0
% 7.53/1.49  inst_num_prop_implied:                  0
% 7.53/1.49  inst_num_existing_simplified:           0
% 7.53/1.49  inst_num_eq_res_simplified:             0
% 7.53/1.49  inst_num_child_elim:                    0
% 7.53/1.49  inst_num_of_dismatching_blockings:      2013
% 7.53/1.49  inst_num_of_non_proper_insts:           4369
% 7.53/1.49  inst_num_of_duplicates:                 0
% 7.53/1.49  inst_inst_num_from_inst_to_res:         0
% 7.53/1.49  inst_dismatching_checking_time:         0.
% 7.53/1.49  
% 7.53/1.49  ------ Resolution
% 7.53/1.49  
% 7.53/1.49  res_num_of_clauses:                     0
% 7.53/1.49  res_num_in_passive:                     0
% 7.53/1.49  res_num_in_active:                      0
% 7.53/1.49  res_num_of_loops:                       135
% 7.53/1.49  res_forward_subset_subsumed:            220
% 7.53/1.49  res_backward_subset_subsumed:           2
% 7.53/1.49  res_forward_subsumed:                   0
% 7.53/1.49  res_backward_subsumed:                  0
% 7.53/1.49  res_forward_subsumption_resolution:     0
% 7.53/1.49  res_backward_subsumption_resolution:    0
% 7.53/1.49  res_clause_to_clause_subsumption:       3944
% 7.53/1.49  res_orphan_elimination:                 0
% 7.53/1.49  res_tautology_del:                      407
% 7.53/1.49  res_num_eq_res_simplified:              1
% 7.53/1.49  res_num_sel_changes:                    0
% 7.53/1.49  res_moves_from_active_to_pass:          0
% 7.53/1.49  
% 7.53/1.49  ------ Superposition
% 7.53/1.49  
% 7.53/1.49  sup_time_total:                         0.
% 7.53/1.49  sup_time_generating:                    0.
% 7.53/1.49  sup_time_sim_full:                      0.
% 7.53/1.49  sup_time_sim_immed:                     0.
% 7.53/1.49  
% 7.53/1.49  sup_num_of_clauses:                     496
% 7.53/1.49  sup_num_in_active:                      141
% 7.53/1.49  sup_num_in_passive:                     355
% 7.53/1.49  sup_num_of_loops:                       312
% 7.53/1.49  sup_fw_superposition:                   585
% 7.53/1.49  sup_bw_superposition:                   384
% 7.53/1.49  sup_immediate_simplified:               422
% 7.53/1.49  sup_given_eliminated:                   0
% 7.53/1.49  comparisons_done:                       0
% 7.53/1.49  comparisons_avoided:                    117
% 7.53/1.49  
% 7.53/1.49  ------ Simplifications
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  sim_fw_subset_subsumed:                 99
% 7.53/1.49  sim_bw_subset_subsumed:                 51
% 7.53/1.49  sim_fw_subsumed:                        101
% 7.53/1.49  sim_bw_subsumed:                        11
% 7.53/1.49  sim_fw_subsumption_res:                 13
% 7.53/1.49  sim_bw_subsumption_res:                 0
% 7.53/1.49  sim_tautology_del:                      3
% 7.53/1.49  sim_eq_tautology_del:                   67
% 7.53/1.49  sim_eq_res_simp:                        7
% 7.53/1.49  sim_fw_demodulated:                     46
% 7.53/1.49  sim_bw_demodulated:                     184
% 7.53/1.49  sim_light_normalised:                   150
% 7.53/1.49  sim_joinable_taut:                      0
% 7.53/1.49  sim_joinable_simp:                      0
% 7.53/1.49  sim_ac_normalised:                      0
% 7.53/1.49  sim_smt_subsumption:                    0
% 7.53/1.49  
%------------------------------------------------------------------------------
