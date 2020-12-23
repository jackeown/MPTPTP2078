%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:01 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  275 (11582 expanded)
%              Number of clauses        :  197 (4198 expanded)
%              Number of leaves         :   22 (2124 expanded)
%              Depth                    :   30
%              Number of atoms          :  832 (60368 expanded)
%              Number of equality atoms :  499 (16715 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

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

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f41,plain,
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

fof(f42,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f41])).

fof(f72,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f78,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f77])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3052,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1010,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_1011,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1010])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1013,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1011,c_29])).

cnf(c_3051,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3057,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4149,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3051,c_3057])).

cnf(c_4259,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1013,c_4149])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3058,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4438,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4259,c_3058])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3314,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3315,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3314])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_222,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_223,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_222])).

cnf(c_279,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_223])).

cnf(c_3326,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_3720,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3326])).

cnf(c_3721,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3720])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3974,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3975,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3974])).

cnf(c_4674,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4438,c_34,c_3315,c_3721,c_3975])).

cnf(c_4675,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4674])).

cnf(c_4684,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3052,c_4675])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3053,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6665,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4684,c_3053])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3054,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5246,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3051,c_3054])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3396,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3550,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_3396])).

cnf(c_5424,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5246,c_31,c_29,c_3550])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3055,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4487,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3051,c_3055])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3376,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3811,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3376])).

cnf(c_3812,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3811])).

cnf(c_4666,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4487,c_32,c_34,c_3812])).

cnf(c_5433,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5424,c_4666])).

cnf(c_7179,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6665,c_5433])).

cnf(c_7183,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_7179])).

cnf(c_10,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3059,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3049,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_5808,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3059,c_3049])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_26])).

cnf(c_1022,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1021])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_8])).

cnf(c_1034,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1022,c_374])).

cnf(c_3039,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1034])).

cnf(c_5430,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5424,c_3039])).

cnf(c_5456,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5430,c_5433])).

cnf(c_7583,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4684,c_5456])).

cnf(c_7590,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7179,c_7583])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3056,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5891,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5424,c_3056])).

cnf(c_6419,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5891,c_32,c_34])).

cnf(c_3048,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_6429,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6419,c_3048])).

cnf(c_3061,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6426,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6419,c_3061])).

cnf(c_6528,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6426,c_3049])).

cnf(c_6562,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6429,c_3975,c_6528])).

cnf(c_7640,plain,
    ( sK1 = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7590,c_6562])).

cnf(c_7642,plain,
    ( sK1 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5808,c_7640])).

cnf(c_7831,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7183,c_34,c_3315,c_3721,c_3975,c_7642])).

cnf(c_7853,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_7831,c_4149])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7859,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7831,c_27])).

cnf(c_7860,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7859])).

cnf(c_7876,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_7853,c_7860])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_954,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_955,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_954])).

cnf(c_3042,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_955])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3122,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3042,c_2])).

cnf(c_7856,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7831,c_3122])).

cnf(c_7866,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7856,c_7860])).

cnf(c_7867,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7866])).

cnf(c_7878,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7876,c_7867])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_99,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_100,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2421,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3489,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2421])).

cnf(c_2422,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3581,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_2422])).

cnf(c_3582,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3581])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_889,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X0
    | sK1 != k1_xboole_0
    | sK0 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_30])).

cnf(c_890,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_3045,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_890])).

cnf(c_3129,plain,
    ( sK3 = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3045,c_1])).

cnf(c_3341,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_2422])).

cnf(c_3611,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_3341])).

cnf(c_3612,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_2421])).

cnf(c_3693,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2422])).

cnf(c_3694,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3693])).

cnf(c_3716,plain,
    ( sK0 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3129,c_27,c_99,c_100,c_3611,c_3612,c_3694])).

cnf(c_3717,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3716])).

cnf(c_2426,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3386,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | X1 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2426])).

cnf(c_3488,plain,
    ( m1_subset_1(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | X0 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3386])).

cnf(c_3744,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3488])).

cnf(c_3746,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3744])).

cnf(c_3748,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3746])).

cnf(c_2425,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_3745,plain,
    ( X0 != k2_zfmisc_1(sK0,sK1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2425])).

cnf(c_3750,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_3745])).

cnf(c_5062,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(sK0,sK1)
    | k2_zfmisc_1(sK0,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_3581])).

cnf(c_5063,plain,
    ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5062])).

cnf(c_5227,plain,
    ( k2_zfmisc_1(sK0,sK1) != X0
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_2422])).

cnf(c_5653,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X0,X1)
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_5227])).

cnf(c_5655,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5653])).

cnf(c_2424,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_5654,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_2424])).

cnf(c_5656,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5654])).

cnf(c_9014,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7878,c_34,c_99,c_100,c_3315,c_3489,c_3582,c_3717,c_3721,c_3748,c_3750,c_3975,c_5063,c_5655,c_5656,c_7642])).

cnf(c_6664,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4259,c_3053])).

cnf(c_7034,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6664,c_32,c_34,c_3315,c_3721,c_3975])).

cnf(c_7043,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_7034])).

cnf(c_7792,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7043,c_34,c_99,c_100,c_3315,c_3489,c_3582,c_3717,c_3721,c_3748,c_3750,c_3975,c_5063,c_5655,c_5656,c_7642])).

cnf(c_7797,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7792,c_3061])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3063,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8668,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7797,c_3063])).

cnf(c_9016,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9014,c_8668])).

cnf(c_6428,plain,
    ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_6419,c_3057])).

cnf(c_7839,plain,
    ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_7831,c_6428])).

cnf(c_7925,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_7839,c_7860])).

cnf(c_7841,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7831,c_6419])).

cnf(c_7911,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7841,c_7860])).

cnf(c_7913,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7911,c_2])).

cnf(c_16,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_935,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_936,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_935])).

cnf(c_3043,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_3238,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3043,c_2])).

cnf(c_3525,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3376])).

cnf(c_3526,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3525])).

cnf(c_3707,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3238,c_32,c_34,c_3526])).

cnf(c_3708,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3707])).

cnf(c_5428,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5424,c_3708])).

cnf(c_7846,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7831,c_5428])).

cnf(c_14,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_837,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_838,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_837])).

cnf(c_3047,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_838])).

cnf(c_3225,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3047,c_1])).

cnf(c_3635,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3225,c_32,c_34,c_3526])).

cnf(c_3636,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3635])).

cnf(c_5429,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5424,c_3636])).

cnf(c_430,plain,
    ( sK2 != X0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_28])).

cnf(c_431,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_3463,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2421])).

cnf(c_3343,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_2422])).

cnf(c_3620,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_3343])).

cnf(c_5591,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5429,c_431,c_3463,c_3620,c_3717])).

cnf(c_7847,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7831,c_5591])).

cnf(c_7889,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7847])).

cnf(c_7892,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7846,c_7889])).

cnf(c_7893,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7892])).

cnf(c_7897,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7893,c_2])).

cnf(c_7915,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_7913,c_7897])).

cnf(c_7927,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7925,c_7915])).

cnf(c_8787,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7927,c_8668])).

cnf(c_3858,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3059,c_3063])).

cnf(c_83,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_85,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_2427,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3331,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
    | X0 != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_2427])).

cnf(c_3332,plain,
    ( X0 != k2_zfmisc_1(X1,X2)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3331])).

cnf(c_3334,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3332])).

cnf(c_3863,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3858,c_85,c_99,c_100,c_3334,c_3582])).

cnf(c_8788,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8787,c_3863])).

cnf(c_9018,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9016,c_8788])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.25/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/0.99  
% 3.25/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.25/0.99  
% 3.25/0.99  ------  iProver source info
% 3.25/0.99  
% 3.25/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.25/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.25/0.99  git: non_committed_changes: false
% 3.25/0.99  git: last_make_outside_of_git: false
% 3.25/0.99  
% 3.25/0.99  ------ 
% 3.25/0.99  
% 3.25/0.99  ------ Input Options
% 3.25/0.99  
% 3.25/0.99  --out_options                           all
% 3.25/0.99  --tptp_safe_out                         true
% 3.25/0.99  --problem_path                          ""
% 3.25/0.99  --include_path                          ""
% 3.25/0.99  --clausifier                            res/vclausify_rel
% 3.25/0.99  --clausifier_options                    --mode clausify
% 3.25/0.99  --stdin                                 false
% 3.25/0.99  --stats_out                             all
% 3.25/0.99  
% 3.25/0.99  ------ General Options
% 3.25/0.99  
% 3.25/0.99  --fof                                   false
% 3.25/0.99  --time_out_real                         305.
% 3.25/0.99  --time_out_virtual                      -1.
% 3.25/0.99  --symbol_type_check                     false
% 3.25/0.99  --clausify_out                          false
% 3.25/0.99  --sig_cnt_out                           false
% 3.25/0.99  --trig_cnt_out                          false
% 3.25/0.99  --trig_cnt_out_tolerance                1.
% 3.25/0.99  --trig_cnt_out_sk_spl                   false
% 3.25/0.99  --abstr_cl_out                          false
% 3.25/0.99  
% 3.25/0.99  ------ Global Options
% 3.25/0.99  
% 3.25/0.99  --schedule                              default
% 3.25/0.99  --add_important_lit                     false
% 3.25/0.99  --prop_solver_per_cl                    1000
% 3.25/0.99  --min_unsat_core                        false
% 3.25/0.99  --soft_assumptions                      false
% 3.25/0.99  --soft_lemma_size                       3
% 3.25/0.99  --prop_impl_unit_size                   0
% 3.25/0.99  --prop_impl_unit                        []
% 3.25/0.99  --share_sel_clauses                     true
% 3.25/0.99  --reset_solvers                         false
% 3.25/0.99  --bc_imp_inh                            [conj_cone]
% 3.25/0.99  --conj_cone_tolerance                   3.
% 3.25/0.99  --extra_neg_conj                        none
% 3.25/0.99  --large_theory_mode                     true
% 3.25/0.99  --prolific_symb_bound                   200
% 3.25/0.99  --lt_threshold                          2000
% 3.25/0.99  --clause_weak_htbl                      true
% 3.25/0.99  --gc_record_bc_elim                     false
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing Options
% 3.25/0.99  
% 3.25/0.99  --preprocessing_flag                    true
% 3.25/0.99  --time_out_prep_mult                    0.1
% 3.25/0.99  --splitting_mode                        input
% 3.25/0.99  --splitting_grd                         true
% 3.25/0.99  --splitting_cvd                         false
% 3.25/0.99  --splitting_cvd_svl                     false
% 3.25/0.99  --splitting_nvd                         32
% 3.25/0.99  --sub_typing                            true
% 3.25/0.99  --prep_gs_sim                           true
% 3.25/0.99  --prep_unflatten                        true
% 3.25/0.99  --prep_res_sim                          true
% 3.25/0.99  --prep_upred                            true
% 3.25/0.99  --prep_sem_filter                       exhaustive
% 3.25/0.99  --prep_sem_filter_out                   false
% 3.25/0.99  --pred_elim                             true
% 3.25/0.99  --res_sim_input                         true
% 3.25/0.99  --eq_ax_congr_red                       true
% 3.25/0.99  --pure_diseq_elim                       true
% 3.25/0.99  --brand_transform                       false
% 3.25/0.99  --non_eq_to_eq                          false
% 3.25/0.99  --prep_def_merge                        true
% 3.25/0.99  --prep_def_merge_prop_impl              false
% 3.25/0.99  --prep_def_merge_mbd                    true
% 3.25/0.99  --prep_def_merge_tr_red                 false
% 3.25/0.99  --prep_def_merge_tr_cl                  false
% 3.25/0.99  --smt_preprocessing                     true
% 3.25/0.99  --smt_ac_axioms                         fast
% 3.25/0.99  --preprocessed_out                      false
% 3.25/0.99  --preprocessed_stats                    false
% 3.25/0.99  
% 3.25/0.99  ------ Abstraction refinement Options
% 3.25/0.99  
% 3.25/0.99  --abstr_ref                             []
% 3.25/0.99  --abstr_ref_prep                        false
% 3.25/0.99  --abstr_ref_until_sat                   false
% 3.25/0.99  --abstr_ref_sig_restrict                funpre
% 3.25/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/0.99  --abstr_ref_under                       []
% 3.25/0.99  
% 3.25/0.99  ------ SAT Options
% 3.25/0.99  
% 3.25/0.99  --sat_mode                              false
% 3.25/0.99  --sat_fm_restart_options                ""
% 3.25/0.99  --sat_gr_def                            false
% 3.25/0.99  --sat_epr_types                         true
% 3.25/0.99  --sat_non_cyclic_types                  false
% 3.25/0.99  --sat_finite_models                     false
% 3.25/0.99  --sat_fm_lemmas                         false
% 3.25/0.99  --sat_fm_prep                           false
% 3.25/0.99  --sat_fm_uc_incr                        true
% 3.25/0.99  --sat_out_model                         small
% 3.25/0.99  --sat_out_clauses                       false
% 3.25/0.99  
% 3.25/0.99  ------ QBF Options
% 3.25/0.99  
% 3.25/0.99  --qbf_mode                              false
% 3.25/0.99  --qbf_elim_univ                         false
% 3.25/0.99  --qbf_dom_inst                          none
% 3.25/0.99  --qbf_dom_pre_inst                      false
% 3.25/0.99  --qbf_sk_in                             false
% 3.25/0.99  --qbf_pred_elim                         true
% 3.25/0.99  --qbf_split                             512
% 3.25/0.99  
% 3.25/0.99  ------ BMC1 Options
% 3.25/0.99  
% 3.25/0.99  --bmc1_incremental                      false
% 3.25/0.99  --bmc1_axioms                           reachable_all
% 3.25/0.99  --bmc1_min_bound                        0
% 3.25/0.99  --bmc1_max_bound                        -1
% 3.25/0.99  --bmc1_max_bound_default                -1
% 3.25/0.99  --bmc1_symbol_reachability              true
% 3.25/0.99  --bmc1_property_lemmas                  false
% 3.25/0.99  --bmc1_k_induction                      false
% 3.25/0.99  --bmc1_non_equiv_states                 false
% 3.25/0.99  --bmc1_deadlock                         false
% 3.25/0.99  --bmc1_ucm                              false
% 3.25/0.99  --bmc1_add_unsat_core                   none
% 3.25/0.99  --bmc1_unsat_core_children              false
% 3.25/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/0.99  --bmc1_out_stat                         full
% 3.25/0.99  --bmc1_ground_init                      false
% 3.25/0.99  --bmc1_pre_inst_next_state              false
% 3.25/0.99  --bmc1_pre_inst_state                   false
% 3.25/0.99  --bmc1_pre_inst_reach_state             false
% 3.25/0.99  --bmc1_out_unsat_core                   false
% 3.25/0.99  --bmc1_aig_witness_out                  false
% 3.25/0.99  --bmc1_verbose                          false
% 3.25/0.99  --bmc1_dump_clauses_tptp                false
% 3.25/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.25/0.99  --bmc1_dump_file                        -
% 3.25/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.25/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.25/0.99  --bmc1_ucm_extend_mode                  1
% 3.25/0.99  --bmc1_ucm_init_mode                    2
% 3.25/0.99  --bmc1_ucm_cone_mode                    none
% 3.25/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.25/0.99  --bmc1_ucm_relax_model                  4
% 3.25/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.25/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/0.99  --bmc1_ucm_layered_model                none
% 3.25/0.99  --bmc1_ucm_max_lemma_size               10
% 3.25/0.99  
% 3.25/0.99  ------ AIG Options
% 3.25/0.99  
% 3.25/0.99  --aig_mode                              false
% 3.25/0.99  
% 3.25/0.99  ------ Instantiation Options
% 3.25/0.99  
% 3.25/0.99  --instantiation_flag                    true
% 3.25/0.99  --inst_sos_flag                         false
% 3.25/0.99  --inst_sos_phase                        true
% 3.25/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/0.99  --inst_lit_sel_side                     num_symb
% 3.25/0.99  --inst_solver_per_active                1400
% 3.25/0.99  --inst_solver_calls_frac                1.
% 3.25/0.99  --inst_passive_queue_type               priority_queues
% 3.25/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/0.99  --inst_passive_queues_freq              [25;2]
% 3.25/0.99  --inst_dismatching                      true
% 3.25/0.99  --inst_eager_unprocessed_to_passive     true
% 3.25/0.99  --inst_prop_sim_given                   true
% 3.25/0.99  --inst_prop_sim_new                     false
% 3.25/0.99  --inst_subs_new                         false
% 3.25/0.99  --inst_eq_res_simp                      false
% 3.25/0.99  --inst_subs_given                       false
% 3.25/0.99  --inst_orphan_elimination               true
% 3.25/0.99  --inst_learning_loop_flag               true
% 3.25/0.99  --inst_learning_start                   3000
% 3.25/0.99  --inst_learning_factor                  2
% 3.25/0.99  --inst_start_prop_sim_after_learn       3
% 3.25/0.99  --inst_sel_renew                        solver
% 3.25/0.99  --inst_lit_activity_flag                true
% 3.25/0.99  --inst_restr_to_given                   false
% 3.25/0.99  --inst_activity_threshold               500
% 3.25/0.99  --inst_out_proof                        true
% 3.25/0.99  
% 3.25/0.99  ------ Resolution Options
% 3.25/0.99  
% 3.25/0.99  --resolution_flag                       true
% 3.25/0.99  --res_lit_sel                           adaptive
% 3.25/0.99  --res_lit_sel_side                      none
% 3.25/0.99  --res_ordering                          kbo
% 3.25/0.99  --res_to_prop_solver                    active
% 3.25/0.99  --res_prop_simpl_new                    false
% 3.25/0.99  --res_prop_simpl_given                  true
% 3.25/0.99  --res_passive_queue_type                priority_queues
% 3.25/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/0.99  --res_passive_queues_freq               [15;5]
% 3.25/0.99  --res_forward_subs                      full
% 3.25/0.99  --res_backward_subs                     full
% 3.25/0.99  --res_forward_subs_resolution           true
% 3.25/0.99  --res_backward_subs_resolution          true
% 3.25/0.99  --res_orphan_elimination                true
% 3.25/0.99  --res_time_limit                        2.
% 3.25/0.99  --res_out_proof                         true
% 3.25/0.99  
% 3.25/0.99  ------ Superposition Options
% 3.25/0.99  
% 3.25/0.99  --superposition_flag                    true
% 3.25/0.99  --sup_passive_queue_type                priority_queues
% 3.25/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.25/0.99  --demod_completeness_check              fast
% 3.25/0.99  --demod_use_ground                      true
% 3.25/0.99  --sup_to_prop_solver                    passive
% 3.25/0.99  --sup_prop_simpl_new                    true
% 3.25/0.99  --sup_prop_simpl_given                  true
% 3.25/0.99  --sup_fun_splitting                     false
% 3.25/0.99  --sup_smt_interval                      50000
% 3.25/0.99  
% 3.25/0.99  ------ Superposition Simplification Setup
% 3.25/0.99  
% 3.25/0.99  --sup_indices_passive                   []
% 3.25/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_full_bw                           [BwDemod]
% 3.25/0.99  --sup_immed_triv                        [TrivRules]
% 3.25/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_immed_bw_main                     []
% 3.25/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.99  
% 3.25/0.99  ------ Combination Options
% 3.25/0.99  
% 3.25/0.99  --comb_res_mult                         3
% 3.25/0.99  --comb_sup_mult                         2
% 3.25/0.99  --comb_inst_mult                        10
% 3.25/0.99  
% 3.25/0.99  ------ Debug Options
% 3.25/0.99  
% 3.25/0.99  --dbg_backtrace                         false
% 3.25/0.99  --dbg_dump_prop_clauses                 false
% 3.25/0.99  --dbg_dump_prop_clauses_file            -
% 3.25/0.99  --dbg_out_stat                          false
% 3.25/0.99  ------ Parsing...
% 3.25/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.25/0.99  ------ Proving...
% 3.25/0.99  ------ Problem Properties 
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  clauses                                 31
% 3.25/0.99  conjectures                             4
% 3.25/0.99  EPR                                     5
% 3.25/0.99  Horn                                    26
% 3.25/0.99  unary                                   6
% 3.25/0.99  binary                                  7
% 3.25/0.99  lits                                    90
% 3.25/0.99  lits eq                                 34
% 3.25/0.99  fd_pure                                 0
% 3.25/0.99  fd_pseudo                               0
% 3.25/0.99  fd_cond                                 4
% 3.25/0.99  fd_pseudo_cond                          0
% 3.25/0.99  AC symbols                              0
% 3.25/0.99  
% 3.25/0.99  ------ Schedule dynamic 5 is on 
% 3.25/0.99  
% 3.25/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  ------ 
% 3.25/0.99  Current options:
% 3.25/0.99  ------ 
% 3.25/0.99  
% 3.25/0.99  ------ Input Options
% 3.25/0.99  
% 3.25/0.99  --out_options                           all
% 3.25/0.99  --tptp_safe_out                         true
% 3.25/0.99  --problem_path                          ""
% 3.25/0.99  --include_path                          ""
% 3.25/0.99  --clausifier                            res/vclausify_rel
% 3.25/0.99  --clausifier_options                    --mode clausify
% 3.25/0.99  --stdin                                 false
% 3.25/0.99  --stats_out                             all
% 3.25/0.99  
% 3.25/0.99  ------ General Options
% 3.25/0.99  
% 3.25/0.99  --fof                                   false
% 3.25/0.99  --time_out_real                         305.
% 3.25/0.99  --time_out_virtual                      -1.
% 3.25/0.99  --symbol_type_check                     false
% 3.25/0.99  --clausify_out                          false
% 3.25/0.99  --sig_cnt_out                           false
% 3.25/0.99  --trig_cnt_out                          false
% 3.25/0.99  --trig_cnt_out_tolerance                1.
% 3.25/0.99  --trig_cnt_out_sk_spl                   false
% 3.25/0.99  --abstr_cl_out                          false
% 3.25/0.99  
% 3.25/0.99  ------ Global Options
% 3.25/0.99  
% 3.25/0.99  --schedule                              default
% 3.25/0.99  --add_important_lit                     false
% 3.25/0.99  --prop_solver_per_cl                    1000
% 3.25/0.99  --min_unsat_core                        false
% 3.25/0.99  --soft_assumptions                      false
% 3.25/0.99  --soft_lemma_size                       3
% 3.25/0.99  --prop_impl_unit_size                   0
% 3.25/0.99  --prop_impl_unit                        []
% 3.25/0.99  --share_sel_clauses                     true
% 3.25/0.99  --reset_solvers                         false
% 3.25/0.99  --bc_imp_inh                            [conj_cone]
% 3.25/0.99  --conj_cone_tolerance                   3.
% 3.25/0.99  --extra_neg_conj                        none
% 3.25/0.99  --large_theory_mode                     true
% 3.25/0.99  --prolific_symb_bound                   200
% 3.25/0.99  --lt_threshold                          2000
% 3.25/0.99  --clause_weak_htbl                      true
% 3.25/0.99  --gc_record_bc_elim                     false
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing Options
% 3.25/0.99  
% 3.25/0.99  --preprocessing_flag                    true
% 3.25/0.99  --time_out_prep_mult                    0.1
% 3.25/0.99  --splitting_mode                        input
% 3.25/0.99  --splitting_grd                         true
% 3.25/0.99  --splitting_cvd                         false
% 3.25/0.99  --splitting_cvd_svl                     false
% 3.25/0.99  --splitting_nvd                         32
% 3.25/0.99  --sub_typing                            true
% 3.25/0.99  --prep_gs_sim                           true
% 3.25/0.99  --prep_unflatten                        true
% 3.25/0.99  --prep_res_sim                          true
% 3.25/0.99  --prep_upred                            true
% 3.25/0.99  --prep_sem_filter                       exhaustive
% 3.25/0.99  --prep_sem_filter_out                   false
% 3.25/0.99  --pred_elim                             true
% 3.25/0.99  --res_sim_input                         true
% 3.25/0.99  --eq_ax_congr_red                       true
% 3.25/0.99  --pure_diseq_elim                       true
% 3.25/0.99  --brand_transform                       false
% 3.25/0.99  --non_eq_to_eq                          false
% 3.25/0.99  --prep_def_merge                        true
% 3.25/0.99  --prep_def_merge_prop_impl              false
% 3.25/0.99  --prep_def_merge_mbd                    true
% 3.25/0.99  --prep_def_merge_tr_red                 false
% 3.25/0.99  --prep_def_merge_tr_cl                  false
% 3.25/0.99  --smt_preprocessing                     true
% 3.25/0.99  --smt_ac_axioms                         fast
% 3.25/0.99  --preprocessed_out                      false
% 3.25/0.99  --preprocessed_stats                    false
% 3.25/0.99  
% 3.25/0.99  ------ Abstraction refinement Options
% 3.25/0.99  
% 3.25/0.99  --abstr_ref                             []
% 3.25/0.99  --abstr_ref_prep                        false
% 3.25/0.99  --abstr_ref_until_sat                   false
% 3.25/0.99  --abstr_ref_sig_restrict                funpre
% 3.25/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/0.99  --abstr_ref_under                       []
% 3.25/0.99  
% 3.25/0.99  ------ SAT Options
% 3.25/0.99  
% 3.25/0.99  --sat_mode                              false
% 3.25/0.99  --sat_fm_restart_options                ""
% 3.25/0.99  --sat_gr_def                            false
% 3.25/0.99  --sat_epr_types                         true
% 3.25/0.99  --sat_non_cyclic_types                  false
% 3.25/0.99  --sat_finite_models                     false
% 3.25/0.99  --sat_fm_lemmas                         false
% 3.25/0.99  --sat_fm_prep                           false
% 3.25/0.99  --sat_fm_uc_incr                        true
% 3.25/0.99  --sat_out_model                         small
% 3.25/0.99  --sat_out_clauses                       false
% 3.25/0.99  
% 3.25/0.99  ------ QBF Options
% 3.25/0.99  
% 3.25/0.99  --qbf_mode                              false
% 3.25/0.99  --qbf_elim_univ                         false
% 3.25/0.99  --qbf_dom_inst                          none
% 3.25/0.99  --qbf_dom_pre_inst                      false
% 3.25/0.99  --qbf_sk_in                             false
% 3.25/0.99  --qbf_pred_elim                         true
% 3.25/0.99  --qbf_split                             512
% 3.25/0.99  
% 3.25/0.99  ------ BMC1 Options
% 3.25/0.99  
% 3.25/0.99  --bmc1_incremental                      false
% 3.25/0.99  --bmc1_axioms                           reachable_all
% 3.25/0.99  --bmc1_min_bound                        0
% 3.25/0.99  --bmc1_max_bound                        -1
% 3.25/0.99  --bmc1_max_bound_default                -1
% 3.25/0.99  --bmc1_symbol_reachability              true
% 3.25/0.99  --bmc1_property_lemmas                  false
% 3.25/0.99  --bmc1_k_induction                      false
% 3.25/0.99  --bmc1_non_equiv_states                 false
% 3.25/0.99  --bmc1_deadlock                         false
% 3.25/0.99  --bmc1_ucm                              false
% 3.25/0.99  --bmc1_add_unsat_core                   none
% 3.25/0.99  --bmc1_unsat_core_children              false
% 3.25/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/0.99  --bmc1_out_stat                         full
% 3.25/0.99  --bmc1_ground_init                      false
% 3.25/0.99  --bmc1_pre_inst_next_state              false
% 3.25/0.99  --bmc1_pre_inst_state                   false
% 3.25/0.99  --bmc1_pre_inst_reach_state             false
% 3.25/0.99  --bmc1_out_unsat_core                   false
% 3.25/0.99  --bmc1_aig_witness_out                  false
% 3.25/0.99  --bmc1_verbose                          false
% 3.25/0.99  --bmc1_dump_clauses_tptp                false
% 3.25/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.25/0.99  --bmc1_dump_file                        -
% 3.25/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.25/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.25/0.99  --bmc1_ucm_extend_mode                  1
% 3.25/0.99  --bmc1_ucm_init_mode                    2
% 3.25/0.99  --bmc1_ucm_cone_mode                    none
% 3.25/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.25/0.99  --bmc1_ucm_relax_model                  4
% 3.25/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.25/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/0.99  --bmc1_ucm_layered_model                none
% 3.25/0.99  --bmc1_ucm_max_lemma_size               10
% 3.25/0.99  
% 3.25/0.99  ------ AIG Options
% 3.25/0.99  
% 3.25/0.99  --aig_mode                              false
% 3.25/0.99  
% 3.25/0.99  ------ Instantiation Options
% 3.25/0.99  
% 3.25/0.99  --instantiation_flag                    true
% 3.25/0.99  --inst_sos_flag                         false
% 3.25/0.99  --inst_sos_phase                        true
% 3.25/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/0.99  --inst_lit_sel_side                     none
% 3.25/0.99  --inst_solver_per_active                1400
% 3.25/0.99  --inst_solver_calls_frac                1.
% 3.25/0.99  --inst_passive_queue_type               priority_queues
% 3.25/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/0.99  --inst_passive_queues_freq              [25;2]
% 3.25/0.99  --inst_dismatching                      true
% 3.25/0.99  --inst_eager_unprocessed_to_passive     true
% 3.25/0.99  --inst_prop_sim_given                   true
% 3.25/0.99  --inst_prop_sim_new                     false
% 3.25/0.99  --inst_subs_new                         false
% 3.25/0.99  --inst_eq_res_simp                      false
% 3.25/0.99  --inst_subs_given                       false
% 3.25/0.99  --inst_orphan_elimination               true
% 3.25/0.99  --inst_learning_loop_flag               true
% 3.25/0.99  --inst_learning_start                   3000
% 3.25/0.99  --inst_learning_factor                  2
% 3.25/0.99  --inst_start_prop_sim_after_learn       3
% 3.25/0.99  --inst_sel_renew                        solver
% 3.25/0.99  --inst_lit_activity_flag                true
% 3.25/0.99  --inst_restr_to_given                   false
% 3.25/0.99  --inst_activity_threshold               500
% 3.25/0.99  --inst_out_proof                        true
% 3.25/0.99  
% 3.25/0.99  ------ Resolution Options
% 3.25/0.99  
% 3.25/0.99  --resolution_flag                       false
% 3.25/0.99  --res_lit_sel                           adaptive
% 3.25/0.99  --res_lit_sel_side                      none
% 3.25/0.99  --res_ordering                          kbo
% 3.25/0.99  --res_to_prop_solver                    active
% 3.25/0.99  --res_prop_simpl_new                    false
% 3.25/0.99  --res_prop_simpl_given                  true
% 3.25/0.99  --res_passive_queue_type                priority_queues
% 3.25/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/0.99  --res_passive_queues_freq               [15;5]
% 3.25/0.99  --res_forward_subs                      full
% 3.25/0.99  --res_backward_subs                     full
% 3.25/0.99  --res_forward_subs_resolution           true
% 3.25/0.99  --res_backward_subs_resolution          true
% 3.25/0.99  --res_orphan_elimination                true
% 3.25/0.99  --res_time_limit                        2.
% 3.25/0.99  --res_out_proof                         true
% 3.25/0.99  
% 3.25/0.99  ------ Superposition Options
% 3.25/0.99  
% 3.25/0.99  --superposition_flag                    true
% 3.25/0.99  --sup_passive_queue_type                priority_queues
% 3.25/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.25/0.99  --demod_completeness_check              fast
% 3.25/0.99  --demod_use_ground                      true
% 3.25/0.99  --sup_to_prop_solver                    passive
% 3.25/0.99  --sup_prop_simpl_new                    true
% 3.25/0.99  --sup_prop_simpl_given                  true
% 3.25/0.99  --sup_fun_splitting                     false
% 3.25/0.99  --sup_smt_interval                      50000
% 3.25/0.99  
% 3.25/0.99  ------ Superposition Simplification Setup
% 3.25/0.99  
% 3.25/0.99  --sup_indices_passive                   []
% 3.25/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_full_bw                           [BwDemod]
% 3.25/0.99  --sup_immed_triv                        [TrivRules]
% 3.25/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_immed_bw_main                     []
% 3.25/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/0.99  
% 3.25/0.99  ------ Combination Options
% 3.25/0.99  
% 3.25/0.99  --comb_res_mult                         3
% 3.25/0.99  --comb_sup_mult                         2
% 3.25/0.99  --comb_inst_mult                        10
% 3.25/0.99  
% 3.25/0.99  ------ Debug Options
% 3.25/0.99  
% 3.25/0.99  --dbg_backtrace                         false
% 3.25/0.99  --dbg_dump_prop_clauses                 false
% 3.25/0.99  --dbg_dump_prop_clauses_file            -
% 3.25/0.99  --dbg_out_stat                          false
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  ------ Proving...
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  % SZS status Theorem for theBenchmark.p
% 3.25/0.99  
% 3.25/0.99   Resolution empty clause
% 3.25/0.99  
% 3.25/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.25/0.99  
% 3.25/0.99  fof(f2,axiom,(
% 3.25/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f36,plain,(
% 3.25/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.25/0.99    inference(nnf_transformation,[],[f2])).
% 3.25/0.99  
% 3.25/0.99  fof(f37,plain,(
% 3.25/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.25/0.99    inference(flattening,[],[f36])).
% 3.25/0.99  
% 3.25/0.99  fof(f46,plain,(
% 3.25/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.25/0.99    inference(cnf_transformation,[],[f37])).
% 3.25/0.99  
% 3.25/0.99  fof(f75,plain,(
% 3.25/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.25/0.99    inference(equality_resolution,[],[f46])).
% 3.25/0.99  
% 3.25/0.99  fof(f15,conjecture,(
% 3.25/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f16,negated_conjecture,(
% 3.25/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.25/0.99    inference(negated_conjecture,[],[f15])).
% 3.25/0.99  
% 3.25/0.99  fof(f34,plain,(
% 3.25/0.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.25/0.99    inference(ennf_transformation,[],[f16])).
% 3.25/0.99  
% 3.25/0.99  fof(f35,plain,(
% 3.25/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.25/0.99    inference(flattening,[],[f34])).
% 3.25/0.99  
% 3.25/0.99  fof(f41,plain,(
% 3.25/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.25/0.99    introduced(choice_axiom,[])).
% 3.25/0.99  
% 3.25/0.99  fof(f42,plain,(
% 3.25/0.99    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.25/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f41])).
% 3.25/0.99  
% 3.25/0.99  fof(f72,plain,(
% 3.25/0.99    r1_tarski(sK2,sK0)),
% 3.25/0.99    inference(cnf_transformation,[],[f42])).
% 3.25/0.99  
% 3.25/0.99  fof(f11,axiom,(
% 3.25/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f26,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.99    inference(ennf_transformation,[],[f11])).
% 3.25/0.99  
% 3.25/0.99  fof(f27,plain,(
% 3.25/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.99    inference(flattening,[],[f26])).
% 3.25/0.99  
% 3.25/0.99  fof(f40,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.99    inference(nnf_transformation,[],[f27])).
% 3.25/0.99  
% 3.25/0.99  fof(f57,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f40])).
% 3.25/0.99  
% 3.25/0.99  fof(f70,plain,(
% 3.25/0.99    v1_funct_2(sK3,sK0,sK1)),
% 3.25/0.99    inference(cnf_transformation,[],[f42])).
% 3.25/0.99  
% 3.25/0.99  fof(f71,plain,(
% 3.25/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.25/0.99    inference(cnf_transformation,[],[f42])).
% 3.25/0.99  
% 3.25/0.99  fof(f10,axiom,(
% 3.25/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f25,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.99    inference(ennf_transformation,[],[f10])).
% 3.25/0.99  
% 3.25/0.99  fof(f56,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f25])).
% 3.25/0.99  
% 3.25/0.99  fof(f8,axiom,(
% 3.25/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f22,plain,(
% 3.25/0.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.25/0.99    inference(ennf_transformation,[],[f8])).
% 3.25/0.99  
% 3.25/0.99  fof(f23,plain,(
% 3.25/0.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.25/0.99    inference(flattening,[],[f22])).
% 3.25/0.99  
% 3.25/0.99  fof(f54,plain,(
% 3.25/0.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f23])).
% 3.25/0.99  
% 3.25/0.99  fof(f3,axiom,(
% 3.25/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f38,plain,(
% 3.25/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.25/0.99    inference(nnf_transformation,[],[f3])).
% 3.25/0.99  
% 3.25/0.99  fof(f47,plain,(
% 3.25/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f38])).
% 3.25/0.99  
% 3.25/0.99  fof(f4,axiom,(
% 3.25/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f19,plain,(
% 3.25/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.25/0.99    inference(ennf_transformation,[],[f4])).
% 3.25/0.99  
% 3.25/0.99  fof(f49,plain,(
% 3.25/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f19])).
% 3.25/0.99  
% 3.25/0.99  fof(f48,plain,(
% 3.25/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f38])).
% 3.25/0.99  
% 3.25/0.99  fof(f6,axiom,(
% 3.25/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f52,plain,(
% 3.25/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f6])).
% 3.25/0.99  
% 3.25/0.99  fof(f14,axiom,(
% 3.25/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f32,plain,(
% 3.25/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.25/0.99    inference(ennf_transformation,[],[f14])).
% 3.25/0.99  
% 3.25/0.99  fof(f33,plain,(
% 3.25/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.25/0.99    inference(flattening,[],[f32])).
% 3.25/0.99  
% 3.25/0.99  fof(f68,plain,(
% 3.25/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f33])).
% 3.25/0.99  
% 3.25/0.99  fof(f13,axiom,(
% 3.25/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f30,plain,(
% 3.25/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.25/0.99    inference(ennf_transformation,[],[f13])).
% 3.25/0.99  
% 3.25/0.99  fof(f31,plain,(
% 3.25/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.25/0.99    inference(flattening,[],[f30])).
% 3.25/0.99  
% 3.25/0.99  fof(f65,plain,(
% 3.25/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f31])).
% 3.25/0.99  
% 3.25/0.99  fof(f69,plain,(
% 3.25/0.99    v1_funct_1(sK3)),
% 3.25/0.99    inference(cnf_transformation,[],[f42])).
% 3.25/0.99  
% 3.25/0.99  fof(f12,axiom,(
% 3.25/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f28,plain,(
% 3.25/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.25/0.99    inference(ennf_transformation,[],[f12])).
% 3.25/0.99  
% 3.25/0.99  fof(f29,plain,(
% 3.25/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.25/0.99    inference(flattening,[],[f28])).
% 3.25/0.99  
% 3.25/0.99  fof(f63,plain,(
% 3.25/0.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f29])).
% 3.25/0.99  
% 3.25/0.99  fof(f7,axiom,(
% 3.25/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f21,plain,(
% 3.25/0.99    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 3.25/0.99    inference(ennf_transformation,[],[f7])).
% 3.25/0.99  
% 3.25/0.99  fof(f53,plain,(
% 3.25/0.99    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f21])).
% 3.25/0.99  
% 3.25/0.99  fof(f67,plain,(
% 3.25/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f33])).
% 3.25/0.99  
% 3.25/0.99  fof(f74,plain,(
% 3.25/0.99    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.25/0.99    inference(cnf_transformation,[],[f42])).
% 3.25/0.99  
% 3.25/0.99  fof(f9,axiom,(
% 3.25/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f17,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.25/0.99    inference(pure_predicate_removal,[],[f9])).
% 3.25/0.99  
% 3.25/0.99  fof(f24,plain,(
% 3.25/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/0.99    inference(ennf_transformation,[],[f17])).
% 3.25/0.99  
% 3.25/0.99  fof(f55,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f24])).
% 3.25/0.99  
% 3.25/0.99  fof(f5,axiom,(
% 3.25/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f20,plain,(
% 3.25/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.25/0.99    inference(ennf_transformation,[],[f5])).
% 3.25/0.99  
% 3.25/0.99  fof(f39,plain,(
% 3.25/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.25/0.99    inference(nnf_transformation,[],[f20])).
% 3.25/0.99  
% 3.25/0.99  fof(f50,plain,(
% 3.25/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f39])).
% 3.25/0.99  
% 3.25/0.99  fof(f64,plain,(
% 3.25/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f29])).
% 3.25/0.99  
% 3.25/0.99  fof(f73,plain,(
% 3.25/0.99    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.25/0.99    inference(cnf_transformation,[],[f42])).
% 3.25/0.99  
% 3.25/0.99  fof(f58,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f40])).
% 3.25/0.99  
% 3.25/0.99  fof(f81,plain,(
% 3.25/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.25/0.99    inference(equality_resolution,[],[f58])).
% 3.25/0.99  
% 3.25/0.99  fof(f45,plain,(
% 3.25/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.25/0.99    inference(cnf_transformation,[],[f37])).
% 3.25/0.99  
% 3.25/0.99  fof(f76,plain,(
% 3.25/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.25/0.99    inference(equality_resolution,[],[f45])).
% 3.25/0.99  
% 3.25/0.99  fof(f44,plain,(
% 3.25/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f37])).
% 3.25/0.99  
% 3.25/0.99  fof(f61,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f40])).
% 3.25/0.99  
% 3.25/0.99  fof(f79,plain,(
% 3.25/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.25/0.99    inference(equality_resolution,[],[f61])).
% 3.25/0.99  
% 3.25/0.99  fof(f1,axiom,(
% 3.25/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.25/0.99  
% 3.25/0.99  fof(f18,plain,(
% 3.25/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.25/0.99    inference(ennf_transformation,[],[f1])).
% 3.25/0.99  
% 3.25/0.99  fof(f43,plain,(
% 3.25/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.25/0.99    inference(cnf_transformation,[],[f18])).
% 3.25/0.99  
% 3.25/0.99  fof(f60,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f40])).
% 3.25/0.99  
% 3.25/0.99  fof(f80,plain,(
% 3.25/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.25/0.99    inference(equality_resolution,[],[f60])).
% 3.25/0.99  
% 3.25/0.99  fof(f62,plain,(
% 3.25/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.99    inference(cnf_transformation,[],[f40])).
% 3.25/0.99  
% 3.25/0.99  fof(f77,plain,(
% 3.25/0.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/0.99    inference(equality_resolution,[],[f62])).
% 3.25/0.99  
% 3.25/0.99  fof(f78,plain,(
% 3.25/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.25/0.99    inference(equality_resolution,[],[f77])).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1,plain,
% 3.25/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.25/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_28,negated_conjecture,
% 3.25/0.99      ( r1_tarski(sK2,sK0) ),
% 3.25/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3052,plain,
% 3.25/0.99      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_19,plain,
% 3.25/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.25/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.25/0.99      | k1_xboole_0 = X2 ),
% 3.25/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_30,negated_conjecture,
% 3.25/0.99      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.25/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1010,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.25/0.99      | sK3 != X0
% 3.25/0.99      | sK1 != X2
% 3.25/0.99      | sK0 != X1
% 3.25/0.99      | k1_xboole_0 = X2 ),
% 3.25/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1011,plain,
% 3.25/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.25/0.99      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.25/0.99      | k1_xboole_0 = sK1 ),
% 3.25/0.99      inference(unflattening,[status(thm)],[c_1010]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_29,negated_conjecture,
% 3.25/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.25/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1013,plain,
% 3.25/0.99      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.25/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1011,c_29]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3051,plain,
% 3.25/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_13,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.25/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3057,plain,
% 3.25/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.25/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4149,plain,
% 3.25/0.99      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_3051,c_3057]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4259,plain,
% 3.25/0.99      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_1013,c_4149]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_11,plain,
% 3.25/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.25/0.99      | ~ v1_relat_1(X1)
% 3.25/0.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.25/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3058,plain,
% 3.25/0.99      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.25/0.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.25/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4438,plain,
% 3.25/0.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.25/0.99      | sK1 = k1_xboole_0
% 3.25/0.99      | r1_tarski(X0,sK0) != iProver_top
% 3.25/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_4259,c_3058]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_34,plain,
% 3.25/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.25/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3314,plain,
% 3.25/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.25/0.99      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3315,plain,
% 3.25/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.25/0.99      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_3314]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_6,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.25/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4,plain,
% 3.25/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.25/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_222,plain,
% 3.25/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.25/0.99      inference(prop_impl,[status(thm)],[c_4]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_223,plain,
% 3.25/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.25/0.99      inference(renaming,[status(thm)],[c_222]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_279,plain,
% 3.25/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.25/0.99      inference(bin_hyper_res,[status(thm)],[c_6,c_223]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3326,plain,
% 3.25/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.25/0.99      | v1_relat_1(X0)
% 3.25/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_279]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3720,plain,
% 3.25/0.99      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 3.25/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.25/0.99      | v1_relat_1(sK3) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_3326]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3721,plain,
% 3.25/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.25/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.25/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_3720]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_9,plain,
% 3.25/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.25/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3974,plain,
% 3.25/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3975,plain,
% 3.25/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_3974]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4674,plain,
% 3.25/0.99      ( r1_tarski(X0,sK0) != iProver_top
% 3.25/0.99      | sK1 = k1_xboole_0
% 3.25/0.99      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_4438,c_34,c_3315,c_3721,c_3975]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4675,plain,
% 3.25/0.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.25/0.99      | sK1 = k1_xboole_0
% 3.25/0.99      | r1_tarski(X0,sK0) != iProver_top ),
% 3.25/0.99      inference(renaming,[status(thm)],[c_4674]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4684,plain,
% 3.25/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_3052,c_4675]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_23,plain,
% 3.25/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.25/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.25/0.99      | ~ v1_funct_1(X0)
% 3.25/0.99      | ~ v1_relat_1(X0) ),
% 3.25/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3053,plain,
% 3.25/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.25/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.25/0.99      | v1_funct_1(X0) != iProver_top
% 3.25/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_6665,plain,
% 3.25/0.99      ( sK1 = k1_xboole_0
% 3.25/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.25/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.25/0.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.25/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_4684,c_3053]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_22,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.99      | ~ v1_funct_1(X0)
% 3.25/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.25/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3054,plain,
% 3.25/0.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.25/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.25/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5246,plain,
% 3.25/0.99      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.25/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_3051,c_3054]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_31,negated_conjecture,
% 3.25/0.99      ( v1_funct_1(sK3) ),
% 3.25/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3396,plain,
% 3.25/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.25/0.99      | ~ v1_funct_1(sK3)
% 3.25/0.99      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3550,plain,
% 3.25/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.25/0.99      | ~ v1_funct_1(sK3)
% 3.25/0.99      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_3396]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5424,plain,
% 3.25/0.99      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_5246,c_31,c_29,c_3550]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_21,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.99      | ~ v1_funct_1(X0)
% 3.25/0.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.25/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3055,plain,
% 3.25/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.25/0.99      | v1_funct_1(X0) != iProver_top
% 3.25/0.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4487,plain,
% 3.25/0.99      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.25/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_3051,c_3055]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_32,plain,
% 3.25/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3376,plain,
% 3.25/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.25/0.99      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.25/0.99      | ~ v1_funct_1(sK3) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3811,plain,
% 3.25/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.25/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.25/0.99      | ~ v1_funct_1(sK3) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_3376]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3812,plain,
% 3.25/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.25/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.25/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_3811]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_4666,plain,
% 3.25/0.99      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_4487,c_32,c_34,c_3812]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5433,plain,
% 3.25/0.99      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_5424,c_4666]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7179,plain,
% 3.25/0.99      ( sK1 = k1_xboole_0
% 3.25/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.25/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.25/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.25/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_6665,c_5433]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7183,plain,
% 3.25/0.99      ( sK1 = k1_xboole_0
% 3.25/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.25/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),k1_xboole_0) != iProver_top
% 3.25/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_1,c_7179]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_10,plain,
% 3.25/0.99      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 3.25/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3059,plain,
% 3.25/0.99      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 3.25/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3049,plain,
% 3.25/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.25/0.99      | v1_relat_1(X1) != iProver_top
% 3.25/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_279]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5808,plain,
% 3.25/0.99      ( v1_relat_1(X0) != iProver_top
% 3.25/0.99      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_3059,c_3049]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_24,plain,
% 3.25/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.25/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.25/0.99      | ~ v1_funct_1(X0)
% 3.25/0.99      | ~ v1_relat_1(X0) ),
% 3.25/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_26,negated_conjecture,
% 3.25/0.99      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.25/0.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.25/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.25/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1021,plain,
% 3.25/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.25/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.25/0.99      | ~ v1_funct_1(X0)
% 3.25/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.25/0.99      | ~ v1_relat_1(X0)
% 3.25/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.25/0.99      | k1_relat_1(X0) != sK2
% 3.25/0.99      | sK1 != X1 ),
% 3.25/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_26]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1022,plain,
% 3.25/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.25/0.99      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.25/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.25/0.99      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.25/0.99      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.25/0.99      inference(unflattening,[status(thm)],[c_1021]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_12,plain,
% 3.25/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.25/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_8,plain,
% 3.25/0.99      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.25/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_374,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 3.25/0.99      | ~ v1_relat_1(X0) ),
% 3.25/0.99      inference(resolution,[status(thm)],[c_12,c_8]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_1034,plain,
% 3.25/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.25/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.25/0.99      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.25/0.99      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.25/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_1022,c_374]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3039,plain,
% 3.25/0.99      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.25/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.25/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top
% 3.25/0.99      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_1034]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5430,plain,
% 3.25/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.25/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.25/0.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.25/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_5424,c_3039]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5456,plain,
% 3.25/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.25/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.25/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.25/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5430,c_5433]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7583,plain,
% 3.25/0.99      ( sK1 = k1_xboole_0
% 3.25/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.25/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_4684,c_5456]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7590,plain,
% 3.25/0.99      ( sK1 = k1_xboole_0
% 3.25/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 3.25/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_7179,c_7583]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_20,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/0.99      | ~ v1_funct_1(X0) ),
% 3.25/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3056,plain,
% 3.25/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.25/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.25/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5891,plain,
% 3.25/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.25/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_5424,c_3056]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_6419,plain,
% 3.25/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_5891,c_32,c_34]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3048,plain,
% 3.25/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.25/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.25/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_6429,plain,
% 3.25/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
% 3.25/0.99      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_6419,c_3048]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3061,plain,
% 3.25/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.25/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_6426,plain,
% 3.25/0.99      ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_6419,c_3061]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_6528,plain,
% 3.25/0.99      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 3.25/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_6426,c_3049]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_6562,plain,
% 3.25/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_6429,c_3975,c_6528]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7640,plain,
% 3.25/0.99      ( sK1 = k1_xboole_0 | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.25/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_7590,c_6562]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7642,plain,
% 3.25/0.99      ( sK1 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_5808,c_7640]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7831,plain,
% 3.25/0.99      ( sK1 = k1_xboole_0 ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_7183,c_34,c_3315,c_3721,c_3975,c_7642]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7853,plain,
% 3.25/0.99      ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_7831,c_4149]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_27,negated_conjecture,
% 3.25/0.99      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.25/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7859,plain,
% 3.25/0.99      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_7831,c_27]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7860,plain,
% 3.25/0.99      ( sK0 = k1_xboole_0 ),
% 3.25/0.99      inference(equality_resolution_simp,[status(thm)],[c_7859]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7876,plain,
% 3.25/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 3.25/0.99      inference(light_normalisation,[status(thm)],[c_7853,c_7860]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_18,plain,
% 3.25/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.25/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.25/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.25/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_954,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.25/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.25/0.99      | sK3 != X0
% 3.25/0.99      | sK1 != X1
% 3.25/0.99      | sK0 != k1_xboole_0 ),
% 3.25/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_955,plain,
% 3.25/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.25/0.99      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.25/0.99      | sK0 != k1_xboole_0 ),
% 3.25/0.99      inference(unflattening,[status(thm)],[c_954]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3042,plain,
% 3.25/0.99      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.25/0.99      | sK0 != k1_xboole_0
% 3.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_955]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2,plain,
% 3.25/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.25/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3122,plain,
% 3.25/0.99      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.25/0.99      | sK0 != k1_xboole_0
% 3.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_3042,c_2]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7856,plain,
% 3.25/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 3.25/0.99      | sK0 != k1_xboole_0
% 3.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_7831,c_3122]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7866,plain,
% 3.25/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 3.25/0.99      | k1_xboole_0 != k1_xboole_0
% 3.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/0.99      inference(light_normalisation,[status(thm)],[c_7856,c_7860]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7867,plain,
% 3.25/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 3.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/0.99      inference(equality_resolution_simp,[status(thm)],[c_7866]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7878,plain,
% 3.25/0.99      ( k1_relat_1(sK3) = k1_xboole_0
% 3.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_7876,c_7867]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3,plain,
% 3.25/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.25/0.99      | k1_xboole_0 = X0
% 3.25/0.99      | k1_xboole_0 = X1 ),
% 3.25/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_99,plain,
% 3.25/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.25/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_100,plain,
% 3.25/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2421,plain,( X0 = X0 ),theory(equality) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3489,plain,
% 3.25/0.99      ( sK3 = sK3 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_2421]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2422,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3581,plain,
% 3.25/0.99      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_2422]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3582,plain,
% 3.25/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.25/0.99      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.25/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_3581]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_15,plain,
% 3.25/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.25/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.25/0.99      | k1_xboole_0 = X1
% 3.25/0.99      | k1_xboole_0 = X0 ),
% 3.25/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_889,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.25/0.99      | sK3 != X0
% 3.25/0.99      | sK1 != k1_xboole_0
% 3.25/0.99      | sK0 != X1
% 3.25/0.99      | k1_xboole_0 = X0
% 3.25/0.99      | k1_xboole_0 = X1 ),
% 3.25/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_30]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_890,plain,
% 3.25/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 3.25/0.99      | sK1 != k1_xboole_0
% 3.25/0.99      | k1_xboole_0 = sK3
% 3.25/0.99      | k1_xboole_0 = sK0 ),
% 3.25/0.99      inference(unflattening,[status(thm)],[c_889]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3045,plain,
% 3.25/0.99      ( sK1 != k1_xboole_0
% 3.25/0.99      | k1_xboole_0 = sK3
% 3.25/0.99      | k1_xboole_0 = sK0
% 3.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_890]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3129,plain,
% 3.25/0.99      ( sK3 = k1_xboole_0
% 3.25/0.99      | sK1 != k1_xboole_0
% 3.25/0.99      | sK0 = k1_xboole_0
% 3.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_3045,c_1]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3341,plain,
% 3.25/0.99      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_2422]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3611,plain,
% 3.25/0.99      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_3341]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3612,plain,
% 3.25/0.99      ( sK0 = sK0 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_2421]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3693,plain,
% 3.25/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_2422]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3694,plain,
% 3.25/0.99      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_3693]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3716,plain,
% 3.25/0.99      ( sK0 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_3129,c_27,c_99,c_100,c_3611,c_3612,c_3694]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3717,plain,
% 3.25/0.99      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 3.25/0.99      inference(renaming,[status(thm)],[c_3716]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2426,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.25/0.99      theory(equality) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3386,plain,
% 3.25/0.99      ( m1_subset_1(X0,X1)
% 3.25/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.25/0.99      | X1 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 3.25/0.99      | X0 != sK3 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_2426]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3488,plain,
% 3.25/0.99      ( m1_subset_1(sK3,X0)
% 3.25/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.25/0.99      | X0 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 3.25/0.99      | sK3 != sK3 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_3386]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3744,plain,
% 3.25/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(X0))
% 3.25/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.25/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 3.25/0.99      | sK3 != sK3 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_3488]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3746,plain,
% 3.25/0.99      ( k1_zfmisc_1(X0) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 3.25/0.99      | sK3 != sK3
% 3.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top
% 3.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_3744]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3748,plain,
% 3.25/0.99      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 3.25/0.99      | sK3 != sK3
% 3.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_3746]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2425,plain,
% 3.25/0.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.25/0.99      theory(equality) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3745,plain,
% 3.25/0.99      ( X0 != k2_zfmisc_1(sK0,sK1)
% 3.25/0.99      | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_2425]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3750,plain,
% 3.25/0.99      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 3.25/0.99      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_3745]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5062,plain,
% 3.25/0.99      ( X0 != X1 | X0 = k2_zfmisc_1(sK0,sK1) | k2_zfmisc_1(sK0,sK1) != X1 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_3581]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5063,plain,
% 3.25/0.99      ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
% 3.25/0.99      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
% 3.25/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_5062]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5227,plain,
% 3.25/0.99      ( k2_zfmisc_1(sK0,sK1) != X0
% 3.25/0.99      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 3.25/0.99      | k1_xboole_0 != X0 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_2422]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5653,plain,
% 3.25/0.99      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X0,X1)
% 3.25/0.99      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 3.25/0.99      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_5227]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5655,plain,
% 3.25/0.99      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.25/0.99      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 3.25/0.99      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_5653]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2424,plain,
% 3.25/0.99      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 3.25/0.99      theory(equality) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5654,plain,
% 3.25/0.99      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1) | sK1 != X1 | sK0 != X0 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_2424]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5656,plain,
% 3.25/0.99      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.25/0.99      | sK1 != k1_xboole_0
% 3.25/0.99      | sK0 != k1_xboole_0 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_5654]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_9014,plain,
% 3.25/0.99      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_7878,c_34,c_99,c_100,c_3315,c_3489,c_3582,c_3717,c_3721,
% 3.25/0.99                 c_3748,c_3750,c_3975,c_5063,c_5655,c_5656,c_7642]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_6664,plain,
% 3.25/0.99      ( sK1 = k1_xboole_0
% 3.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
% 3.25/0.99      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.25/0.99      | v1_funct_1(sK3) != iProver_top
% 3.25/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_4259,c_3053]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7034,plain,
% 3.25/0.99      ( sK1 = k1_xboole_0
% 3.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
% 3.25/0.99      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_6664,c_32,c_34,c_3315,c_3721,c_3975]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7043,plain,
% 3.25/0.99      ( sK1 = k1_xboole_0
% 3.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.25/0.99      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_1,c_7034]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7792,plain,
% 3.25/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_7043,c_34,c_99,c_100,c_3315,c_3489,c_3582,c_3717,c_3721,
% 3.25/0.99                 c_3748,c_3750,c_3975,c_5063,c_5655,c_5656,c_7642]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7797,plain,
% 3.25/0.99      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_7792,c_3061]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_0,plain,
% 3.25/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.25/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3063,plain,
% 3.25/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_8668,plain,
% 3.25/0.99      ( sK3 = k1_xboole_0 ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_7797,c_3063]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_9016,plain,
% 3.25/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.25/0.99      inference(light_normalisation,[status(thm)],[c_9014,c_8668]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_6428,plain,
% 3.25/0.99      ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_6419,c_3057]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7839,plain,
% 3.25/0.99      ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_7831,c_6428]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7925,plain,
% 3.25/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.25/0.99      inference(light_normalisation,[status(thm)],[c_7839,c_7860]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7841,plain,
% 3.25/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_7831,c_6419]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7911,plain,
% 3.25/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.25/0.99      inference(light_normalisation,[status(thm)],[c_7841,c_7860]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7913,plain,
% 3.25/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_7911,c_2]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_16,plain,
% 3.25/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.25/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.25/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.25/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_935,plain,
% 3.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.25/0.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.25/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.25/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.25/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.25/0.99      | sK2 != k1_xboole_0
% 3.25/0.99      | sK1 != X1 ),
% 3.25/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_936,plain,
% 3.25/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.25/0.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.25/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.25/0.99      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.25/0.99      | sK2 != k1_xboole_0 ),
% 3.25/0.99      inference(unflattening,[status(thm)],[c_935]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3043,plain,
% 3.25/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.25/0.99      | sK2 != k1_xboole_0
% 3.25/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.25/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.25/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_936]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3238,plain,
% 3.25/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.25/0.99      | sK2 != k1_xboole_0
% 3.25/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.25/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.25/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_3043,c_2]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3525,plain,
% 3.25/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.25/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.25/0.99      | ~ v1_funct_1(sK3) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_3376]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3526,plain,
% 3.25/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.25/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 3.25/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_3525]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3707,plain,
% 3.25/0.99      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.25/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.25/0.99      | sK2 != k1_xboole_0
% 3.25/0.99      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_3238,c_32,c_34,c_3526]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3708,plain,
% 3.25/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.25/0.99      | sK2 != k1_xboole_0
% 3.25/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.25/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/0.99      inference(renaming,[status(thm)],[c_3707]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5428,plain,
% 3.25/0.99      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.25/0.99      | sK2 != k1_xboole_0
% 3.25/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.25/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_5424,c_3708]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7846,plain,
% 3.25/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.25/0.99      | sK2 != k1_xboole_0
% 3.25/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.25/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_7831,c_5428]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_14,plain,
% 3.25/0.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.25/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.25/0.99      | k1_xboole_0 = X0 ),
% 3.25/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_837,plain,
% 3.25/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.25/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.25/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.25/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.25/0.99      | sK2 != X0
% 3.25/0.99      | sK1 != k1_xboole_0
% 3.25/0.99      | k1_xboole_0 = X0 ),
% 3.25/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_838,plain,
% 3.25/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.25/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.25/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.25/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.25/0.99      | sK1 != k1_xboole_0
% 3.25/0.99      | k1_xboole_0 = sK2 ),
% 3.25/0.99      inference(unflattening,[status(thm)],[c_837]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3047,plain,
% 3.25/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.25/0.99      | sK1 != k1_xboole_0
% 3.25/0.99      | k1_xboole_0 = sK2
% 3.25/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.25/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.25/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_838]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3225,plain,
% 3.25/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.25/0.99      | sK2 = k1_xboole_0
% 3.25/0.99      | sK1 != k1_xboole_0
% 3.25/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.25/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.25/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_3047,c_1]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3635,plain,
% 3.25/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.25/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.25/0.99      | sK1 != k1_xboole_0
% 3.25/0.99      | sK2 = k1_xboole_0
% 3.25/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_3225,c_32,c_34,c_3526]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3636,plain,
% 3.25/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.25/0.99      | sK2 = k1_xboole_0
% 3.25/0.99      | sK1 != k1_xboole_0
% 3.25/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.25/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/0.99      inference(renaming,[status(thm)],[c_3635]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5429,plain,
% 3.25/0.99      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.25/0.99      | sK2 = k1_xboole_0
% 3.25/0.99      | sK1 != k1_xboole_0
% 3.25/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.25/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_5424,c_3636]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_430,plain,
% 3.25/0.99      ( sK2 != X0 | sK0 != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.25/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_28]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_431,plain,
% 3.25/0.99      ( sK0 != k1_xboole_0 | k1_xboole_0 = sK2 ),
% 3.25/0.99      inference(unflattening,[status(thm)],[c_430]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3463,plain,
% 3.25/0.99      ( sK2 = sK2 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_2421]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3343,plain,
% 3.25/0.99      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_2422]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3620,plain,
% 3.25/0.99      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_3343]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_5591,plain,
% 3.25/0.99      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_5429,c_431,c_3463,c_3620,c_3717]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7847,plain,
% 3.25/0.99      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_7831,c_5591]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7889,plain,
% 3.25/0.99      ( sK2 = k1_xboole_0 ),
% 3.25/0.99      inference(equality_resolution_simp,[status(thm)],[c_7847]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7892,plain,
% 3.25/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 3.25/0.99      | k1_xboole_0 != k1_xboole_0
% 3.25/0.99      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.25/0.99      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/0.99      inference(light_normalisation,[status(thm)],[c_7846,c_7889]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7893,plain,
% 3.25/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 3.25/0.99      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.25/0.99      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/0.99      inference(equality_resolution_simp,[status(thm)],[c_7892]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7897,plain,
% 3.25/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 3.25/0.99      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_7893,c_2]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7915,plain,
% 3.25/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
% 3.25/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_7913,c_7897]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_7927,plain,
% 3.25/0.99      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_7925,c_7915]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_8787,plain,
% 3.25/0.99      ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
% 3.25/0.99      inference(light_normalisation,[status(thm)],[c_7927,c_8668]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3858,plain,
% 3.25/0.99      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 3.25/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.25/0.99      inference(superposition,[status(thm)],[c_3059,c_3063]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_83,plain,
% 3.25/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_85,plain,
% 3.25/0.99      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_83]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_2427,plain,
% 3.25/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.25/0.99      theory(equality) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3331,plain,
% 3.25/0.99      ( v1_relat_1(X0)
% 3.25/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
% 3.25/0.99      | X0 != k2_zfmisc_1(X1,X2) ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_2427]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3332,plain,
% 3.25/0.99      ( X0 != k2_zfmisc_1(X1,X2)
% 3.25/0.99      | v1_relat_1(X0) = iProver_top
% 3.25/0.99      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.25/0.99      inference(predicate_to_equality,[status(thm)],[c_3331]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3334,plain,
% 3.25/0.99      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.25/0.99      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.25/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.25/0.99      inference(instantiation,[status(thm)],[c_3332]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_3863,plain,
% 3.25/0.99      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.25/0.99      inference(global_propositional_subsumption,
% 3.25/0.99                [status(thm)],
% 3.25/0.99                [c_3858,c_85,c_99,c_100,c_3334,c_3582]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_8788,plain,
% 3.25/0.99      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 3.25/0.99      inference(demodulation,[status(thm)],[c_8787,c_3863]) ).
% 3.25/0.99  
% 3.25/0.99  cnf(c_9018,plain,
% 3.25/0.99      ( $false ),
% 3.25/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_9016,c_8788]) ).
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.25/0.99  
% 3.25/0.99  ------                               Statistics
% 3.25/0.99  
% 3.25/0.99  ------ General
% 3.25/0.99  
% 3.25/0.99  abstr_ref_over_cycles:                  0
% 3.25/0.99  abstr_ref_under_cycles:                 0
% 3.25/0.99  gc_basic_clause_elim:                   0
% 3.25/0.99  forced_gc_time:                         0
% 3.25/0.99  parsing_time:                           0.011
% 3.25/0.99  unif_index_cands_time:                  0.
% 3.25/0.99  unif_index_add_time:                    0.
% 3.25/0.99  orderings_time:                         0.
% 3.25/0.99  out_proof_time:                         0.016
% 3.25/0.99  total_time:                             0.244
% 3.25/0.99  num_of_symbols:                         49
% 3.25/0.99  num_of_terms:                           6762
% 3.25/0.99  
% 3.25/0.99  ------ Preprocessing
% 3.25/0.99  
% 3.25/0.99  num_of_splits:                          0
% 3.25/0.99  num_of_split_atoms:                     0
% 3.25/0.99  num_of_reused_defs:                     0
% 3.25/0.99  num_eq_ax_congr_red:                    13
% 3.25/0.99  num_of_sem_filtered_clauses:            1
% 3.25/0.99  num_of_subtypes:                        0
% 3.25/0.99  monotx_restored_types:                  0
% 3.25/0.99  sat_num_of_epr_types:                   0
% 3.25/0.99  sat_num_of_non_cyclic_types:            0
% 3.25/0.99  sat_guarded_non_collapsed_types:        0
% 3.25/0.99  num_pure_diseq_elim:                    0
% 3.25/0.99  simp_replaced_by:                       0
% 3.25/0.99  res_preprocessed:                       147
% 3.25/0.99  prep_upred:                             0
% 3.25/0.99  prep_unflattend:                        159
% 3.25/0.99  smt_new_axioms:                         0
% 3.25/0.99  pred_elim_cands:                        4
% 3.25/0.99  pred_elim:                              2
% 3.25/0.99  pred_elim_cl:                           0
% 3.25/0.99  pred_elim_cycles:                       5
% 3.25/0.99  merged_defs:                            8
% 3.25/0.99  merged_defs_ncl:                        0
% 3.25/0.99  bin_hyper_res:                          9
% 3.25/0.99  prep_cycles:                            4
% 3.25/0.99  pred_elim_time:                         0.035
% 3.25/0.99  splitting_time:                         0.
% 3.25/0.99  sem_filter_time:                        0.
% 3.25/0.99  monotx_time:                            0.001
% 3.25/0.99  subtype_inf_time:                       0.
% 3.25/0.99  
% 3.25/0.99  ------ Problem properties
% 3.25/0.99  
% 3.25/0.99  clauses:                                31
% 3.25/0.99  conjectures:                            4
% 3.25/0.99  epr:                                    5
% 3.25/0.99  horn:                                   26
% 3.25/0.99  ground:                                 12
% 3.25/0.99  unary:                                  6
% 3.25/0.99  binary:                                 7
% 3.25/0.99  lits:                                   90
% 3.25/0.99  lits_eq:                                34
% 3.25/0.99  fd_pure:                                0
% 3.25/0.99  fd_pseudo:                              0
% 3.25/0.99  fd_cond:                                4
% 3.25/0.99  fd_pseudo_cond:                         0
% 3.25/0.99  ac_symbols:                             0
% 3.25/0.99  
% 3.25/0.99  ------ Propositional Solver
% 3.25/0.99  
% 3.25/0.99  prop_solver_calls:                      29
% 3.25/0.99  prop_fast_solver_calls:                 1502
% 3.25/0.99  smt_solver_calls:                       0
% 3.25/0.99  smt_fast_solver_calls:                  0
% 3.25/0.99  prop_num_of_clauses:                    2826
% 3.25/0.99  prop_preprocess_simplified:             7091
% 3.25/0.99  prop_fo_subsumed:                       36
% 3.25/0.99  prop_solver_time:                       0.
% 3.25/0.99  smt_solver_time:                        0.
% 3.25/0.99  smt_fast_solver_time:                   0.
% 3.25/0.99  prop_fast_solver_time:                  0.
% 3.25/0.99  prop_unsat_core_time:                   0.
% 3.25/0.99  
% 3.25/0.99  ------ QBF
% 3.25/0.99  
% 3.25/0.99  qbf_q_res:                              0
% 3.25/0.99  qbf_num_tautologies:                    0
% 3.25/0.99  qbf_prep_cycles:                        0
% 3.25/0.99  
% 3.25/0.99  ------ BMC1
% 3.25/0.99  
% 3.25/0.99  bmc1_current_bound:                     -1
% 3.25/0.99  bmc1_last_solved_bound:                 -1
% 3.25/0.99  bmc1_unsat_core_size:                   -1
% 3.25/0.99  bmc1_unsat_core_parents_size:           -1
% 3.25/0.99  bmc1_merge_next_fun:                    0
% 3.25/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.25/0.99  
% 3.25/0.99  ------ Instantiation
% 3.25/0.99  
% 3.25/0.99  inst_num_of_clauses:                    859
% 3.25/0.99  inst_num_in_passive:                    371
% 3.25/0.99  inst_num_in_active:                     404
% 3.25/0.99  inst_num_in_unprocessed:                84
% 3.25/0.99  inst_num_of_loops:                      530
% 3.25/0.99  inst_num_of_learning_restarts:          0
% 3.25/0.99  inst_num_moves_active_passive:          122
% 3.25/0.99  inst_lit_activity:                      0
% 3.25/0.99  inst_lit_activity_moves:                0
% 3.25/0.99  inst_num_tautologies:                   0
% 3.25/0.99  inst_num_prop_implied:                  0
% 3.25/0.99  inst_num_existing_simplified:           0
% 3.25/0.99  inst_num_eq_res_simplified:             0
% 3.25/0.99  inst_num_child_elim:                    0
% 3.25/0.99  inst_num_of_dismatching_blockings:      259
% 3.25/0.99  inst_num_of_non_proper_insts:           779
% 3.25/0.99  inst_num_of_duplicates:                 0
% 3.25/0.99  inst_inst_num_from_inst_to_res:         0
% 3.25/0.99  inst_dismatching_checking_time:         0.
% 3.25/0.99  
% 3.25/0.99  ------ Resolution
% 3.25/0.99  
% 3.25/0.99  res_num_of_clauses:                     0
% 3.25/0.99  res_num_in_passive:                     0
% 3.25/0.99  res_num_in_active:                      0
% 3.25/0.99  res_num_of_loops:                       151
% 3.25/0.99  res_forward_subset_subsumed:            32
% 3.25/0.99  res_backward_subset_subsumed:           0
% 3.25/0.99  res_forward_subsumed:                   0
% 3.25/0.99  res_backward_subsumed:                  0
% 3.25/0.99  res_forward_subsumption_resolution:     3
% 3.25/0.99  res_backward_subsumption_resolution:    0
% 3.25/0.99  res_clause_to_clause_subsumption:       499
% 3.25/0.99  res_orphan_elimination:                 0
% 3.25/0.99  res_tautology_del:                      68
% 3.25/0.99  res_num_eq_res_simplified:              1
% 3.25/0.99  res_num_sel_changes:                    0
% 3.25/0.99  res_moves_from_active_to_pass:          0
% 3.25/0.99  
% 3.25/0.99  ------ Superposition
% 3.25/0.99  
% 3.25/0.99  sup_time_total:                         0.
% 3.25/0.99  sup_time_generating:                    0.
% 3.25/0.99  sup_time_sim_full:                      0.
% 3.25/0.99  sup_time_sim_immed:                     0.
% 3.25/0.99  
% 3.25/0.99  sup_num_of_clauses:                     122
% 3.25/0.99  sup_num_in_active:                      53
% 3.25/0.99  sup_num_in_passive:                     69
% 3.25/0.99  sup_num_of_loops:                       105
% 3.25/0.99  sup_fw_superposition:                   64
% 3.25/0.99  sup_bw_superposition:                   101
% 3.25/0.99  sup_immediate_simplified:               54
% 3.25/0.99  sup_given_eliminated:                   3
% 3.25/0.99  comparisons_done:                       0
% 3.25/0.99  comparisons_avoided:                    19
% 3.25/0.99  
% 3.25/0.99  ------ Simplifications
% 3.25/0.99  
% 3.25/0.99  
% 3.25/0.99  sim_fw_subset_subsumed:                 16
% 3.25/0.99  sim_bw_subset_subsumed:                 10
% 3.25/0.99  sim_fw_subsumed:                        5
% 3.25/0.99  sim_bw_subsumed:                        2
% 3.25/0.99  sim_fw_subsumption_res:                 7
% 3.25/0.99  sim_bw_subsumption_res:                 2
% 3.25/0.99  sim_tautology_del:                      7
% 3.25/0.99  sim_eq_tautology_del:                   14
% 3.25/0.99  sim_eq_res_simp:                        6
% 3.25/0.99  sim_fw_demodulated:                     18
% 3.25/0.99  sim_bw_demodulated:                     55
% 3.25/0.99  sim_light_normalised:                   26
% 3.25/0.99  sim_joinable_taut:                      0
% 3.25/0.99  sim_joinable_simp:                      0
% 3.25/0.99  sim_ac_normalised:                      0
% 3.25/0.99  sim_smt_subsumption:                    0
% 3.25/0.99  
%------------------------------------------------------------------------------
