%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:00 EST 2020

% Result     : Theorem 23.48s
% Output     : CNFRefutation 23.48s
% Verified   : 
% Statistics : Number of formulae       :  285 (40874 expanded)
%              Number of clauses        :  214 (15665 expanded)
%              Number of leaves         :   21 (8070 expanded)
%              Depth                    :   41
%              Number of atoms          :  770 (211590 expanded)
%              Number of equality atoms :  489 (60085 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f35])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f41])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(nnf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

cnf(c_6,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_701,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_693,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_681,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_687,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2306,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_681,c_687])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_694,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2074,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_681,c_694])).

cnf(c_2320,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2306,c_2074])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,plain,
    ( v1_funct_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2810,plain,
    ( sK1 = k1_xboole_0
    | k1_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2320,c_31])).

cnf(c_2811,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2810])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_695,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1706,plain,
    ( v4_relat_1(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_681,c_695])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_699,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2298,plain,
    ( k7_relat_1(sK3,sK0) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1706,c_699])).

cnf(c_988,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1070,plain,
    ( ~ v4_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK0) = sK3 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1125,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_4,c_27])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1290,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2804,plain,
    ( k7_relat_1(sK3,sK0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2298,c_27,c_988,c_1070,c_1125,c_1290])).

cnf(c_9,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_698,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2807,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2804,c_698])).

cnf(c_1126,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(c_1291,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1290])).

cnf(c_2934,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2807,c_1126,c_1291])).

cnf(c_2939,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK0,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2811,c_2934])).

cnf(c_703,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2415,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_681,c_703])).

cnf(c_2658,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2415,c_1126,c_1291])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_697,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3140,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))) = k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_698,c_697])).

cnf(c_19462,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK3))))) = k1_relat_1(k7_relat_1(X0,k1_relat_1(sK3)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2658,c_3140])).

cnf(c_20719,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) ),
    inference(superposition,[status(thm)],[c_2658,c_19462])).

cnf(c_20754,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
    | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20719,c_697])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_684,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5641,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_681,c_684])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1032,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1199,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_5870,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5641,c_29,c_27,c_1199])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_686,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5899,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5870,c_686])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1027,plain,
    ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1211,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_1212,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1211])).

cnf(c_247,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1912,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_248,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1809,plain,
    ( X0 != X1
    | X0 = k2_partfun1(sK0,sK1,sK3,X2)
    | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_2638,plain,
    ( X0 = k2_partfun1(sK0,sK1,sK3,X1)
    | X0 != k7_relat_1(sK3,X1)
    | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_1809])).

cnf(c_2877,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
    | k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | k7_relat_1(sK3,X0) != k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2638])).

cnf(c_2878,plain,
    ( k7_relat_1(sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_253,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1338,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | X0 != k2_partfun1(sK0,sK1,sK3,X2)
    | X1 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_1911,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | X0 != k2_partfun1(sK0,sK1,sK3,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1338])).

cnf(c_3743,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1911])).

cnf(c_3749,plain,
    ( k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3743])).

cnf(c_6164,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5899,c_29,c_30,c_27,c_32,c_1199,c_1212,c_1912,c_2877,c_2878,c_3749])).

cnf(c_6172,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6164,c_703])).

cnf(c_7174,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6172,c_1291])).

cnf(c_24805,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
    | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20754,c_7174])).

cnf(c_24813,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2811,c_24805])).

cnf(c_24817,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24813,c_2804])).

cnf(c_28393,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2811,c_24817])).

cnf(c_28435,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK0)) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2939,c_28393])).

cnf(c_6177,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6164,c_695])).

cnf(c_6925,plain,
    ( k7_relat_1(k7_relat_1(sK3,X0),sK0) = k7_relat_1(sK3,X0)
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6177,c_699])).

cnf(c_8014,plain,
    ( k7_relat_1(k7_relat_1(sK3,X0),sK0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6925,c_1291,c_6172])).

cnf(c_28448,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) = sK0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28435,c_8014,c_20719])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_682,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3142,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2811,c_697])).

cnf(c_3464,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3142,c_1126,c_1291])).

cnf(c_3465,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3464])).

cnf(c_3473,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_682,c_3465])).

cnf(c_3647,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3473,c_698])).

cnf(c_3668,plain,
    ( r1_tarski(sK2,sK2) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3647,c_1126,c_1291])).

cnf(c_3669,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3668])).

cnf(c_6173,plain,
    ( k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1) = k7_relat_1(k7_relat_1(sK3,X0),X1)
    | v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6164,c_684])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_685,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1086,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_681,c_685])).

cnf(c_258,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1296,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))
    | X0 != k2_partfun1(sK0,sK1,sK3,X1) ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_3744,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | v1_funct_1(k7_relat_1(sK3,X0))
    | k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1296])).

cnf(c_3745,plain,
    ( k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3744])).

cnf(c_7209,plain,
    ( k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1) = k7_relat_1(k7_relat_1(sK3,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6173,c_29,c_30,c_27,c_1086,c_1199,c_2877,c_2878,c_3745])).

cnf(c_7220,plain,
    ( m1_subset_1(k7_relat_1(k7_relat_1(sK3,X0),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7209,c_686])).

cnf(c_58151,plain,
    ( m1_subset_1(k7_relat_1(k7_relat_1(sK3,X0),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7220,c_29,c_30,c_27,c_32,c_1086,c_1199,c_1212,c_1912,c_2877,c_2878,c_3745,c_3749])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_696,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_58166,plain,
    ( v5_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_58151,c_696])).

cnf(c_28433,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_682,c_28393])).

cnf(c_4083,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_694])).

cnf(c_38025,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | v5_relat_1(X2,X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_4083])).

cnf(c_38087,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2))
    | sK1 = k1_xboole_0
    | v5_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28433,c_38025])).

cnf(c_58921,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2))
    | sK1 = k1_xboole_0
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_58166,c_38087])).

cnf(c_58160,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_58151,c_703])).

cnf(c_2414,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_686,c_703])).

cnf(c_700,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7690,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2414,c_700])).

cnf(c_7697,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6164,c_7690])).

cnf(c_7714,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7697,c_7209])).

cnf(c_59136,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_58160,c_29,c_30,c_27,c_1086,c_1199,c_2877,c_2878,c_3745,c_7714])).

cnf(c_61442,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2))
    | sK1 = k1_xboole_0
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_58921,c_59136])).

cnf(c_61447,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3669,c_61442])).

cnf(c_61613,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(k7_relat_1(sK3,sK0),sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_28448,c_61447])).

cnf(c_61632,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_61613,c_2804])).

cnf(c_61649,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_61632,c_28433])).

cnf(c_18,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_689,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_62055,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) = iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_61649,c_689])).

cnf(c_24,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_683,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5875,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5870,c_683])).

cnf(c_1349,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1086,c_30])).

cnf(c_5876,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5870,c_1349])).

cnf(c_5882,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5875,c_5876])).

cnf(c_62226,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_62055,c_5882])).

cnf(c_62232,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_62226])).

cnf(c_3648,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3473,c_697])).

cnf(c_7185,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7174,c_3648])).

cnf(c_7659,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(X0,sK2)))) = k1_relat_1(k7_relat_1(X0,sK2))
    | sK1 = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_698,c_7185])).

cnf(c_12775,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2658,c_7659])).

cnf(c_13340,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3473,c_12775])).

cnf(c_13396,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13340,c_698])).

cnf(c_13880,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13396,c_7174])).

cnf(c_67427,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_62232,c_13880])).

cnf(c_67434,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_67427,c_7174])).

cnf(c_67436,plain,
    ( sK1 = k1_xboole_0
    | v5_relat_1(k7_relat_1(sK3,sK2),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_67434])).

cnf(c_6176,plain,
    ( v5_relat_1(k7_relat_1(sK3,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6164,c_696])).

cnf(c_67442,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_67436,c_7174,c_6176])).

cnf(c_67560,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67442,c_6164])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_67572,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_67442,c_25])).

cnf(c_67573,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_67572])).

cnf(c_67596,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_67560,c_67573])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_67598,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67596,c_2])).

cnf(c_67561,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_67442,c_5882])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_67593,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_67561,c_1])).

cnf(c_67600,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_67598,c_67593])).

cnf(c_68807,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
    inference(demodulation,[status(thm)],[c_67573,c_2804])).

cnf(c_68809,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67573,c_682])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_704,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_68934,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_68809,c_704])).

cnf(c_79751,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_67600,c_68807,c_68934])).

cnf(c_67570,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67442,c_681])).

cnf(c_67579,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_67570,c_67573])).

cnf(c_67581,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67579,c_2])).

cnf(c_2076,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_694])).

cnf(c_68135,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_67581,c_2076])).

cnf(c_71082,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_68135,c_689])).

cnf(c_71094,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_71082,c_2])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_93,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_94,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_985,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_986,plain,
    ( v5_relat_1(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_985])).

cnf(c_991,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_992,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_991])).

cnf(c_993,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1067,plain,
    ( ~ v5_relat_1(sK3,sK1)
    | r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1068,plain,
    ( v5_relat_1(sK3,sK1) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1067])).

cnf(c_249,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1483,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X2),X3)
    | X3 != X1
    | k2_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_1689,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | r1_tarski(k2_relat_1(X0),X2)
    | X2 != X1
    | k2_relat_1(X0) != k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_2647,plain,
    ( r1_tarski(k2_relat_1(sK3),X0)
    | ~ r1_tarski(k2_relat_1(sK3),sK1)
    | X0 != sK1
    | k2_relat_1(sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1689])).

cnf(c_2648,plain,
    ( X0 != sK1
    | k2_relat_1(sK3) != k2_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2647])).

cnf(c_2650,plain,
    ( k2_relat_1(sK3) != k2_relat_1(sK3)
    | k1_xboole_0 != sK1
    | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2648])).

cnf(c_1690,plain,
    ( k2_relat_1(X0) = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_3088,plain,
    ( k2_relat_1(sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1690])).

cnf(c_2056,plain,
    ( X0 != X1
    | k1_relat_1(X2) != X1
    | k1_relat_1(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_3014,plain,
    ( X0 != k1_relat_1(X1)
    | k1_relat_1(X2) = X0
    | k1_relat_1(X2) != k1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_2056])).

cnf(c_4283,plain,
    ( k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | k1_relat_1(X0) = k1_relset_1(sK0,sK1,sK3)
    | k1_relat_1(X0) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3014])).

cnf(c_6321,plain,
    ( k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4283])).

cnf(c_2052,plain,
    ( k1_relat_1(X0) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_6322,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2052])).

cnf(c_4079,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_693])).

cnf(c_6644,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2934,c_4079])).

cnf(c_6833,plain,
    ( X0 != k1_relset_1(sK0,sK1,sK3)
    | k1_relat_1(sK3) = X0
    | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_2056])).

cnf(c_6834,plain,
    ( k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_relset_1(sK0,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_6833])).

cnf(c_17324,plain,
    ( ~ r1_tarski(k1_relset_1(sK0,sK1,sK3),k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_17328,plain,
    ( k1_xboole_0 = k1_relset_1(sK0,sK1,sK3)
    | r1_tarski(k1_relset_1(sK0,sK1,sK3),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17324])).

cnf(c_2717,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_249,c_247])).

cnf(c_5155,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relset_1(X1,X2,X0),X3)
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(resolution,[status(thm)],[c_2717,c_13])).

cnf(c_54670,plain,
    ( r1_tarski(k1_relset_1(sK0,sK1,sK3),X0)
    | ~ r1_tarski(k1_relat_1(sK3),X0) ),
    inference(resolution,[status(thm)],[c_5155,c_27])).

cnf(c_54671,plain,
    ( r1_tarski(k1_relset_1(sK0,sK1,sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54670])).

cnf(c_54673,plain,
    ( r1_tarski(k1_relset_1(sK0,sK1,sK3),k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54671])).

cnf(c_68805,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67573,c_2934])).

cnf(c_17,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_690,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_799,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_690,c_2])).

cnf(c_71083,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_68135,c_799])).

cnf(c_72566,plain,
    ( v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_71094,c_27,c_32,c_93,c_94,c_986,c_992,c_993,c_1068,c_1126,c_1291,c_2650,c_3088,c_6321,c_6322,c_6644,c_6834,c_17328,c_54673,c_67442,c_68805,c_71083])).

cnf(c_79753,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_79751,c_72566])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:27:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.48/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.48/3.49  
% 23.48/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.48/3.49  
% 23.48/3.49  ------  iProver source info
% 23.48/3.49  
% 23.48/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.48/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.48/3.49  git: non_committed_changes: false
% 23.48/3.49  git: last_make_outside_of_git: false
% 23.48/3.49  
% 23.48/3.49  ------ 
% 23.48/3.49  ------ Parsing...
% 23.48/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.48/3.49  
% 23.48/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 23.48/3.49  
% 23.48/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.48/3.49  
% 23.48/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.48/3.49  ------ Proving...
% 23.48/3.49  ------ Problem Properties 
% 23.48/3.49  
% 23.48/3.49  
% 23.48/3.49  clauses                                 30
% 23.48/3.49  conjectures                             6
% 23.48/3.49  EPR                                     5
% 23.48/3.49  Horn                                    25
% 23.48/3.49  unary                                   7
% 23.48/3.49  binary                                  6
% 23.48/3.49  lits                                    74
% 23.48/3.49  lits eq                                 21
% 23.48/3.49  fd_pure                                 0
% 23.48/3.49  fd_pseudo                               0
% 23.48/3.49  fd_cond                                 5
% 23.48/3.49  fd_pseudo_cond                          0
% 23.48/3.49  AC symbols                              0
% 23.48/3.49  
% 23.48/3.49  ------ Input Options Time Limit: Unbounded
% 23.48/3.49  
% 23.48/3.49  
% 23.48/3.49  ------ 
% 23.48/3.49  Current options:
% 23.48/3.49  ------ 
% 23.48/3.49  
% 23.48/3.49  
% 23.48/3.49  
% 23.48/3.49  
% 23.48/3.49  ------ Proving...
% 23.48/3.49  
% 23.48/3.49  
% 23.48/3.49  % SZS status Theorem for theBenchmark.p
% 23.48/3.49  
% 23.48/3.49   Resolution empty clause
% 23.48/3.49  
% 23.48/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.48/3.49  
% 23.48/3.49  fof(f4,axiom,(
% 23.48/3.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 23.48/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f19,plain,(
% 23.48/3.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 23.48/3.49    inference(ennf_transformation,[],[f4])).
% 23.48/3.49  
% 23.48/3.49  fof(f39,plain,(
% 23.48/3.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 23.48/3.49    inference(nnf_transformation,[],[f19])).
% 23.48/3.49  
% 23.48/3.49  fof(f48,plain,(
% 23.48/3.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f39])).
% 23.48/3.49  
% 23.48/3.49  fof(f11,axiom,(
% 23.48/3.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 23.48/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f27,plain,(
% 23.48/3.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 23.48/3.49    inference(ennf_transformation,[],[f11])).
% 23.48/3.49  
% 23.48/3.49  fof(f28,plain,(
% 23.48/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 23.48/3.49    inference(flattening,[],[f27])).
% 23.48/3.49  
% 23.48/3.49  fof(f57,plain,(
% 23.48/3.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f28])).
% 23.48/3.49  
% 23.48/3.49  fof(f15,conjecture,(
% 23.48/3.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 23.48/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f16,negated_conjecture,(
% 23.48/3.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 23.48/3.49    inference(negated_conjecture,[],[f15])).
% 23.48/3.49  
% 23.48/3.49  fof(f35,plain,(
% 23.48/3.49    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 23.48/3.49    inference(ennf_transformation,[],[f16])).
% 23.48/3.49  
% 23.48/3.49  fof(f36,plain,(
% 23.48/3.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 23.48/3.49    inference(flattening,[],[f35])).
% 23.48/3.49  
% 23.48/3.49  fof(f41,plain,(
% 23.48/3.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 23.48/3.49    introduced(choice_axiom,[])).
% 23.48/3.49  
% 23.48/3.49  fof(f42,plain,(
% 23.48/3.49    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 23.48/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f41])).
% 23.48/3.49  
% 23.48/3.49  fof(f69,plain,(
% 23.48/3.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 23.48/3.49    inference(cnf_transformation,[],[f42])).
% 23.48/3.49  
% 23.48/3.49  fof(f12,axiom,(
% 23.48/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 23.48/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f29,plain,(
% 23.48/3.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.48/3.49    inference(ennf_transformation,[],[f12])).
% 23.48/3.49  
% 23.48/3.49  fof(f30,plain,(
% 23.48/3.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.48/3.49    inference(flattening,[],[f29])).
% 23.48/3.49  
% 23.48/3.49  fof(f40,plain,(
% 23.48/3.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.48/3.49    inference(nnf_transformation,[],[f30])).
% 23.48/3.49  
% 23.48/3.49  fof(f58,plain,(
% 23.48/3.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.48/3.49    inference(cnf_transformation,[],[f40])).
% 23.48/3.49  
% 23.48/3.49  fof(f10,axiom,(
% 23.48/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 23.48/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f26,plain,(
% 23.48/3.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.48/3.49    inference(ennf_transformation,[],[f10])).
% 23.48/3.49  
% 23.48/3.49  fof(f56,plain,(
% 23.48/3.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.48/3.49    inference(cnf_transformation,[],[f26])).
% 23.48/3.49  
% 23.48/3.49  fof(f68,plain,(
% 23.48/3.49    v1_funct_2(sK3,sK0,sK1)),
% 23.48/3.49    inference(cnf_transformation,[],[f42])).
% 23.48/3.49  
% 23.48/3.49  fof(f9,axiom,(
% 23.48/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 23.48/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f25,plain,(
% 23.48/3.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.48/3.49    inference(ennf_transformation,[],[f9])).
% 23.48/3.49  
% 23.48/3.49  fof(f54,plain,(
% 23.48/3.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.48/3.49    inference(cnf_transformation,[],[f25])).
% 23.48/3.49  
% 23.48/3.49  fof(f6,axiom,(
% 23.48/3.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 23.48/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f20,plain,(
% 23.48/3.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 23.48/3.49    inference(ennf_transformation,[],[f6])).
% 23.48/3.49  
% 23.48/3.49  fof(f21,plain,(
% 23.48/3.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 23.48/3.49    inference(flattening,[],[f20])).
% 23.48/3.49  
% 23.48/3.49  fof(f51,plain,(
% 23.48/3.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f21])).
% 23.48/3.49  
% 23.48/3.49  fof(f3,axiom,(
% 23.48/3.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 23.48/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f18,plain,(
% 23.48/3.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 23.48/3.49    inference(ennf_transformation,[],[f3])).
% 23.48/3.49  
% 23.48/3.49  fof(f47,plain,(
% 23.48/3.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f18])).
% 23.48/3.49  
% 23.48/3.49  fof(f5,axiom,(
% 23.48/3.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 23.48/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f50,plain,(
% 23.48/3.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 23.48/3.49    inference(cnf_transformation,[],[f5])).
% 23.48/3.49  
% 23.48/3.49  fof(f7,axiom,(
% 23.48/3.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 23.48/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f22,plain,(
% 23.48/3.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 23.48/3.49    inference(ennf_transformation,[],[f7])).
% 23.48/3.49  
% 23.48/3.49  fof(f52,plain,(
% 23.48/3.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f22])).
% 23.48/3.49  
% 23.48/3.49  fof(f8,axiom,(
% 23.48/3.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 23.48/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f23,plain,(
% 23.48/3.49    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 23.48/3.49    inference(ennf_transformation,[],[f8])).
% 23.48/3.49  
% 23.48/3.49  fof(f24,plain,(
% 23.48/3.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 23.48/3.49    inference(flattening,[],[f23])).
% 23.48/3.49  
% 23.48/3.49  fof(f53,plain,(
% 23.48/3.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f24])).
% 23.48/3.49  
% 23.48/3.49  fof(f14,axiom,(
% 23.48/3.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 23.48/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f33,plain,(
% 23.48/3.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 23.48/3.49    inference(ennf_transformation,[],[f14])).
% 23.48/3.49  
% 23.48/3.49  fof(f34,plain,(
% 23.48/3.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 23.48/3.49    inference(flattening,[],[f33])).
% 23.48/3.49  
% 23.48/3.49  fof(f66,plain,(
% 23.48/3.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f34])).
% 23.48/3.49  
% 23.48/3.49  fof(f67,plain,(
% 23.48/3.49    v1_funct_1(sK3)),
% 23.48/3.49    inference(cnf_transformation,[],[f42])).
% 23.48/3.49  
% 23.48/3.49  fof(f13,axiom,(
% 23.48/3.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 23.48/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f31,plain,(
% 23.48/3.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 23.48/3.49    inference(ennf_transformation,[],[f13])).
% 23.48/3.49  
% 23.48/3.49  fof(f32,plain,(
% 23.48/3.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 23.48/3.49    inference(flattening,[],[f31])).
% 23.48/3.49  
% 23.48/3.49  fof(f65,plain,(
% 23.48/3.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f32])).
% 23.48/3.49  
% 23.48/3.49  fof(f70,plain,(
% 23.48/3.49    r1_tarski(sK2,sK0)),
% 23.48/3.49    inference(cnf_transformation,[],[f42])).
% 23.48/3.49  
% 23.48/3.49  fof(f64,plain,(
% 23.48/3.49    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f32])).
% 23.48/3.49  
% 23.48/3.49  fof(f55,plain,(
% 23.48/3.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.48/3.49    inference(cnf_transformation,[],[f25])).
% 23.48/3.49  
% 23.48/3.49  fof(f60,plain,(
% 23.48/3.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.48/3.49    inference(cnf_transformation,[],[f40])).
% 23.48/3.49  
% 23.48/3.49  fof(f72,plain,(
% 23.48/3.49    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 23.48/3.49    inference(cnf_transformation,[],[f42])).
% 23.48/3.49  
% 23.48/3.49  fof(f71,plain,(
% 23.48/3.49    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 23.48/3.49    inference(cnf_transformation,[],[f42])).
% 23.48/3.49  
% 23.48/3.49  fof(f2,axiom,(
% 23.48/3.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 23.48/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f37,plain,(
% 23.48/3.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 23.48/3.49    inference(nnf_transformation,[],[f2])).
% 23.48/3.49  
% 23.48/3.49  fof(f38,plain,(
% 23.48/3.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 23.48/3.49    inference(flattening,[],[f37])).
% 23.48/3.49  
% 23.48/3.49  fof(f45,plain,(
% 23.48/3.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 23.48/3.49    inference(cnf_transformation,[],[f38])).
% 23.48/3.49  
% 23.48/3.49  fof(f74,plain,(
% 23.48/3.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 23.48/3.49    inference(equality_resolution,[],[f45])).
% 23.48/3.49  
% 23.48/3.49  fof(f46,plain,(
% 23.48/3.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 23.48/3.49    inference(cnf_transformation,[],[f38])).
% 23.48/3.49  
% 23.48/3.49  fof(f73,plain,(
% 23.48/3.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 23.48/3.49    inference(equality_resolution,[],[f46])).
% 23.48/3.49  
% 23.48/3.49  fof(f1,axiom,(
% 23.48/3.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 23.48/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.48/3.49  
% 23.48/3.49  fof(f17,plain,(
% 23.48/3.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 23.48/3.49    inference(ennf_transformation,[],[f1])).
% 23.48/3.49  
% 23.48/3.49  fof(f43,plain,(
% 23.48/3.49    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f17])).
% 23.48/3.49  
% 23.48/3.49  fof(f44,plain,(
% 23.48/3.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 23.48/3.49    inference(cnf_transformation,[],[f38])).
% 23.48/3.49  
% 23.48/3.49  fof(f61,plain,(
% 23.48/3.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.48/3.49    inference(cnf_transformation,[],[f40])).
% 23.48/3.49  
% 23.48/3.49  fof(f78,plain,(
% 23.48/3.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 23.48/3.49    inference(equality_resolution,[],[f61])).
% 23.48/3.49  
% 23.48/3.49  cnf(c_6,plain,
% 23.48/3.49      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 23.48/3.49      inference(cnf_transformation,[],[f48]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_701,plain,
% 23.48/3.49      ( v5_relat_1(X0,X1) != iProver_top
% 23.48/3.49      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 23.48/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_14,plain,
% 23.48/3.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.48/3.49      | ~ r1_tarski(k1_relat_1(X0),X1)
% 23.48/3.49      | ~ r1_tarski(k2_relat_1(X0),X2)
% 23.48/3.49      | ~ v1_relat_1(X0) ),
% 23.48/3.49      inference(cnf_transformation,[],[f57]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_693,plain,
% 23.48/3.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 23.48/3.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 23.48/3.49      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 23.48/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_27,negated_conjecture,
% 23.48/3.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 23.48/3.49      inference(cnf_transformation,[],[f69]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_681,plain,
% 23.48/3.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_20,plain,
% 23.48/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 23.48/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.48/3.49      | k1_relset_1(X1,X2,X0) = X1
% 23.48/3.49      | k1_xboole_0 = X2 ),
% 23.48/3.49      inference(cnf_transformation,[],[f58]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_687,plain,
% 23.48/3.49      ( k1_relset_1(X0,X1,X2) = X0
% 23.48/3.49      | k1_xboole_0 = X1
% 23.48/3.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 23.48/3.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2306,plain,
% 23.48/3.49      ( k1_relset_1(sK0,sK1,sK3) = sK0
% 23.48/3.49      | sK1 = k1_xboole_0
% 23.48/3.49      | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_681,c_687]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_13,plain,
% 23.48/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.48/3.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 23.48/3.49      inference(cnf_transformation,[],[f56]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_694,plain,
% 23.48/3.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 23.48/3.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2074,plain,
% 23.48/3.49      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_681,c_694]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2320,plain,
% 23.48/3.49      ( k1_relat_1(sK3) = sK0
% 23.48/3.49      | sK1 = k1_xboole_0
% 23.48/3.49      | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
% 23.48/3.49      inference(demodulation,[status(thm)],[c_2306,c_2074]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_28,negated_conjecture,
% 23.48/3.49      ( v1_funct_2(sK3,sK0,sK1) ),
% 23.48/3.49      inference(cnf_transformation,[],[f68]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_31,plain,
% 23.48/3.49      ( v1_funct_2(sK3,sK0,sK1) = iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2810,plain,
% 23.48/3.49      ( sK1 = k1_xboole_0 | k1_relat_1(sK3) = sK0 ),
% 23.48/3.49      inference(global_propositional_subsumption,[status(thm)],[c_2320,c_31]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2811,plain,
% 23.48/3.49      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 23.48/3.49      inference(renaming,[status(thm)],[c_2810]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_12,plain,
% 23.48/3.49      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 23.48/3.49      inference(cnf_transformation,[],[f54]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_695,plain,
% 23.48/3.49      ( v4_relat_1(X0,X1) = iProver_top
% 23.48/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1706,plain,
% 23.48/3.49      ( v4_relat_1(sK3,sK0) = iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_681,c_695]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_8,plain,
% 23.48/3.49      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 23.48/3.49      inference(cnf_transformation,[],[f51]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_699,plain,
% 23.48/3.49      ( k7_relat_1(X0,X1) = X0
% 23.48/3.49      | v4_relat_1(X0,X1) != iProver_top
% 23.48/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2298,plain,
% 23.48/3.49      ( k7_relat_1(sK3,sK0) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_1706,c_699]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_988,plain,
% 23.48/3.49      ( v4_relat_1(sK3,sK0)
% 23.48/3.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_12]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1070,plain,
% 23.48/3.49      ( ~ v4_relat_1(sK3,sK0) | ~ v1_relat_1(sK3) | k7_relat_1(sK3,sK0) = sK3 ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_8]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_4,plain,
% 23.48/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 23.48/3.49      inference(cnf_transformation,[],[f47]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1125,plain,
% 23.48/3.49      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) ),
% 23.48/3.49      inference(resolution,[status(thm)],[c_4,c_27]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_7,plain,
% 23.48/3.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 23.48/3.49      inference(cnf_transformation,[],[f50]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1290,plain,
% 23.48/3.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_7]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2804,plain,
% 23.48/3.49      ( k7_relat_1(sK3,sK0) = sK3 ),
% 23.48/3.49      inference(global_propositional_subsumption,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_2298,c_27,c_988,c_1070,c_1125,c_1290]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_9,plain,
% 23.48/3.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 23.48/3.49      inference(cnf_transformation,[],[f52]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_698,plain,
% 23.48/3.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 23.48/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2807,plain,
% 23.48/3.49      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
% 23.48/3.49      | v1_relat_1(sK3) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_2804,c_698]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1126,plain,
% 23.48/3.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 23.48/3.49      | v1_relat_1(sK3) = iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_1125]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1291,plain,
% 23.48/3.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_1290]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2934,plain,
% 23.48/3.49      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
% 23.48/3.49      inference(global_propositional_subsumption,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_2807,c_1126,c_1291]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2939,plain,
% 23.48/3.49      ( sK1 = k1_xboole_0 | r1_tarski(sK0,sK0) = iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_2811,c_2934]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_703,plain,
% 23.48/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.48/3.49      | v1_relat_1(X1) != iProver_top
% 23.48/3.49      | v1_relat_1(X0) = iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2415,plain,
% 23.48/3.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 23.48/3.49      | v1_relat_1(sK3) = iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_681,c_703]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2658,plain,
% 23.48/3.49      ( v1_relat_1(sK3) = iProver_top ),
% 23.48/3.49      inference(global_propositional_subsumption,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_2415,c_1126,c_1291]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_10,plain,
% 23.48/3.49      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 23.48/3.49      | ~ v1_relat_1(X1)
% 23.48/3.49      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 23.48/3.49      inference(cnf_transformation,[],[f53]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_697,plain,
% 23.48/3.49      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 23.48/3.49      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 23.48/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3140,plain,
% 23.48/3.49      ( k1_relat_1(k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))) = k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))
% 23.48/3.49      | v1_relat_1(X1) != iProver_top
% 23.48/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_698,c_697]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_19462,plain,
% 23.48/3.49      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK3))))) = k1_relat_1(k7_relat_1(X0,k1_relat_1(sK3)))
% 23.48/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_2658,c_3140]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_20719,plain,
% 23.48/3.49      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_2658,c_19462]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_20754,plain,
% 23.48/3.49      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
% 23.48/3.49      | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))) != iProver_top
% 23.48/3.49      | v1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))))) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_20719,c_697]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_23,plain,
% 23.48/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.48/3.49      | ~ v1_funct_1(X0)
% 23.48/3.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 23.48/3.49      inference(cnf_transformation,[],[f66]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_684,plain,
% 23.48/3.49      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 23.48/3.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 23.48/3.49      | v1_funct_1(X2) != iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_5641,plain,
% 23.48/3.49      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 23.48/3.49      | v1_funct_1(sK3) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_681,c_684]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_29,negated_conjecture,
% 23.48/3.49      ( v1_funct_1(sK3) ),
% 23.48/3.49      inference(cnf_transformation,[],[f67]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1032,plain,
% 23.48/3.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.48/3.49      | ~ v1_funct_1(sK3)
% 23.48/3.49      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_23]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1199,plain,
% 23.48/3.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.48/3.49      | ~ v1_funct_1(sK3)
% 23.48/3.49      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_1032]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_5870,plain,
% 23.48/3.49      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 23.48/3.49      inference(global_propositional_subsumption,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_5641,c_29,c_27,c_1199]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_21,plain,
% 23.48/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.48/3.49      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.48/3.49      | ~ v1_funct_1(X0) ),
% 23.48/3.49      inference(cnf_transformation,[],[f65]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_686,plain,
% 23.48/3.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.48/3.49      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 23.48/3.49      | v1_funct_1(X0) != iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_5899,plain,
% 23.48/3.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 23.48/3.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.48/3.49      | v1_funct_1(sK3) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_5870,c_686]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_30,plain,
% 23.48/3.49      ( v1_funct_1(sK3) = iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_32,plain,
% 23.48/3.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1027,plain,
% 23.48/3.49      ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.48/3.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.48/3.49      | ~ v1_funct_1(sK3) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_21]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1211,plain,
% 23.48/3.49      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.48/3.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.48/3.49      | ~ v1_funct_1(sK3) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_1027]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1212,plain,
% 23.48/3.49      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 23.48/3.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.48/3.49      | v1_funct_1(sK3) != iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_1211]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_247,plain,( X0 = X0 ),theory(equality) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1912,plain,
% 23.48/3.49      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_247]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_248,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1809,plain,
% 23.48/3.49      ( X0 != X1
% 23.48/3.49      | X0 = k2_partfun1(sK0,sK1,sK3,X2)
% 23.48/3.49      | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_248]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2638,plain,
% 23.48/3.49      ( X0 = k2_partfun1(sK0,sK1,sK3,X1)
% 23.48/3.49      | X0 != k7_relat_1(sK3,X1)
% 23.48/3.49      | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_1809]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2877,plain,
% 23.48/3.49      ( k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
% 23.48/3.49      | k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
% 23.48/3.49      | k7_relat_1(sK3,X0) != k7_relat_1(sK3,X0) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_2638]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_2878,plain,
% 23.48/3.49      ( k7_relat_1(sK3,X0) = k7_relat_1(sK3,X0) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_247]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_253,plain,
% 23.48/3.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.48/3.49      theory(equality) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1338,plain,
% 23.48/3.49      ( m1_subset_1(X0,X1)
% 23.48/3.49      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.48/3.49      | X0 != k2_partfun1(sK0,sK1,sK3,X2)
% 23.48/3.49      | X1 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_253]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1911,plain,
% 23.48/3.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.48/3.49      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.48/3.49      | X0 != k2_partfun1(sK0,sK1,sK3,X1)
% 23.48/3.49      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_1338]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3743,plain,
% 23.48/3.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.48/3.49      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.48/3.49      | k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
% 23.48/3.49      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 23.48/3.49      inference(instantiation,[status(thm)],[c_1911]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3749,plain,
% 23.48/3.49      ( k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
% 23.48/3.49      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 23.48/3.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.48/3.49      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_3743]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_6164,plain,
% 23.48/3.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 23.48/3.49      inference(global_propositional_subsumption,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_5899,c_29,c_30,c_27,c_32,c_1199,c_1212,c_1912,c_2877,
% 23.48/3.49                 c_2878,c_3749]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_6172,plain,
% 23.48/3.49      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 23.48/3.49      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_6164,c_703]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_7174,plain,
% 23.48/3.49      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 23.48/3.49      inference(global_propositional_subsumption,[status(thm)],[c_6172,c_1291]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_24805,plain,
% 23.48/3.49      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
% 23.48/3.49      | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))) != iProver_top ),
% 23.48/3.49      inference(forward_subsumption_resolution,[status(thm)],[c_20754,c_7174]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_24813,plain,
% 23.48/3.49      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
% 23.48/3.49      | sK1 = k1_xboole_0
% 23.48/3.49      | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,sK0))) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_2811,c_24805]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_24817,plain,
% 23.48/3.49      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
% 23.48/3.49      | sK1 = k1_xboole_0
% 23.48/3.49      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
% 23.48/3.49      inference(light_normalisation,[status(thm)],[c_24813,c_2804]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_28393,plain,
% 23.48/3.49      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),X0)) = X0
% 23.48/3.49      | sK1 = k1_xboole_0
% 23.48/3.49      | r1_tarski(X0,sK0) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_2811,c_24817]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_28435,plain,
% 23.48/3.49      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK0)) = sK0
% 23.48/3.49      | sK1 = k1_xboole_0 ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_2939,c_28393]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_6177,plain,
% 23.48/3.49      ( v4_relat_1(k7_relat_1(sK3,X0),sK0) = iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_6164,c_695]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_6925,plain,
% 23.48/3.49      ( k7_relat_1(k7_relat_1(sK3,X0),sK0) = k7_relat_1(sK3,X0)
% 23.48/3.49      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_6177,c_699]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_8014,plain,
% 23.48/3.49      ( k7_relat_1(k7_relat_1(sK3,X0),sK0) = k7_relat_1(sK3,X0) ),
% 23.48/3.49      inference(global_propositional_subsumption,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_6925,c_1291,c_6172]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_28448,plain,
% 23.48/3.49      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) = sK0 | sK1 = k1_xboole_0 ),
% 23.48/3.49      inference(demodulation,[status(thm)],[c_28435,c_8014,c_20719]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_26,negated_conjecture,
% 23.48/3.49      ( r1_tarski(sK2,sK0) ),
% 23.48/3.49      inference(cnf_transformation,[],[f70]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_682,plain,
% 23.48/3.49      ( r1_tarski(sK2,sK0) = iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3142,plain,
% 23.48/3.49      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 23.48/3.49      | sK1 = k1_xboole_0
% 23.48/3.49      | r1_tarski(X0,sK0) != iProver_top
% 23.48/3.49      | v1_relat_1(sK3) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_2811,c_697]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3464,plain,
% 23.48/3.49      ( r1_tarski(X0,sK0) != iProver_top
% 23.48/3.49      | sK1 = k1_xboole_0
% 23.48/3.49      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 23.48/3.49      inference(global_propositional_subsumption,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_3142,c_1126,c_1291]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3465,plain,
% 23.48/3.49      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 23.48/3.49      | sK1 = k1_xboole_0
% 23.48/3.49      | r1_tarski(X0,sK0) != iProver_top ),
% 23.48/3.49      inference(renaming,[status(thm)],[c_3464]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3473,plain,
% 23.48/3.49      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_682,c_3465]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3647,plain,
% 23.48/3.49      ( sK1 = k1_xboole_0
% 23.48/3.49      | r1_tarski(sK2,sK2) = iProver_top
% 23.48/3.49      | v1_relat_1(sK3) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_3473,c_698]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3668,plain,
% 23.48/3.49      ( r1_tarski(sK2,sK2) = iProver_top | sK1 = k1_xboole_0 ),
% 23.48/3.49      inference(global_propositional_subsumption,
% 23.48/3.49                [status(thm)],
% 23.48/3.49                [c_3647,c_1126,c_1291]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_3669,plain,
% 23.48/3.49      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK2) = iProver_top ),
% 23.48/3.49      inference(renaming,[status(thm)],[c_3668]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_6173,plain,
% 23.48/3.49      ( k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1) = k7_relat_1(k7_relat_1(sK3,X0),X1)
% 23.48/3.49      | v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_6164,c_684]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_22,plain,
% 23.48/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.48/3.49      | ~ v1_funct_1(X0)
% 23.48/3.49      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 23.48/3.49      inference(cnf_transformation,[],[f64]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_685,plain,
% 23.48/3.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.48/3.49      | v1_funct_1(X0) != iProver_top
% 23.48/3.49      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 23.48/3.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_1086,plain,
% 23.48/3.49      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 23.48/3.49      | v1_funct_1(sK3) != iProver_top ),
% 23.48/3.49      inference(superposition,[status(thm)],[c_681,c_685]) ).
% 23.48/3.49  
% 23.48/3.49  cnf(c_258,plain,
% 23.48/3.49      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 23.48/3.50      theory(equality) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_1296,plain,
% 23.48/3.50      ( v1_funct_1(X0)
% 23.48/3.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))
% 23.48/3.50      | X0 != k2_partfun1(sK0,sK1,sK3,X1) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_258]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_3744,plain,
% 23.48/3.50      ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 23.48/3.50      | v1_funct_1(k7_relat_1(sK3,X0))
% 23.48/3.50      | k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_1296]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_3745,plain,
% 23.48/3.50      ( k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
% 23.48/3.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) != iProver_top
% 23.48/3.50      | v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 23.48/3.50      inference(predicate_to_equality,[status(thm)],[c_3744]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_7209,plain,
% 23.48/3.50      ( k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1) = k7_relat_1(k7_relat_1(sK3,X0),X1) ),
% 23.48/3.50      inference(global_propositional_subsumption,
% 23.48/3.50                [status(thm)],
% 23.48/3.50                [c_6173,c_29,c_30,c_27,c_1086,c_1199,c_2877,c_2878,c_3745]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_7220,plain,
% 23.48/3.50      ( m1_subset_1(k7_relat_1(k7_relat_1(sK3,X0),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 23.48/3.50      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.48/3.50      | v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_7209,c_686]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_58151,plain,
% 23.48/3.50      ( m1_subset_1(k7_relat_1(k7_relat_1(sK3,X0),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 23.48/3.50      inference(global_propositional_subsumption,
% 23.48/3.50                [status(thm)],
% 23.48/3.50                [c_7220,c_29,c_30,c_27,c_32,c_1086,c_1199,c_1212,c_1912,
% 23.48/3.50                 c_2877,c_2878,c_3745,c_3749]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_11,plain,
% 23.48/3.50      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 23.48/3.50      inference(cnf_transformation,[],[f55]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_696,plain,
% 23.48/3.50      ( v5_relat_1(X0,X1) = iProver_top
% 23.48/3.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 23.48/3.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_58166,plain,
% 23.48/3.50      ( v5_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1),sK1) = iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_58151,c_696]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_28433,plain,
% 23.48/3.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) = sK2
% 23.48/3.50      | sK1 = k1_xboole_0 ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_682,c_28393]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_4083,plain,
% 23.48/3.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 23.48/3.50      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 23.48/3.50      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 23.48/3.50      | v1_relat_1(X2) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_693,c_694]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_38025,plain,
% 23.48/3.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 23.48/3.50      | v5_relat_1(X2,X1) != iProver_top
% 23.48/3.50      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 23.48/3.50      | v1_relat_1(X2) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_701,c_4083]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_38087,plain,
% 23.48/3.50      ( k1_relset_1(X0,X1,k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2))
% 23.48/3.50      | sK1 = k1_xboole_0
% 23.48/3.50      | v5_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2),X1) != iProver_top
% 23.48/3.50      | r1_tarski(sK2,X0) != iProver_top
% 23.48/3.50      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_28433,c_38025]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_58921,plain,
% 23.48/3.50      ( k1_relset_1(X0,sK1,k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2))
% 23.48/3.50      | sK1 = k1_xboole_0
% 23.48/3.50      | r1_tarski(sK2,X0) != iProver_top
% 23.48/3.50      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_58166,c_38087]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_58160,plain,
% 23.48/3.50      ( v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) = iProver_top
% 23.48/3.50      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_58151,c_703]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_2414,plain,
% 23.48/3.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.48/3.50      | v1_funct_1(X0) != iProver_top
% 23.48/3.50      | v1_relat_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top
% 23.48/3.50      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_686,c_703]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_700,plain,
% 23.48/3.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 23.48/3.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_7690,plain,
% 23.48/3.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.48/3.50      | v1_funct_1(X0) != iProver_top
% 23.48/3.50      | v1_relat_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 23.48/3.50      inference(forward_subsumption_resolution,[status(thm)],[c_2414,c_700]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_7697,plain,
% 23.48/3.50      ( v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top
% 23.48/3.50      | v1_relat_1(k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1)) = iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_6164,c_7690]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_7714,plain,
% 23.48/3.50      ( v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top
% 23.48/3.50      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) = iProver_top ),
% 23.48/3.50      inference(light_normalisation,[status(thm)],[c_7697,c_7209]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_59136,plain,
% 23.48/3.50      ( v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) = iProver_top ),
% 23.48/3.50      inference(global_propositional_subsumption,
% 23.48/3.50                [status(thm)],
% 23.48/3.50                [c_58160,c_29,c_30,c_27,c_1086,c_1199,c_2877,c_2878,c_3745,
% 23.48/3.50                 c_7714]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_61442,plain,
% 23.48/3.50      ( k1_relset_1(X0,sK1,k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2))
% 23.48/3.50      | sK1 = k1_xboole_0
% 23.48/3.50      | r1_tarski(sK2,X0) != iProver_top ),
% 23.48/3.50      inference(forward_subsumption_resolution,[status(thm)],[c_58921,c_59136]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_61447,plain,
% 23.48/3.50      ( k1_relset_1(sK2,sK1,k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2))
% 23.48/3.50      | sK1 = k1_xboole_0 ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_3669,c_61442]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_61613,plain,
% 23.48/3.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(k7_relat_1(sK3,sK0),sK2))
% 23.48/3.50      | sK1 = k1_xboole_0 ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_28448,c_61447]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_61632,plain,
% 23.48/3.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))),sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
% 23.48/3.50      | sK1 = k1_xboole_0 ),
% 23.48/3.50      inference(light_normalisation,[status(thm)],[c_61613,c_2804]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_61649,plain,
% 23.48/3.50      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_61632,c_28433]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_18,plain,
% 23.48/3.50      ( v1_funct_2(X0,X1,X2)
% 23.48/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.48/3.50      | k1_relset_1(X1,X2,X0) != X1
% 23.48/3.50      | k1_xboole_0 = X2 ),
% 23.48/3.50      inference(cnf_transformation,[],[f60]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_689,plain,
% 23.48/3.50      ( k1_relset_1(X0,X1,X2) != X0
% 23.48/3.50      | k1_xboole_0 = X1
% 23.48/3.50      | v1_funct_2(X2,X0,X1) = iProver_top
% 23.48/3.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.48/3.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_62055,plain,
% 23.48/3.50      ( sK1 = k1_xboole_0
% 23.48/3.50      | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) = iProver_top
% 23.48/3.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_61649,c_689]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_24,negated_conjecture,
% 23.48/3.50      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 23.48/3.50      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 23.48/3.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 23.48/3.50      inference(cnf_transformation,[],[f72]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_683,plain,
% 23.48/3.50      ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
% 23.48/3.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 23.48/3.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 23.48/3.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_5875,plain,
% 23.48/3.50      ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) != iProver_top
% 23.48/3.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 23.48/3.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_5870,c_683]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_1349,plain,
% 23.48/3.50      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 23.48/3.50      inference(global_propositional_subsumption,[status(thm)],[c_1086,c_30]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_5876,plain,
% 23.48/3.50      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_5870,c_1349]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_5882,plain,
% 23.48/3.50      ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) != iProver_top
% 23.48/3.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 23.48/3.50      inference(forward_subsumption_resolution,[status(thm)],[c_5875,c_5876]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_62226,plain,
% 23.48/3.50      ( sK1 = k1_xboole_0
% 23.48/3.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 23.48/3.50      inference(global_propositional_subsumption,
% 23.48/3.50                [status(thm)],
% 23.48/3.50                [c_62055,c_5882]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_62232,plain,
% 23.48/3.50      ( sK1 = k1_xboole_0
% 23.48/3.50      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top
% 23.48/3.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 23.48/3.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_693,c_62226]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_3648,plain,
% 23.48/3.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
% 23.48/3.50      | sK1 = k1_xboole_0
% 23.48/3.50      | r1_tarski(X0,sK2) != iProver_top
% 23.48/3.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_3473,c_697]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_7185,plain,
% 23.48/3.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
% 23.48/3.50      | sK1 = k1_xboole_0
% 23.48/3.50      | r1_tarski(X0,sK2) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_7174,c_3648]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_7659,plain,
% 23.48/3.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(X0,sK2)))) = k1_relat_1(k7_relat_1(X0,sK2))
% 23.48/3.50      | sK1 = k1_xboole_0
% 23.48/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_698,c_7185]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_12775,plain,
% 23.48/3.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,sK2))
% 23.48/3.50      | sK1 = k1_xboole_0 ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_2658,c_7659]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_13340,plain,
% 23.48/3.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 23.48/3.50      | sK1 = k1_xboole_0 ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_3473,c_12775]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_13396,plain,
% 23.48/3.50      ( sK1 = k1_xboole_0
% 23.48/3.50      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
% 23.48/3.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_13340,c_698]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_13880,plain,
% 23.48/3.50      ( sK1 = k1_xboole_0
% 23.48/3.50      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top ),
% 23.48/3.50      inference(forward_subsumption_resolution,[status(thm)],[c_13396,c_7174]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_67427,plain,
% 23.48/3.50      ( sK1 = k1_xboole_0
% 23.48/3.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 23.48/3.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 23.48/3.50      inference(global_propositional_subsumption,
% 23.48/3.50                [status(thm)],
% 23.48/3.50                [c_62232,c_13880]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_67434,plain,
% 23.48/3.50      ( sK1 = k1_xboole_0
% 23.48/3.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
% 23.48/3.50      inference(forward_subsumption_resolution,[status(thm)],[c_67427,c_7174]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_67436,plain,
% 23.48/3.50      ( sK1 = k1_xboole_0
% 23.48/3.50      | v5_relat_1(k7_relat_1(sK3,sK2),sK1) != iProver_top
% 23.48/3.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_701,c_67434]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_6176,plain,
% 23.48/3.50      ( v5_relat_1(k7_relat_1(sK3,X0),sK1) = iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_6164,c_696]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_67442,plain,
% 23.48/3.50      ( sK1 = k1_xboole_0 ),
% 23.48/3.50      inference(forward_subsumption_resolution,
% 23.48/3.50                [status(thm)],
% 23.48/3.50                [c_67436,c_7174,c_6176]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_67560,plain,
% 23.48/3.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_67442,c_6164]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_25,negated_conjecture,
% 23.48/3.50      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 23.48/3.50      inference(cnf_transformation,[],[f71]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_67572,plain,
% 23.48/3.50      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_67442,c_25]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_67573,plain,
% 23.48/3.50      ( sK0 = k1_xboole_0 ),
% 23.48/3.50      inference(equality_resolution_simp,[status(thm)],[c_67572]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_67596,plain,
% 23.48/3.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 23.48/3.50      inference(light_normalisation,[status(thm)],[c_67560,c_67573]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_2,plain,
% 23.48/3.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 23.48/3.50      inference(cnf_transformation,[],[f74]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_67598,plain,
% 23.48/3.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_67596,c_2]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_67561,plain,
% 23.48/3.50      ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) != iProver_top
% 23.48/3.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_67442,c_5882]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_1,plain,
% 23.48/3.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 23.48/3.50      inference(cnf_transformation,[],[f73]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_67593,plain,
% 23.48/3.50      ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) != iProver_top
% 23.48/3.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_67561,c_1]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_67600,plain,
% 23.48/3.50      ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) != iProver_top ),
% 23.48/3.50      inference(backward_subsumption_resolution,
% 23.48/3.50                [status(thm)],
% 23.48/3.50                [c_67598,c_67593]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_68807,plain,
% 23.48/3.50      ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_67573,c_2804]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_68809,plain,
% 23.48/3.50      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_67573,c_682]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_0,plain,
% 23.48/3.50      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 23.48/3.50      inference(cnf_transformation,[],[f43]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_704,plain,
% 23.48/3.50      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 23.48/3.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_68934,plain,
% 23.48/3.50      ( sK2 = k1_xboole_0 ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_68809,c_704]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_79751,plain,
% 23.48/3.50      ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 23.48/3.50      inference(light_normalisation,[status(thm)],[c_67600,c_68807,c_68934]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_67570,plain,
% 23.48/3.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_67442,c_681]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_67579,plain,
% 23.48/3.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 23.48/3.50      inference(light_normalisation,[status(thm)],[c_67570,c_67573]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_67581,plain,
% 23.48/3.50      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_67579,c_2]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_2076,plain,
% 23.48/3.50      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 23.48/3.50      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_2,c_694]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_68135,plain,
% 23.48/3.50      ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_relat_1(sK3) ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_67581,c_2076]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_71082,plain,
% 23.48/3.50      ( k1_relat_1(sK3) != k1_xboole_0
% 23.48/3.50      | k1_xboole_0 = X0
% 23.48/3.50      | v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top
% 23.48/3.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_68135,c_689]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_71094,plain,
% 23.48/3.50      ( k1_relat_1(sK3) != k1_xboole_0
% 23.48/3.50      | k1_xboole_0 = X0
% 23.48/3.50      | v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top
% 23.48/3.50      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.48/3.50      inference(light_normalisation,[status(thm)],[c_71082,c_2]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_3,plain,
% 23.48/3.50      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 23.48/3.50      | k1_xboole_0 = X0
% 23.48/3.50      | k1_xboole_0 = X1 ),
% 23.48/3.50      inference(cnf_transformation,[],[f44]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_93,plain,
% 23.48/3.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 23.48/3.50      | k1_xboole_0 = k1_xboole_0 ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_3]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_94,plain,
% 23.48/3.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_2]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_985,plain,
% 23.48/3.50      ( v5_relat_1(sK3,sK1)
% 23.48/3.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_11]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_986,plain,
% 23.48/3.50      ( v5_relat_1(sK3,sK1) = iProver_top
% 23.48/3.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 23.48/3.50      inference(predicate_to_equality,[status(thm)],[c_985]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_991,plain,
% 23.48/3.50      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_248]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_992,plain,
% 23.48/3.50      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_991]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_993,plain,
% 23.48/3.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.48/3.50      | k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_13]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_1067,plain,
% 23.48/3.50      ( ~ v5_relat_1(sK3,sK1)
% 23.48/3.50      | r1_tarski(k2_relat_1(sK3),sK1)
% 23.48/3.50      | ~ v1_relat_1(sK3) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_6]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_1068,plain,
% 23.48/3.50      ( v5_relat_1(sK3,sK1) != iProver_top
% 23.48/3.50      | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
% 23.48/3.50      | v1_relat_1(sK3) != iProver_top ),
% 23.48/3.50      inference(predicate_to_equality,[status(thm)],[c_1067]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_249,plain,
% 23.48/3.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.48/3.50      theory(equality) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_1483,plain,
% 23.48/3.50      ( ~ r1_tarski(X0,X1)
% 23.48/3.50      | r1_tarski(k2_relat_1(X2),X3)
% 23.48/3.50      | X3 != X1
% 23.48/3.50      | k2_relat_1(X2) != X0 ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_249]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_1689,plain,
% 23.48/3.50      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 23.48/3.50      | r1_tarski(k2_relat_1(X0),X2)
% 23.48/3.50      | X2 != X1
% 23.48/3.50      | k2_relat_1(X0) != k2_relat_1(X0) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_1483]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_2647,plain,
% 23.48/3.50      ( r1_tarski(k2_relat_1(sK3),X0)
% 23.48/3.50      | ~ r1_tarski(k2_relat_1(sK3),sK1)
% 23.48/3.50      | X0 != sK1
% 23.48/3.50      | k2_relat_1(sK3) != k2_relat_1(sK3) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_1689]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_2648,plain,
% 23.48/3.50      ( X0 != sK1
% 23.48/3.50      | k2_relat_1(sK3) != k2_relat_1(sK3)
% 23.48/3.50      | r1_tarski(k2_relat_1(sK3),X0) = iProver_top
% 23.48/3.50      | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top ),
% 23.48/3.50      inference(predicate_to_equality,[status(thm)],[c_2647]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_2650,plain,
% 23.48/3.50      ( k2_relat_1(sK3) != k2_relat_1(sK3)
% 23.48/3.50      | k1_xboole_0 != sK1
% 23.48/3.50      | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
% 23.48/3.50      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) = iProver_top ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_2648]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_1690,plain,
% 23.48/3.50      ( k2_relat_1(X0) = k2_relat_1(X0) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_247]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_3088,plain,
% 23.48/3.50      ( k2_relat_1(sK3) = k2_relat_1(sK3) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_1690]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_2056,plain,
% 23.48/3.50      ( X0 != X1 | k1_relat_1(X2) != X1 | k1_relat_1(X2) = X0 ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_248]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_3014,plain,
% 23.48/3.50      ( X0 != k1_relat_1(X1)
% 23.48/3.50      | k1_relat_1(X2) = X0
% 23.48/3.50      | k1_relat_1(X2) != k1_relat_1(X1) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_2056]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_4283,plain,
% 23.48/3.50      ( k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
% 23.48/3.50      | k1_relat_1(X0) = k1_relset_1(sK0,sK1,sK3)
% 23.48/3.50      | k1_relat_1(X0) != k1_relat_1(sK3) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_3014]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_6321,plain,
% 23.48/3.50      ( k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
% 23.48/3.50      | k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
% 23.48/3.50      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_4283]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_2052,plain,
% 23.48/3.50      ( k1_relat_1(X0) = k1_relat_1(X0) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_247]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_6322,plain,
% 23.48/3.50      ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_2052]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_4079,plain,
% 23.48/3.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 23.48/3.50      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 23.48/3.50      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 23.48/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_1,c_693]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_6644,plain,
% 23.48/3.50      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 23.48/3.50      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 23.48/3.50      | v1_relat_1(sK3) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_2934,c_4079]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_6833,plain,
% 23.48/3.50      ( X0 != k1_relset_1(sK0,sK1,sK3)
% 23.48/3.50      | k1_relat_1(sK3) = X0
% 23.48/3.50      | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_2056]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_6834,plain,
% 23.48/3.50      ( k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3)
% 23.48/3.50      | k1_relat_1(sK3) = k1_xboole_0
% 23.48/3.50      | k1_xboole_0 != k1_relset_1(sK0,sK1,sK3) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_6833]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_17324,plain,
% 23.48/3.50      ( ~ r1_tarski(k1_relset_1(sK0,sK1,sK3),k1_xboole_0)
% 23.48/3.50      | k1_xboole_0 = k1_relset_1(sK0,sK1,sK3) ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_0]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_17328,plain,
% 23.48/3.50      ( k1_xboole_0 = k1_relset_1(sK0,sK1,sK3)
% 23.48/3.50      | r1_tarski(k1_relset_1(sK0,sK1,sK3),k1_xboole_0) != iProver_top ),
% 23.48/3.50      inference(predicate_to_equality,[status(thm)],[c_17324]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_2717,plain,
% 23.48/3.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 23.48/3.50      inference(resolution,[status(thm)],[c_249,c_247]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_5155,plain,
% 23.48/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.48/3.50      | r1_tarski(k1_relset_1(X1,X2,X0),X3)
% 23.48/3.50      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 23.48/3.50      inference(resolution,[status(thm)],[c_2717,c_13]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_54670,plain,
% 23.48/3.50      ( r1_tarski(k1_relset_1(sK0,sK1,sK3),X0)
% 23.48/3.50      | ~ r1_tarski(k1_relat_1(sK3),X0) ),
% 23.48/3.50      inference(resolution,[status(thm)],[c_5155,c_27]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_54671,plain,
% 23.48/3.50      ( r1_tarski(k1_relset_1(sK0,sK1,sK3),X0) = iProver_top
% 23.48/3.50      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 23.48/3.50      inference(predicate_to_equality,[status(thm)],[c_54670]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_54673,plain,
% 23.48/3.50      ( r1_tarski(k1_relset_1(sK0,sK1,sK3),k1_xboole_0) = iProver_top
% 23.48/3.50      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 23.48/3.50      inference(instantiation,[status(thm)],[c_54671]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_68805,plain,
% 23.48/3.50      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_67573,c_2934]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_17,plain,
% 23.48/3.50      ( v1_funct_2(X0,k1_xboole_0,X1)
% 23.48/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 23.48/3.50      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 23.48/3.50      inference(cnf_transformation,[],[f78]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_690,plain,
% 23.48/3.50      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 23.48/3.50      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 23.48/3.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 23.48/3.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_799,plain,
% 23.48/3.50      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 23.48/3.50      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 23.48/3.50      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.48/3.50      inference(light_normalisation,[status(thm)],[c_690,c_2]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_71083,plain,
% 23.48/3.50      ( k1_relat_1(sK3) != k1_xboole_0
% 23.48/3.50      | v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top
% 23.48/3.50      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_68135,c_799]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_72566,plain,
% 23.48/3.50      ( v1_funct_2(sK3,k1_xboole_0,X0) = iProver_top ),
% 23.48/3.50      inference(global_propositional_subsumption,
% 23.48/3.50                [status(thm)],
% 23.48/3.50                [c_71094,c_27,c_32,c_93,c_94,c_986,c_992,c_993,c_1068,c_1126,
% 23.48/3.50                 c_1291,c_2650,c_3088,c_6321,c_6322,c_6644,c_6834,c_17328,
% 23.48/3.50                 c_54673,c_67442,c_68805,c_71083]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_79753,plain,
% 23.48/3.50      ( $false ),
% 23.48/3.50      inference(forward_subsumption_resolution,[status(thm)],[c_79751,c_72566]) ).
% 23.48/3.50  
% 23.48/3.50  
% 23.48/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.48/3.50  
% 23.48/3.50  ------                               Statistics
% 23.48/3.50  
% 23.48/3.50  ------ Selected
% 23.48/3.50  
% 23.48/3.50  total_time:                             2.551
% 23.48/3.50  
%------------------------------------------------------------------------------
