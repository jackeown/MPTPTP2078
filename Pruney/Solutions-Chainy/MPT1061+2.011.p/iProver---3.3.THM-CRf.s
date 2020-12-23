%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:31 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 789 expanded)
%              Number of clauses        :   94 ( 272 expanded)
%              Number of leaves         :   13 ( 181 expanded)
%              Depth                    :   18
%              Number of atoms          :  462 (4872 expanded)
%              Number of equality atoms :  184 ( 483 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f27])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(k2_partfun1(X0,X3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(k2_partfun1(X0,X3,sK4,X1),X1,X2)
          | ~ v1_funct_1(k2_partfun1(X0,X3,sK4,X1)) )
        & r1_tarski(k7_relset_1(X0,X3,sK4,X1),X2)
        & r1_tarski(X1,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_2(sK4,X0,X3)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
            & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
            & r1_tarski(X1,X0)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
            | ~ v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2)
            | ~ v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1)) )
          & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2)
          & r1_tarski(sK1,sK0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
          & v1_funct_2(X4,sK0,sK3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    & v1_funct_2(sK4,sK0,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f28,f31,f30])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f51,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1158,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1624,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1158])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1164,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1618,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
    | v1_relat_1(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1164])).

cnf(c_2028,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_1618])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1165,plain,
    ( ~ v1_relat_1(X0_49)
    | k2_relat_1(k7_relat_1(X0_49,X1_49)) = k9_relat_1(X0_49,X1_49) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1617,plain,
    ( k2_relat_1(k7_relat_1(X0_49,X1_49)) = k9_relat_1(X0_49,X1_49)
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1165])).

cnf(c_2200,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0_49)) = k9_relat_1(sK4,X0_49) ),
    inference(superposition,[status(thm)],[c_2028,c_1617])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_397,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_398,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_1153,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_49),sK2)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_398])).

cnf(c_1628,plain,
    ( k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_49),sK2))) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1153])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1162,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | k7_relset_1(X1_49,X2_49,X0_49,X3_49) = k9_relat_1(X0_49,X3_49) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1620,plain,
    ( k7_relset_1(X0_49,X1_49,X2_49,X3_49) = k9_relat_1(X2_49,X3_49)
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1162])).

cnf(c_2084,plain,
    ( k7_relset_1(sK0,sK3,sK4,X0_49) = k9_relat_1(sK4,X0_49) ),
    inference(superposition,[status(thm)],[c_1624,c_1620])).

cnf(c_2265,plain,
    ( k9_relat_1(sK4,sK1) != k2_relat_1(X0_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_49),sK2))) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1628,c_2084])).

cnf(c_2497,plain,
    ( k9_relat_1(sK4,X0_49) != k9_relat_1(sK4,sK1)
    | m1_subset_1(k7_relat_1(sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X0_49)),sK2))) = iProver_top
    | v1_funct_1(k7_relat_1(sK4,X0_49)) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,X0_49)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2200,c_2265])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_26,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1159,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | ~ v1_funct_1(X0_49)
    | k2_partfun1(X1_49,X2_49,X0_49,X3_49) = k7_relat_1(X0_49,X3_49) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1623,plain,
    ( k2_partfun1(X0_49,X1_49,X2_49,X3_49) = k7_relat_1(X2_49,X3_49)
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X2_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1159])).

cnf(c_2476,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0_49) = k7_relat_1(sK4,X0_49)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_1623])).

cnf(c_1956,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_49,X1_49,sK4,X2_49) = k7_relat_1(sK4,X2_49) ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_2050,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK0,sK3,sK4,X0_49) = k7_relat_1(sK4,X0_49) ),
    inference(instantiation,[status(thm)],[c_1956])).

cnf(c_2557,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0_49) = k7_relat_1(sK4,X0_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2476,c_23,c_21,c_2050])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1160,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1622,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1160])).

cnf(c_2194,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0_49)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_1622])).

cnf(c_28,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1933,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_funct_1(k2_partfun1(X0_49,X1_49,sK4,X2_49))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1160])).

cnf(c_2045,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0_49))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1933])).

cnf(c_2046,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0_49)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2045])).

cnf(c_2257,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0_49)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2194,c_26,c_28,c_2046])).

cnf(c_2564,plain,
    ( v1_funct_1(k7_relat_1(sK4,X0_49)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2557,c_2257])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1161,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | m1_subset_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1621,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
    | m1_subset_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) = iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1161])).

cnf(c_2394,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1621,c_1618])).

cnf(c_2605,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,X0_49)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_2394])).

cnf(c_2617,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,X0_49)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2605,c_2557])).

cnf(c_4108,plain,
    ( k9_relat_1(sK4,X0_49) != k9_relat_1(sK4,sK1)
    | m1_subset_1(k7_relat_1(sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X0_49)),sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2497,c_26,c_2564,c_2617])).

cnf(c_4116,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,sK1)),sK2))) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4108])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_806,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_807,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | k1_relset_1(sK0,sK3,sK4) = sK0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_806])).

cnf(c_809,plain,
    ( k1_relset_1(sK0,sK3,sK4) = sK0
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_807,c_21])).

cnf(c_1143,plain,
    ( k1_relset_1(sK0,sK3,sK4) = sK0
    | k1_xboole_0 = sK3 ),
    inference(subtyping,[status(esa)],[c_809])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1163,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | k1_relset_1(X1_49,X2_49,X0_49) = k1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1619,plain,
    ( k1_relset_1(X0_49,X1_49,X2_49) = k1_relat_1(X2_49)
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1163])).

cnf(c_2080,plain,
    ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1624,c_1619])).

cnf(c_2219,plain,
    ( k1_relat_1(sK4) = sK0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1143,c_2080])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_271,plain,
    ( sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_24])).

cnf(c_1156,plain,
    ( sK3 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_271])).

cnf(c_2734,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2219,c_1156])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_364,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK0
    | k1_relat_1(k7_relat_1(X0,X1)) = X1
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_20])).

cnf(c_365,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK0
    | k1_relat_1(k7_relat_1(X0,sK1)) = sK1 ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_1154,plain,
    ( ~ v1_relat_1(X0_49)
    | k1_relat_1(X0_49) != sK0
    | k1_relat_1(k7_relat_1(X0_49,sK1)) = sK1 ),
    inference(subtyping,[status(esa)],[c_365])).

cnf(c_1627,plain,
    ( k1_relat_1(X0_49) != sK0
    | k1_relat_1(k7_relat_1(X0_49,sK1)) = sK1
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1154])).

cnf(c_2738,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2734,c_1627])).

cnf(c_1922,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1164])).

cnf(c_2016,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k7_relat_1(sK4,sK1)) = sK1
    | k1_relat_1(sK4) != sK0 ),
    inference(instantiation,[status(thm)],[c_1154])).

cnf(c_2866,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2738,c_21,c_1156,c_1922,c_2016,c_2219])).

cnf(c_4117,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4116,c_2866])).

cnf(c_18,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_16,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_379,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_380,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),sK2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_889,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0)
    | k1_relat_1(X0) != sK1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_380])).

cnf(c_890,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_902,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_890,c_3])).

cnf(c_1139,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
    inference(subtyping,[status(esa)],[c_902])).

cnf(c_1641,plain,
    ( k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

cnf(c_1243,plain,
    ( k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

cnf(c_2104,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2045])).

cnf(c_2105,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2104])).

cnf(c_3395,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1641,c_26,c_28,c_1243,c_2105])).

cnf(c_3396,plain,
    ( k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3395])).

cnf(c_3399,plain,
    ( k9_relat_1(sK4,sK1) != k9_relat_1(sK4,sK1)
    | sK1 != sK1
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3396,c_2084,c_2200,c_2557,c_2866])).

cnf(c_3400,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3399])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4117,c_3400])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.55/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.01  
% 2.55/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.55/1.01  
% 2.55/1.01  ------  iProver source info
% 2.55/1.01  
% 2.55/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.55/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.55/1.01  git: non_committed_changes: false
% 2.55/1.01  git: last_make_outside_of_git: false
% 2.55/1.01  
% 2.55/1.01  ------ 
% 2.55/1.01  
% 2.55/1.01  ------ Input Options
% 2.55/1.01  
% 2.55/1.01  --out_options                           all
% 2.55/1.01  --tptp_safe_out                         true
% 2.55/1.01  --problem_path                          ""
% 2.55/1.01  --include_path                          ""
% 2.55/1.01  --clausifier                            res/vclausify_rel
% 2.55/1.01  --clausifier_options                    --mode clausify
% 2.55/1.01  --stdin                                 false
% 2.55/1.01  --stats_out                             all
% 2.55/1.01  
% 2.55/1.01  ------ General Options
% 2.55/1.01  
% 2.55/1.01  --fof                                   false
% 2.55/1.01  --time_out_real                         305.
% 2.55/1.01  --time_out_virtual                      -1.
% 2.55/1.01  --symbol_type_check                     false
% 2.55/1.01  --clausify_out                          false
% 2.55/1.01  --sig_cnt_out                           false
% 2.55/1.01  --trig_cnt_out                          false
% 2.55/1.01  --trig_cnt_out_tolerance                1.
% 2.55/1.01  --trig_cnt_out_sk_spl                   false
% 2.55/1.01  --abstr_cl_out                          false
% 2.55/1.01  
% 2.55/1.01  ------ Global Options
% 2.55/1.01  
% 2.55/1.01  --schedule                              default
% 2.55/1.01  --add_important_lit                     false
% 2.55/1.01  --prop_solver_per_cl                    1000
% 2.55/1.01  --min_unsat_core                        false
% 2.55/1.01  --soft_assumptions                      false
% 2.55/1.01  --soft_lemma_size                       3
% 2.55/1.01  --prop_impl_unit_size                   0
% 2.55/1.01  --prop_impl_unit                        []
% 2.55/1.01  --share_sel_clauses                     true
% 2.55/1.01  --reset_solvers                         false
% 2.55/1.01  --bc_imp_inh                            [conj_cone]
% 2.55/1.01  --conj_cone_tolerance                   3.
% 2.55/1.01  --extra_neg_conj                        none
% 2.55/1.01  --large_theory_mode                     true
% 2.55/1.01  --prolific_symb_bound                   200
% 2.55/1.01  --lt_threshold                          2000
% 2.55/1.01  --clause_weak_htbl                      true
% 2.55/1.01  --gc_record_bc_elim                     false
% 2.55/1.01  
% 2.55/1.01  ------ Preprocessing Options
% 2.55/1.01  
% 2.55/1.01  --preprocessing_flag                    true
% 2.55/1.01  --time_out_prep_mult                    0.1
% 2.55/1.01  --splitting_mode                        input
% 2.55/1.01  --splitting_grd                         true
% 2.55/1.01  --splitting_cvd                         false
% 2.55/1.01  --splitting_cvd_svl                     false
% 2.55/1.01  --splitting_nvd                         32
% 2.55/1.01  --sub_typing                            true
% 2.55/1.01  --prep_gs_sim                           true
% 2.55/1.01  --prep_unflatten                        true
% 2.55/1.01  --prep_res_sim                          true
% 2.55/1.01  --prep_upred                            true
% 2.55/1.01  --prep_sem_filter                       exhaustive
% 2.55/1.01  --prep_sem_filter_out                   false
% 2.55/1.01  --pred_elim                             true
% 2.55/1.01  --res_sim_input                         true
% 2.55/1.01  --eq_ax_congr_red                       true
% 2.55/1.01  --pure_diseq_elim                       true
% 2.55/1.01  --brand_transform                       false
% 2.55/1.01  --non_eq_to_eq                          false
% 2.55/1.01  --prep_def_merge                        true
% 2.55/1.01  --prep_def_merge_prop_impl              false
% 2.55/1.01  --prep_def_merge_mbd                    true
% 2.55/1.01  --prep_def_merge_tr_red                 false
% 2.55/1.01  --prep_def_merge_tr_cl                  false
% 2.55/1.01  --smt_preprocessing                     true
% 2.55/1.01  --smt_ac_axioms                         fast
% 2.55/1.01  --preprocessed_out                      false
% 2.55/1.01  --preprocessed_stats                    false
% 2.55/1.01  
% 2.55/1.01  ------ Abstraction refinement Options
% 2.55/1.01  
% 2.55/1.01  --abstr_ref                             []
% 2.55/1.01  --abstr_ref_prep                        false
% 2.55/1.01  --abstr_ref_until_sat                   false
% 2.55/1.01  --abstr_ref_sig_restrict                funpre
% 2.55/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.55/1.01  --abstr_ref_under                       []
% 2.55/1.01  
% 2.55/1.01  ------ SAT Options
% 2.55/1.01  
% 2.55/1.01  --sat_mode                              false
% 2.55/1.01  --sat_fm_restart_options                ""
% 2.55/1.01  --sat_gr_def                            false
% 2.55/1.01  --sat_epr_types                         true
% 2.55/1.01  --sat_non_cyclic_types                  false
% 2.55/1.01  --sat_finite_models                     false
% 2.55/1.01  --sat_fm_lemmas                         false
% 2.55/1.01  --sat_fm_prep                           false
% 2.55/1.01  --sat_fm_uc_incr                        true
% 2.55/1.01  --sat_out_model                         small
% 2.55/1.01  --sat_out_clauses                       false
% 2.55/1.01  
% 2.55/1.01  ------ QBF Options
% 2.55/1.01  
% 2.55/1.01  --qbf_mode                              false
% 2.55/1.01  --qbf_elim_univ                         false
% 2.55/1.01  --qbf_dom_inst                          none
% 2.55/1.01  --qbf_dom_pre_inst                      false
% 2.55/1.01  --qbf_sk_in                             false
% 2.55/1.01  --qbf_pred_elim                         true
% 2.55/1.01  --qbf_split                             512
% 2.55/1.01  
% 2.55/1.01  ------ BMC1 Options
% 2.55/1.01  
% 2.55/1.01  --bmc1_incremental                      false
% 2.55/1.01  --bmc1_axioms                           reachable_all
% 2.55/1.01  --bmc1_min_bound                        0
% 2.55/1.01  --bmc1_max_bound                        -1
% 2.55/1.01  --bmc1_max_bound_default                -1
% 2.55/1.01  --bmc1_symbol_reachability              true
% 2.55/1.01  --bmc1_property_lemmas                  false
% 2.55/1.01  --bmc1_k_induction                      false
% 2.55/1.01  --bmc1_non_equiv_states                 false
% 2.55/1.01  --bmc1_deadlock                         false
% 2.55/1.01  --bmc1_ucm                              false
% 2.55/1.01  --bmc1_add_unsat_core                   none
% 2.55/1.01  --bmc1_unsat_core_children              false
% 2.55/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.55/1.01  --bmc1_out_stat                         full
% 2.55/1.01  --bmc1_ground_init                      false
% 2.55/1.01  --bmc1_pre_inst_next_state              false
% 2.55/1.01  --bmc1_pre_inst_state                   false
% 2.55/1.01  --bmc1_pre_inst_reach_state             false
% 2.55/1.01  --bmc1_out_unsat_core                   false
% 2.55/1.01  --bmc1_aig_witness_out                  false
% 2.55/1.01  --bmc1_verbose                          false
% 2.55/1.01  --bmc1_dump_clauses_tptp                false
% 2.55/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.55/1.01  --bmc1_dump_file                        -
% 2.55/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.55/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.55/1.01  --bmc1_ucm_extend_mode                  1
% 2.55/1.01  --bmc1_ucm_init_mode                    2
% 2.55/1.01  --bmc1_ucm_cone_mode                    none
% 2.55/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.55/1.01  --bmc1_ucm_relax_model                  4
% 2.55/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.55/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.55/1.01  --bmc1_ucm_layered_model                none
% 2.55/1.01  --bmc1_ucm_max_lemma_size               10
% 2.55/1.01  
% 2.55/1.01  ------ AIG Options
% 2.55/1.01  
% 2.55/1.01  --aig_mode                              false
% 2.55/1.01  
% 2.55/1.01  ------ Instantiation Options
% 2.55/1.01  
% 2.55/1.01  --instantiation_flag                    true
% 2.55/1.01  --inst_sos_flag                         false
% 2.55/1.01  --inst_sos_phase                        true
% 2.55/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.55/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.55/1.01  --inst_lit_sel_side                     num_symb
% 2.55/1.01  --inst_solver_per_active                1400
% 2.55/1.01  --inst_solver_calls_frac                1.
% 2.55/1.01  --inst_passive_queue_type               priority_queues
% 2.55/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.55/1.01  --inst_passive_queues_freq              [25;2]
% 2.55/1.01  --inst_dismatching                      true
% 2.55/1.01  --inst_eager_unprocessed_to_passive     true
% 2.55/1.01  --inst_prop_sim_given                   true
% 2.55/1.01  --inst_prop_sim_new                     false
% 2.55/1.01  --inst_subs_new                         false
% 2.55/1.01  --inst_eq_res_simp                      false
% 2.55/1.01  --inst_subs_given                       false
% 2.55/1.01  --inst_orphan_elimination               true
% 2.55/1.01  --inst_learning_loop_flag               true
% 2.55/1.01  --inst_learning_start                   3000
% 2.55/1.01  --inst_learning_factor                  2
% 2.55/1.01  --inst_start_prop_sim_after_learn       3
% 2.55/1.01  --inst_sel_renew                        solver
% 2.55/1.01  --inst_lit_activity_flag                true
% 2.55/1.01  --inst_restr_to_given                   false
% 2.55/1.01  --inst_activity_threshold               500
% 2.55/1.01  --inst_out_proof                        true
% 2.55/1.01  
% 2.55/1.01  ------ Resolution Options
% 2.55/1.01  
% 2.55/1.01  --resolution_flag                       true
% 2.55/1.01  --res_lit_sel                           adaptive
% 2.55/1.01  --res_lit_sel_side                      none
% 2.55/1.01  --res_ordering                          kbo
% 2.55/1.01  --res_to_prop_solver                    active
% 2.55/1.01  --res_prop_simpl_new                    false
% 2.55/1.01  --res_prop_simpl_given                  true
% 2.55/1.01  --res_passive_queue_type                priority_queues
% 2.55/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.55/1.01  --res_passive_queues_freq               [15;5]
% 2.55/1.01  --res_forward_subs                      full
% 2.55/1.01  --res_backward_subs                     full
% 2.55/1.01  --res_forward_subs_resolution           true
% 2.55/1.01  --res_backward_subs_resolution          true
% 2.55/1.01  --res_orphan_elimination                true
% 2.55/1.01  --res_time_limit                        2.
% 2.55/1.01  --res_out_proof                         true
% 2.55/1.01  
% 2.55/1.01  ------ Superposition Options
% 2.55/1.01  
% 2.55/1.01  --superposition_flag                    true
% 2.55/1.01  --sup_passive_queue_type                priority_queues
% 2.55/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.55/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.55/1.01  --demod_completeness_check              fast
% 2.55/1.01  --demod_use_ground                      true
% 2.55/1.01  --sup_to_prop_solver                    passive
% 2.55/1.01  --sup_prop_simpl_new                    true
% 2.55/1.01  --sup_prop_simpl_given                  true
% 2.55/1.01  --sup_fun_splitting                     false
% 2.55/1.01  --sup_smt_interval                      50000
% 2.55/1.01  
% 2.55/1.01  ------ Superposition Simplification Setup
% 2.55/1.01  
% 2.55/1.01  --sup_indices_passive                   []
% 2.55/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.55/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.01  --sup_full_bw                           [BwDemod]
% 2.55/1.01  --sup_immed_triv                        [TrivRules]
% 2.55/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.55/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.01  --sup_immed_bw_main                     []
% 2.55/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.55/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/1.01  
% 2.55/1.01  ------ Combination Options
% 2.55/1.01  
% 2.55/1.01  --comb_res_mult                         3
% 2.55/1.01  --comb_sup_mult                         2
% 2.55/1.01  --comb_inst_mult                        10
% 2.55/1.01  
% 2.55/1.01  ------ Debug Options
% 2.55/1.01  
% 2.55/1.01  --dbg_backtrace                         false
% 2.55/1.01  --dbg_dump_prop_clauses                 false
% 2.55/1.01  --dbg_dump_prop_clauses_file            -
% 2.55/1.01  --dbg_out_stat                          false
% 2.55/1.01  ------ Parsing...
% 2.55/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.55/1.01  
% 2.55/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.55/1.01  
% 2.55/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.55/1.01  
% 2.55/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.55/1.01  ------ Proving...
% 2.55/1.01  ------ Problem Properties 
% 2.55/1.01  
% 2.55/1.01  
% 2.55/1.01  clauses                                 28
% 2.55/1.01  conjectures                             2
% 2.55/1.01  EPR                                     2
% 2.55/1.01  Horn                                    23
% 2.55/1.01  unary                                   3
% 2.55/1.01  binary                                  5
% 2.55/1.01  lits                                    100
% 2.55/1.01  lits eq                                 50
% 2.55/1.01  fd_pure                                 0
% 2.55/1.01  fd_pseudo                               0
% 2.55/1.01  fd_cond                                 2
% 2.55/1.01  fd_pseudo_cond                          0
% 2.55/1.01  AC symbols                              0
% 2.55/1.01  
% 2.55/1.01  ------ Schedule dynamic 5 is on 
% 2.55/1.01  
% 2.55/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.55/1.01  
% 2.55/1.01  
% 2.55/1.01  ------ 
% 2.55/1.01  Current options:
% 2.55/1.01  ------ 
% 2.55/1.01  
% 2.55/1.01  ------ Input Options
% 2.55/1.01  
% 2.55/1.01  --out_options                           all
% 2.55/1.01  --tptp_safe_out                         true
% 2.55/1.01  --problem_path                          ""
% 2.55/1.01  --include_path                          ""
% 2.55/1.01  --clausifier                            res/vclausify_rel
% 2.55/1.01  --clausifier_options                    --mode clausify
% 2.55/1.01  --stdin                                 false
% 2.55/1.01  --stats_out                             all
% 2.55/1.01  
% 2.55/1.01  ------ General Options
% 2.55/1.01  
% 2.55/1.01  --fof                                   false
% 2.55/1.01  --time_out_real                         305.
% 2.55/1.01  --time_out_virtual                      -1.
% 2.55/1.01  --symbol_type_check                     false
% 2.55/1.01  --clausify_out                          false
% 2.55/1.01  --sig_cnt_out                           false
% 2.55/1.01  --trig_cnt_out                          false
% 2.55/1.01  --trig_cnt_out_tolerance                1.
% 2.55/1.01  --trig_cnt_out_sk_spl                   false
% 2.55/1.01  --abstr_cl_out                          false
% 2.55/1.01  
% 2.55/1.01  ------ Global Options
% 2.55/1.01  
% 2.55/1.01  --schedule                              default
% 2.55/1.01  --add_important_lit                     false
% 2.55/1.01  --prop_solver_per_cl                    1000
% 2.55/1.01  --min_unsat_core                        false
% 2.55/1.01  --soft_assumptions                      false
% 2.55/1.01  --soft_lemma_size                       3
% 2.55/1.01  --prop_impl_unit_size                   0
% 2.55/1.01  --prop_impl_unit                        []
% 2.55/1.01  --share_sel_clauses                     true
% 2.55/1.01  --reset_solvers                         false
% 2.55/1.01  --bc_imp_inh                            [conj_cone]
% 2.55/1.01  --conj_cone_tolerance                   3.
% 2.55/1.01  --extra_neg_conj                        none
% 2.55/1.01  --large_theory_mode                     true
% 2.55/1.01  --prolific_symb_bound                   200
% 2.55/1.01  --lt_threshold                          2000
% 2.55/1.01  --clause_weak_htbl                      true
% 2.55/1.01  --gc_record_bc_elim                     false
% 2.55/1.01  
% 2.55/1.01  ------ Preprocessing Options
% 2.55/1.01  
% 2.55/1.01  --preprocessing_flag                    true
% 2.55/1.01  --time_out_prep_mult                    0.1
% 2.55/1.01  --splitting_mode                        input
% 2.55/1.01  --splitting_grd                         true
% 2.55/1.01  --splitting_cvd                         false
% 2.55/1.01  --splitting_cvd_svl                     false
% 2.55/1.01  --splitting_nvd                         32
% 2.55/1.01  --sub_typing                            true
% 2.55/1.01  --prep_gs_sim                           true
% 2.55/1.01  --prep_unflatten                        true
% 2.55/1.01  --prep_res_sim                          true
% 2.55/1.01  --prep_upred                            true
% 2.55/1.01  --prep_sem_filter                       exhaustive
% 2.55/1.01  --prep_sem_filter_out                   false
% 2.55/1.01  --pred_elim                             true
% 2.55/1.01  --res_sim_input                         true
% 2.55/1.01  --eq_ax_congr_red                       true
% 2.55/1.01  --pure_diseq_elim                       true
% 2.55/1.01  --brand_transform                       false
% 2.55/1.01  --non_eq_to_eq                          false
% 2.55/1.01  --prep_def_merge                        true
% 2.55/1.01  --prep_def_merge_prop_impl              false
% 2.55/1.01  --prep_def_merge_mbd                    true
% 2.55/1.01  --prep_def_merge_tr_red                 false
% 2.55/1.01  --prep_def_merge_tr_cl                  false
% 2.55/1.01  --smt_preprocessing                     true
% 2.55/1.01  --smt_ac_axioms                         fast
% 2.55/1.01  --preprocessed_out                      false
% 2.55/1.01  --preprocessed_stats                    false
% 2.55/1.01  
% 2.55/1.01  ------ Abstraction refinement Options
% 2.55/1.01  
% 2.55/1.01  --abstr_ref                             []
% 2.55/1.01  --abstr_ref_prep                        false
% 2.55/1.01  --abstr_ref_until_sat                   false
% 2.55/1.01  --abstr_ref_sig_restrict                funpre
% 2.55/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.55/1.01  --abstr_ref_under                       []
% 2.55/1.01  
% 2.55/1.01  ------ SAT Options
% 2.55/1.01  
% 2.55/1.01  --sat_mode                              false
% 2.55/1.01  --sat_fm_restart_options                ""
% 2.55/1.01  --sat_gr_def                            false
% 2.55/1.01  --sat_epr_types                         true
% 2.55/1.01  --sat_non_cyclic_types                  false
% 2.55/1.01  --sat_finite_models                     false
% 2.55/1.01  --sat_fm_lemmas                         false
% 2.55/1.01  --sat_fm_prep                           false
% 2.55/1.01  --sat_fm_uc_incr                        true
% 2.55/1.01  --sat_out_model                         small
% 2.55/1.01  --sat_out_clauses                       false
% 2.55/1.01  
% 2.55/1.01  ------ QBF Options
% 2.55/1.01  
% 2.55/1.01  --qbf_mode                              false
% 2.55/1.01  --qbf_elim_univ                         false
% 2.55/1.01  --qbf_dom_inst                          none
% 2.55/1.01  --qbf_dom_pre_inst                      false
% 2.55/1.01  --qbf_sk_in                             false
% 2.55/1.01  --qbf_pred_elim                         true
% 2.55/1.01  --qbf_split                             512
% 2.55/1.01  
% 2.55/1.01  ------ BMC1 Options
% 2.55/1.01  
% 2.55/1.01  --bmc1_incremental                      false
% 2.55/1.01  --bmc1_axioms                           reachable_all
% 2.55/1.01  --bmc1_min_bound                        0
% 2.55/1.01  --bmc1_max_bound                        -1
% 2.55/1.01  --bmc1_max_bound_default                -1
% 2.55/1.01  --bmc1_symbol_reachability              true
% 2.55/1.01  --bmc1_property_lemmas                  false
% 2.55/1.01  --bmc1_k_induction                      false
% 2.55/1.01  --bmc1_non_equiv_states                 false
% 2.55/1.01  --bmc1_deadlock                         false
% 2.55/1.01  --bmc1_ucm                              false
% 2.55/1.01  --bmc1_add_unsat_core                   none
% 2.55/1.01  --bmc1_unsat_core_children              false
% 2.55/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.55/1.01  --bmc1_out_stat                         full
% 2.55/1.01  --bmc1_ground_init                      false
% 2.55/1.01  --bmc1_pre_inst_next_state              false
% 2.55/1.01  --bmc1_pre_inst_state                   false
% 2.55/1.01  --bmc1_pre_inst_reach_state             false
% 2.55/1.01  --bmc1_out_unsat_core                   false
% 2.55/1.01  --bmc1_aig_witness_out                  false
% 2.55/1.01  --bmc1_verbose                          false
% 2.55/1.01  --bmc1_dump_clauses_tptp                false
% 2.55/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.55/1.01  --bmc1_dump_file                        -
% 2.55/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.55/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.55/1.01  --bmc1_ucm_extend_mode                  1
% 2.55/1.01  --bmc1_ucm_init_mode                    2
% 2.55/1.01  --bmc1_ucm_cone_mode                    none
% 2.55/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.55/1.01  --bmc1_ucm_relax_model                  4
% 2.55/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.55/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.55/1.01  --bmc1_ucm_layered_model                none
% 2.55/1.01  --bmc1_ucm_max_lemma_size               10
% 2.55/1.01  
% 2.55/1.01  ------ AIG Options
% 2.55/1.01  
% 2.55/1.01  --aig_mode                              false
% 2.55/1.01  
% 2.55/1.01  ------ Instantiation Options
% 2.55/1.01  
% 2.55/1.01  --instantiation_flag                    true
% 2.55/1.01  --inst_sos_flag                         false
% 2.55/1.01  --inst_sos_phase                        true
% 2.55/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.55/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.55/1.01  --inst_lit_sel_side                     none
% 2.55/1.01  --inst_solver_per_active                1400
% 2.55/1.01  --inst_solver_calls_frac                1.
% 2.55/1.01  --inst_passive_queue_type               priority_queues
% 2.55/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.55/1.01  --inst_passive_queues_freq              [25;2]
% 2.55/1.01  --inst_dismatching                      true
% 2.55/1.01  --inst_eager_unprocessed_to_passive     true
% 2.55/1.01  --inst_prop_sim_given                   true
% 2.55/1.01  --inst_prop_sim_new                     false
% 2.55/1.01  --inst_subs_new                         false
% 2.55/1.01  --inst_eq_res_simp                      false
% 2.55/1.01  --inst_subs_given                       false
% 2.55/1.01  --inst_orphan_elimination               true
% 2.55/1.01  --inst_learning_loop_flag               true
% 2.55/1.01  --inst_learning_start                   3000
% 2.55/1.01  --inst_learning_factor                  2
% 2.55/1.01  --inst_start_prop_sim_after_learn       3
% 2.55/1.01  --inst_sel_renew                        solver
% 2.55/1.01  --inst_lit_activity_flag                true
% 2.55/1.01  --inst_restr_to_given                   false
% 2.55/1.01  --inst_activity_threshold               500
% 2.55/1.01  --inst_out_proof                        true
% 2.55/1.01  
% 2.55/1.01  ------ Resolution Options
% 2.55/1.01  
% 2.55/1.01  --resolution_flag                       false
% 2.55/1.01  --res_lit_sel                           adaptive
% 2.55/1.01  --res_lit_sel_side                      none
% 2.55/1.01  --res_ordering                          kbo
% 2.55/1.01  --res_to_prop_solver                    active
% 2.55/1.01  --res_prop_simpl_new                    false
% 2.55/1.01  --res_prop_simpl_given                  true
% 2.55/1.01  --res_passive_queue_type                priority_queues
% 2.55/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.55/1.01  --res_passive_queues_freq               [15;5]
% 2.55/1.01  --res_forward_subs                      full
% 2.55/1.01  --res_backward_subs                     full
% 2.55/1.01  --res_forward_subs_resolution           true
% 2.55/1.01  --res_backward_subs_resolution          true
% 2.55/1.01  --res_orphan_elimination                true
% 2.55/1.01  --res_time_limit                        2.
% 2.55/1.01  --res_out_proof                         true
% 2.55/1.01  
% 2.55/1.01  ------ Superposition Options
% 2.55/1.01  
% 2.55/1.01  --superposition_flag                    true
% 2.55/1.01  --sup_passive_queue_type                priority_queues
% 2.55/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.55/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.55/1.01  --demod_completeness_check              fast
% 2.55/1.01  --demod_use_ground                      true
% 2.55/1.01  --sup_to_prop_solver                    passive
% 2.55/1.01  --sup_prop_simpl_new                    true
% 2.55/1.01  --sup_prop_simpl_given                  true
% 2.55/1.01  --sup_fun_splitting                     false
% 2.55/1.01  --sup_smt_interval                      50000
% 2.55/1.01  
% 2.55/1.01  ------ Superposition Simplification Setup
% 2.55/1.01  
% 2.55/1.01  --sup_indices_passive                   []
% 2.55/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.55/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.01  --sup_full_bw                           [BwDemod]
% 2.55/1.01  --sup_immed_triv                        [TrivRules]
% 2.55/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.55/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.01  --sup_immed_bw_main                     []
% 2.55/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.55/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/1.01  
% 2.55/1.01  ------ Combination Options
% 2.55/1.01  
% 2.55/1.01  --comb_res_mult                         3
% 2.55/1.01  --comb_sup_mult                         2
% 2.55/1.01  --comb_inst_mult                        10
% 2.55/1.01  
% 2.55/1.01  ------ Debug Options
% 2.55/1.01  
% 2.55/1.01  --dbg_backtrace                         false
% 2.55/1.01  --dbg_dump_prop_clauses                 false
% 2.55/1.01  --dbg_dump_prop_clauses_file            -
% 2.55/1.01  --dbg_out_stat                          false
% 2.55/1.01  
% 2.55/1.01  
% 2.55/1.01  
% 2.55/1.01  
% 2.55/1.01  ------ Proving...
% 2.55/1.01  
% 2.55/1.01  
% 2.55/1.01  % SZS status Theorem for theBenchmark.p
% 2.55/1.01  
% 2.55/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.55/1.01  
% 2.55/1.01  fof(f11,conjecture,(
% 2.55/1.01    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 2.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.55/1.01  
% 2.55/1.01  fof(f12,negated_conjecture,(
% 2.55/1.01    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 2.55/1.01    inference(negated_conjecture,[],[f11])).
% 2.55/1.01  
% 2.55/1.01  fof(f27,plain,(
% 2.55/1.01    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 2.55/1.01    inference(ennf_transformation,[],[f12])).
% 2.55/1.01  
% 2.55/1.01  fof(f28,plain,(
% 2.55/1.01    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 2.55/1.01    inference(flattening,[],[f27])).
% 2.55/1.01  
% 2.55/1.01  fof(f31,plain,(
% 2.55/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(X0,X3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,sK4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,sK4,X1))) & r1_tarski(k7_relset_1(X0,X3,sK4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(sK4,X0,X3) & v1_funct_1(sK4))) )),
% 2.55/1.01    introduced(choice_axiom,[])).
% 2.55/1.01  
% 2.55/1.01  fof(f30,plain,(
% 2.55/1.01    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) & ~v1_xboole_0(sK3))),
% 2.55/1.01    introduced(choice_axiom,[])).
% 2.55/1.01  
% 2.55/1.01  fof(f32,plain,(
% 2.55/1.01    ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 2.55/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f28,f31,f30])).
% 2.55/1.01  
% 2.55/1.01  fof(f54,plain,(
% 2.55/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 2.55/1.01    inference(cnf_transformation,[],[f32])).
% 2.55/1.01  
% 2.55/1.01  fof(f4,axiom,(
% 2.55/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.55/1.01  
% 2.55/1.01  fof(f16,plain,(
% 2.55/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.01    inference(ennf_transformation,[],[f4])).
% 2.55/1.01  
% 2.55/1.01  fof(f36,plain,(
% 2.55/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.55/1.01    inference(cnf_transformation,[],[f16])).
% 2.55/1.01  
% 2.55/1.01  fof(f2,axiom,(
% 2.55/1.01    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.55/1.01  
% 2.55/1.01  fof(f13,plain,(
% 2.55/1.01    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.55/1.01    inference(ennf_transformation,[],[f2])).
% 2.55/1.01  
% 2.55/1.01  fof(f34,plain,(
% 2.55/1.01    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.55/1.01    inference(cnf_transformation,[],[f13])).
% 2.55/1.01  
% 2.55/1.01  fof(f10,axiom,(
% 2.55/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.55/1.01  
% 2.55/1.01  fof(f25,plain,(
% 2.55/1.01    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.55/1.01    inference(ennf_transformation,[],[f10])).
% 2.55/1.01  
% 2.55/1.01  fof(f26,plain,(
% 2.55/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.55/1.01    inference(flattening,[],[f25])).
% 2.55/1.01  
% 2.55/1.01  fof(f50,plain,(
% 2.55/1.01    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.55/1.01    inference(cnf_transformation,[],[f26])).
% 2.55/1.01  
% 2.55/1.01  fof(f56,plain,(
% 2.55/1.01    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 2.55/1.01    inference(cnf_transformation,[],[f32])).
% 2.55/1.01  
% 2.55/1.01  fof(f6,axiom,(
% 2.55/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.55/1.01  
% 2.55/1.01  fof(f18,plain,(
% 2.55/1.01    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.01    inference(ennf_transformation,[],[f6])).
% 2.55/1.01  
% 2.55/1.01  fof(f38,plain,(
% 2.55/1.01    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.55/1.01    inference(cnf_transformation,[],[f18])).
% 2.55/1.01  
% 2.55/1.01  fof(f52,plain,(
% 2.55/1.01    v1_funct_1(sK4)),
% 2.55/1.01    inference(cnf_transformation,[],[f32])).
% 2.55/1.01  
% 2.55/1.01  fof(f9,axiom,(
% 2.55/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.55/1.01  
% 2.55/1.01  fof(f23,plain,(
% 2.55/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.55/1.01    inference(ennf_transformation,[],[f9])).
% 2.55/1.01  
% 2.55/1.01  fof(f24,plain,(
% 2.55/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.55/1.01    inference(flattening,[],[f23])).
% 2.55/1.01  
% 2.55/1.01  fof(f47,plain,(
% 2.55/1.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.55/1.01    inference(cnf_transformation,[],[f24])).
% 2.55/1.01  
% 2.55/1.01  fof(f8,axiom,(
% 2.55/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 2.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.55/1.01  
% 2.55/1.01  fof(f21,plain,(
% 2.55/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.55/1.01    inference(ennf_transformation,[],[f8])).
% 2.55/1.01  
% 2.55/1.01  fof(f22,plain,(
% 2.55/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.55/1.01    inference(flattening,[],[f21])).
% 2.55/1.01  
% 2.55/1.01  fof(f45,plain,(
% 2.55/1.01    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.55/1.01    inference(cnf_transformation,[],[f22])).
% 2.55/1.01  
% 2.55/1.01  fof(f46,plain,(
% 2.55/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.55/1.01    inference(cnf_transformation,[],[f22])).
% 2.55/1.01  
% 2.55/1.01  fof(f7,axiom,(
% 2.55/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.55/1.01  
% 2.55/1.01  fof(f19,plain,(
% 2.55/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.01    inference(ennf_transformation,[],[f7])).
% 2.55/1.01  
% 2.55/1.01  fof(f20,plain,(
% 2.55/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.01    inference(flattening,[],[f19])).
% 2.55/1.01  
% 2.55/1.01  fof(f29,plain,(
% 2.55/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.01    inference(nnf_transformation,[],[f20])).
% 2.55/1.01  
% 2.55/1.01  fof(f39,plain,(
% 2.55/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.55/1.01    inference(cnf_transformation,[],[f29])).
% 2.55/1.01  
% 2.55/1.01  fof(f53,plain,(
% 2.55/1.01    v1_funct_2(sK4,sK0,sK3)),
% 2.55/1.01    inference(cnf_transformation,[],[f32])).
% 2.55/1.01  
% 2.55/1.01  fof(f5,axiom,(
% 2.55/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.55/1.01  
% 2.55/1.01  fof(f17,plain,(
% 2.55/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.55/1.01    inference(ennf_transformation,[],[f5])).
% 2.55/1.01  
% 2.55/1.01  fof(f37,plain,(
% 2.55/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.55/1.01    inference(cnf_transformation,[],[f17])).
% 2.55/1.01  
% 2.55/1.01  fof(f1,axiom,(
% 2.55/1.01    v1_xboole_0(k1_xboole_0)),
% 2.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.55/1.01  
% 2.55/1.01  fof(f33,plain,(
% 2.55/1.01    v1_xboole_0(k1_xboole_0)),
% 2.55/1.01    inference(cnf_transformation,[],[f1])).
% 2.55/1.01  
% 2.55/1.01  fof(f51,plain,(
% 2.55/1.01    ~v1_xboole_0(sK3)),
% 2.55/1.01    inference(cnf_transformation,[],[f32])).
% 2.55/1.01  
% 2.55/1.01  fof(f3,axiom,(
% 2.55/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.55/1.01  
% 2.55/1.01  fof(f14,plain,(
% 2.55/1.01    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.55/1.01    inference(ennf_transformation,[],[f3])).
% 2.55/1.01  
% 2.55/1.01  fof(f15,plain,(
% 2.55/1.01    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.55/1.01    inference(flattening,[],[f14])).
% 2.55/1.01  
% 2.55/1.01  fof(f35,plain,(
% 2.55/1.01    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.55/1.01    inference(cnf_transformation,[],[f15])).
% 2.55/1.01  
% 2.55/1.01  fof(f55,plain,(
% 2.55/1.01    r1_tarski(sK1,sK0)),
% 2.55/1.01    inference(cnf_transformation,[],[f32])).
% 2.55/1.01  
% 2.55/1.01  fof(f57,plain,(
% 2.55/1.01    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 2.55/1.01    inference(cnf_transformation,[],[f32])).
% 2.55/1.01  
% 2.55/1.01  fof(f49,plain,(
% 2.55/1.01    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.55/1.01    inference(cnf_transformation,[],[f26])).
% 2.55/1.01  
% 2.55/1.01  cnf(c_21,negated_conjecture,
% 2.55/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
% 2.55/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1158,negated_conjecture,
% 2.55/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
% 2.55/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1624,plain,
% 2.55/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 2.55/1.01      inference(predicate_to_equality,[status(thm)],[c_1158]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_3,plain,
% 2.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.01      | v1_relat_1(X0) ),
% 2.55/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1164,plain,
% 2.55/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.55/1.01      | v1_relat_1(X0_49) ),
% 2.55/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1618,plain,
% 2.55/1.01      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
% 2.55/1.01      | v1_relat_1(X0_49) = iProver_top ),
% 2.55/1.01      inference(predicate_to_equality,[status(thm)],[c_1164]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2028,plain,
% 2.55/1.01      ( v1_relat_1(sK4) = iProver_top ),
% 2.55/1.01      inference(superposition,[status(thm)],[c_1624,c_1618]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1,plain,
% 2.55/1.01      ( ~ v1_relat_1(X0)
% 2.55/1.01      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.55/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1165,plain,
% 2.55/1.01      ( ~ v1_relat_1(X0_49)
% 2.55/1.01      | k2_relat_1(k7_relat_1(X0_49,X1_49)) = k9_relat_1(X0_49,X1_49) ),
% 2.55/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1617,plain,
% 2.55/1.01      ( k2_relat_1(k7_relat_1(X0_49,X1_49)) = k9_relat_1(X0_49,X1_49)
% 2.55/1.01      | v1_relat_1(X0_49) != iProver_top ),
% 2.55/1.01      inference(predicate_to_equality,[status(thm)],[c_1165]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2200,plain,
% 2.55/1.01      ( k2_relat_1(k7_relat_1(sK4,X0_49)) = k9_relat_1(sK4,X0_49) ),
% 2.55/1.01      inference(superposition,[status(thm)],[c_2028,c_1617]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_15,plain,
% 2.55/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.55/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.55/1.01      | ~ v1_funct_1(X0)
% 2.55/1.01      | ~ v1_relat_1(X0) ),
% 2.55/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_19,negated_conjecture,
% 2.55/1.01      ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
% 2.55/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_397,plain,
% 2.55/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.55/1.01      | ~ v1_funct_1(X0)
% 2.55/1.01      | ~ v1_relat_1(X0)
% 2.55/1.01      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0)
% 2.55/1.01      | sK2 != X1 ),
% 2.55/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_398,plain,
% 2.55/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),sK2)))
% 2.55/1.01      | ~ v1_funct_1(X0)
% 2.55/1.01      | ~ v1_relat_1(X0)
% 2.55/1.01      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0) ),
% 2.55/1.01      inference(unflattening,[status(thm)],[c_397]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1153,plain,
% 2.55/1.01      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_49),sK2)))
% 2.55/1.01      | ~ v1_funct_1(X0_49)
% 2.55/1.01      | ~ v1_relat_1(X0_49)
% 2.55/1.01      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0_49) ),
% 2.55/1.01      inference(subtyping,[status(esa)],[c_398]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1628,plain,
% 2.55/1.01      ( k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0_49)
% 2.55/1.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_49),sK2))) = iProver_top
% 2.55/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.55/1.01      | v1_relat_1(X0_49) != iProver_top ),
% 2.55/1.01      inference(predicate_to_equality,[status(thm)],[c_1153]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_5,plain,
% 2.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.01      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.55/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1162,plain,
% 2.55/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.55/1.01      | k7_relset_1(X1_49,X2_49,X0_49,X3_49) = k9_relat_1(X0_49,X3_49) ),
% 2.55/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1620,plain,
% 2.55/1.01      ( k7_relset_1(X0_49,X1_49,X2_49,X3_49) = k9_relat_1(X2_49,X3_49)
% 2.55/1.01      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 2.55/1.01      inference(predicate_to_equality,[status(thm)],[c_1162]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2084,plain,
% 2.55/1.01      ( k7_relset_1(sK0,sK3,sK4,X0_49) = k9_relat_1(sK4,X0_49) ),
% 2.55/1.01      inference(superposition,[status(thm)],[c_1624,c_1620]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2265,plain,
% 2.55/1.01      ( k9_relat_1(sK4,sK1) != k2_relat_1(X0_49)
% 2.55/1.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_49),sK2))) = iProver_top
% 2.55/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.55/1.01      | v1_relat_1(X0_49) != iProver_top ),
% 2.55/1.01      inference(demodulation,[status(thm)],[c_1628,c_2084]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2497,plain,
% 2.55/1.01      ( k9_relat_1(sK4,X0_49) != k9_relat_1(sK4,sK1)
% 2.55/1.01      | m1_subset_1(k7_relat_1(sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X0_49)),sK2))) = iProver_top
% 2.55/1.01      | v1_funct_1(k7_relat_1(sK4,X0_49)) != iProver_top
% 2.55/1.01      | v1_relat_1(k7_relat_1(sK4,X0_49)) != iProver_top ),
% 2.55/1.01      inference(superposition,[status(thm)],[c_2200,c_2265]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_23,negated_conjecture,
% 2.55/1.01      ( v1_funct_1(sK4) ),
% 2.55/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_26,plain,
% 2.55/1.01      ( v1_funct_1(sK4) = iProver_top ),
% 2.55/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_14,plain,
% 2.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.01      | ~ v1_funct_1(X0)
% 2.55/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.55/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1159,plain,
% 2.55/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.55/1.01      | ~ v1_funct_1(X0_49)
% 2.55/1.01      | k2_partfun1(X1_49,X2_49,X0_49,X3_49) = k7_relat_1(X0_49,X3_49) ),
% 2.55/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1623,plain,
% 2.55/1.01      ( k2_partfun1(X0_49,X1_49,X2_49,X3_49) = k7_relat_1(X2_49,X3_49)
% 2.55/1.01      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 2.55/1.01      | v1_funct_1(X2_49) != iProver_top ),
% 2.55/1.01      inference(predicate_to_equality,[status(thm)],[c_1159]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2476,plain,
% 2.55/1.01      ( k2_partfun1(sK0,sK3,sK4,X0_49) = k7_relat_1(sK4,X0_49)
% 2.55/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.55/1.01      inference(superposition,[status(thm)],[c_1624,c_1623]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1956,plain,
% 2.55/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 2.55/1.01      | ~ v1_funct_1(sK4)
% 2.55/1.01      | k2_partfun1(X0_49,X1_49,sK4,X2_49) = k7_relat_1(sK4,X2_49) ),
% 2.55/1.01      inference(instantiation,[status(thm)],[c_1159]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2050,plain,
% 2.55/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.55/1.01      | ~ v1_funct_1(sK4)
% 2.55/1.01      | k2_partfun1(sK0,sK3,sK4,X0_49) = k7_relat_1(sK4,X0_49) ),
% 2.55/1.01      inference(instantiation,[status(thm)],[c_1956]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2557,plain,
% 2.55/1.01      ( k2_partfun1(sK0,sK3,sK4,X0_49) = k7_relat_1(sK4,X0_49) ),
% 2.55/1.01      inference(global_propositional_subsumption,
% 2.55/1.01                [status(thm)],
% 2.55/1.01                [c_2476,c_23,c_21,c_2050]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_13,plain,
% 2.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.01      | ~ v1_funct_1(X0)
% 2.55/1.01      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 2.55/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1160,plain,
% 2.55/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.55/1.01      | ~ v1_funct_1(X0_49)
% 2.55/1.01      | v1_funct_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49)) ),
% 2.55/1.01      inference(subtyping,[status(esa)],[c_13]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1622,plain,
% 2.55/1.01      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
% 2.55/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.55/1.01      | v1_funct_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49)) = iProver_top ),
% 2.55/1.01      inference(predicate_to_equality,[status(thm)],[c_1160]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2194,plain,
% 2.55/1.01      ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0_49)) = iProver_top
% 2.55/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.55/1.01      inference(superposition,[status(thm)],[c_1624,c_1622]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_28,plain,
% 2.55/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 2.55/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1933,plain,
% 2.55/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 2.55/1.01      | v1_funct_1(k2_partfun1(X0_49,X1_49,sK4,X2_49))
% 2.55/1.01      | ~ v1_funct_1(sK4) ),
% 2.55/1.01      inference(instantiation,[status(thm)],[c_1160]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2045,plain,
% 2.55/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.55/1.01      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0_49))
% 2.55/1.01      | ~ v1_funct_1(sK4) ),
% 2.55/1.01      inference(instantiation,[status(thm)],[c_1933]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2046,plain,
% 2.55/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 2.55/1.01      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0_49)) = iProver_top
% 2.55/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.55/1.01      inference(predicate_to_equality,[status(thm)],[c_2045]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2257,plain,
% 2.55/1.01      ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0_49)) = iProver_top ),
% 2.55/1.01      inference(global_propositional_subsumption,
% 2.55/1.01                [status(thm)],
% 2.55/1.01                [c_2194,c_26,c_28,c_2046]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2564,plain,
% 2.55/1.01      ( v1_funct_1(k7_relat_1(sK4,X0_49)) = iProver_top ),
% 2.55/1.01      inference(demodulation,[status(thm)],[c_2557,c_2257]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_12,plain,
% 2.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.01      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.01      | ~ v1_funct_1(X0) ),
% 2.55/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1161,plain,
% 2.55/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.55/1.01      | m1_subset_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.55/1.01      | ~ v1_funct_1(X0_49) ),
% 2.55/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1621,plain,
% 2.55/1.01      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
% 2.55/1.01      | m1_subset_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) = iProver_top
% 2.55/1.01      | v1_funct_1(X0_49) != iProver_top ),
% 2.55/1.01      inference(predicate_to_equality,[status(thm)],[c_1161]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2394,plain,
% 2.55/1.01      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
% 2.55/1.01      | v1_funct_1(X0_49) != iProver_top
% 2.55/1.01      | v1_relat_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49)) = iProver_top ),
% 2.55/1.01      inference(superposition,[status(thm)],[c_1621,c_1618]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2605,plain,
% 2.55/1.01      ( v1_funct_1(sK4) != iProver_top
% 2.55/1.01      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,X0_49)) = iProver_top ),
% 2.55/1.01      inference(superposition,[status(thm)],[c_1624,c_2394]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2617,plain,
% 2.55/1.01      ( v1_funct_1(sK4) != iProver_top
% 2.55/1.01      | v1_relat_1(k7_relat_1(sK4,X0_49)) = iProver_top ),
% 2.55/1.01      inference(light_normalisation,[status(thm)],[c_2605,c_2557]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_4108,plain,
% 2.55/1.01      ( k9_relat_1(sK4,X0_49) != k9_relat_1(sK4,sK1)
% 2.55/1.01      | m1_subset_1(k7_relat_1(sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X0_49)),sK2))) = iProver_top ),
% 2.55/1.01      inference(global_propositional_subsumption,
% 2.55/1.01                [status(thm)],
% 2.55/1.01                [c_2497,c_26,c_2564,c_2617]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_4116,plain,
% 2.55/1.01      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,sK1)),sK2))) = iProver_top ),
% 2.55/1.01      inference(equality_resolution,[status(thm)],[c_4108]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_11,plain,
% 2.55/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.55/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.55/1.01      | k1_xboole_0 = X2 ),
% 2.55/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_22,negated_conjecture,
% 2.55/1.01      ( v1_funct_2(sK4,sK0,sK3) ),
% 2.55/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_806,plain,
% 2.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.55/1.01      | sK4 != X0
% 2.55/1.01      | sK3 != X2
% 2.55/1.01      | sK0 != X1
% 2.55/1.01      | k1_xboole_0 = X2 ),
% 2.55/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_807,plain,
% 2.55/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.55/1.01      | k1_relset_1(sK0,sK3,sK4) = sK0
% 2.55/1.01      | k1_xboole_0 = sK3 ),
% 2.55/1.01      inference(unflattening,[status(thm)],[c_806]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_809,plain,
% 2.55/1.01      ( k1_relset_1(sK0,sK3,sK4) = sK0 | k1_xboole_0 = sK3 ),
% 2.55/1.01      inference(global_propositional_subsumption,
% 2.55/1.01                [status(thm)],
% 2.55/1.01                [c_807,c_21]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1143,plain,
% 2.55/1.01      ( k1_relset_1(sK0,sK3,sK4) = sK0 | k1_xboole_0 = sK3 ),
% 2.55/1.01      inference(subtyping,[status(esa)],[c_809]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_4,plain,
% 2.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.55/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.55/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1163,plain,
% 2.55/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.55/1.01      | k1_relset_1(X1_49,X2_49,X0_49) = k1_relat_1(X0_49) ),
% 2.55/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1619,plain,
% 2.55/1.01      ( k1_relset_1(X0_49,X1_49,X2_49) = k1_relat_1(X2_49)
% 2.55/1.01      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 2.55/1.01      inference(predicate_to_equality,[status(thm)],[c_1163]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2080,plain,
% 2.55/1.01      ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
% 2.55/1.01      inference(superposition,[status(thm)],[c_1624,c_1619]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2219,plain,
% 2.55/1.01      ( k1_relat_1(sK4) = sK0 | sK3 = k1_xboole_0 ),
% 2.55/1.01      inference(superposition,[status(thm)],[c_1143,c_2080]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_0,plain,
% 2.55/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.55/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_24,negated_conjecture,
% 2.55/1.01      ( ~ v1_xboole_0(sK3) ),
% 2.55/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_271,plain,
% 2.55/1.01      ( sK3 != k1_xboole_0 ),
% 2.55/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_24]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1156,plain,
% 2.55/1.01      ( sK3 != k1_xboole_0 ),
% 2.55/1.01      inference(subtyping,[status(esa)],[c_271]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2734,plain,
% 2.55/1.01      ( k1_relat_1(sK4) = sK0 ),
% 2.55/1.01      inference(global_propositional_subsumption,
% 2.55/1.01                [status(thm)],
% 2.55/1.01                [c_2219,c_1156]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2,plain,
% 2.55/1.01      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 2.55/1.01      | ~ v1_relat_1(X1)
% 2.55/1.01      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 2.55/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_20,negated_conjecture,
% 2.55/1.01      ( r1_tarski(sK1,sK0) ),
% 2.55/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_364,plain,
% 2.55/1.01      ( ~ v1_relat_1(X0)
% 2.55/1.01      | k1_relat_1(X0) != sK0
% 2.55/1.01      | k1_relat_1(k7_relat_1(X0,X1)) = X1
% 2.55/1.01      | sK1 != X1 ),
% 2.55/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_20]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_365,plain,
% 2.55/1.01      ( ~ v1_relat_1(X0)
% 2.55/1.01      | k1_relat_1(X0) != sK0
% 2.55/1.01      | k1_relat_1(k7_relat_1(X0,sK1)) = sK1 ),
% 2.55/1.01      inference(unflattening,[status(thm)],[c_364]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1154,plain,
% 2.55/1.01      ( ~ v1_relat_1(X0_49)
% 2.55/1.01      | k1_relat_1(X0_49) != sK0
% 2.55/1.01      | k1_relat_1(k7_relat_1(X0_49,sK1)) = sK1 ),
% 2.55/1.01      inference(subtyping,[status(esa)],[c_365]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1627,plain,
% 2.55/1.01      ( k1_relat_1(X0_49) != sK0
% 2.55/1.01      | k1_relat_1(k7_relat_1(X0_49,sK1)) = sK1
% 2.55/1.01      | v1_relat_1(X0_49) != iProver_top ),
% 2.55/1.01      inference(predicate_to_equality,[status(thm)],[c_1154]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2738,plain,
% 2.55/1.01      ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1
% 2.55/1.01      | v1_relat_1(sK4) != iProver_top ),
% 2.55/1.01      inference(superposition,[status(thm)],[c_2734,c_1627]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1922,plain,
% 2.55/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.55/1.01      | v1_relat_1(sK4) ),
% 2.55/1.01      inference(instantiation,[status(thm)],[c_1164]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2016,plain,
% 2.55/1.01      ( ~ v1_relat_1(sK4)
% 2.55/1.01      | k1_relat_1(k7_relat_1(sK4,sK1)) = sK1
% 2.55/1.01      | k1_relat_1(sK4) != sK0 ),
% 2.55/1.01      inference(instantiation,[status(thm)],[c_1154]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2866,plain,
% 2.55/1.01      ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1 ),
% 2.55/1.01      inference(global_propositional_subsumption,
% 2.55/1.01                [status(thm)],
% 2.55/1.01                [c_2738,c_21,c_1156,c_1922,c_2016,c_2219]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_4117,plain,
% 2.55/1.01      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.55/1.01      inference(light_normalisation,[status(thm)],[c_4116,c_2866]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_18,negated_conjecture,
% 2.55/1.01      ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
% 2.55/1.01      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.55/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
% 2.55/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_16,plain,
% 2.55/1.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.55/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.55/1.01      | ~ v1_funct_1(X0)
% 2.55/1.01      | ~ v1_relat_1(X0) ),
% 2.55/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_379,plain,
% 2.55/1.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.55/1.01      | ~ v1_funct_1(X0)
% 2.55/1.01      | ~ v1_relat_1(X0)
% 2.55/1.01      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0)
% 2.55/1.01      | sK2 != X1 ),
% 2.55/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_380,plain,
% 2.55/1.01      ( v1_funct_2(X0,k1_relat_1(X0),sK2)
% 2.55/1.01      | ~ v1_funct_1(X0)
% 2.55/1.01      | ~ v1_relat_1(X0)
% 2.55/1.01      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0) ),
% 2.55/1.01      inference(unflattening,[status(thm)],[c_379]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_889,plain,
% 2.55/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.55/1.01      | ~ v1_funct_1(X0)
% 2.55/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.55/1.01      | ~ v1_relat_1(X0)
% 2.55/1.01      | k2_partfun1(sK0,sK3,sK4,sK1) != X0
% 2.55/1.01      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0)
% 2.55/1.01      | k1_relat_1(X0) != sK1
% 2.55/1.01      | sK2 != sK2 ),
% 2.55/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_380]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_890,plain,
% 2.55/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.55/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.55/1.01      | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.55/1.01      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.55/1.01      | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
% 2.55/1.01      inference(unflattening,[status(thm)],[c_889]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_902,plain,
% 2.55/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.55/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.55/1.01      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.55/1.01      | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
% 2.55/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_890,c_3]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1139,plain,
% 2.55/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.55/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.55/1.01      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.55/1.01      | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
% 2.55/1.01      inference(subtyping,[status(esa)],[c_902]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1641,plain,
% 2.55/1.01      ( k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.55/1.01      | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 2.55/1.01      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.55/1.01      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 2.55/1.01      inference(predicate_to_equality,[status(thm)],[c_1139]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_1243,plain,
% 2.55/1.01      ( k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.55/1.01      | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 2.55/1.01      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.55/1.01      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 2.55/1.01      inference(predicate_to_equality,[status(thm)],[c_1139]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2104,plain,
% 2.55/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.55/1.01      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.55/1.01      | ~ v1_funct_1(sK4) ),
% 2.55/1.01      inference(instantiation,[status(thm)],[c_2045]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_2105,plain,
% 2.55/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 2.55/1.01      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) = iProver_top
% 2.55/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.55/1.01      inference(predicate_to_equality,[status(thm)],[c_2104]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_3395,plain,
% 2.55/1.01      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.55/1.01      | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 2.55/1.01      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
% 2.55/1.01      inference(global_propositional_subsumption,
% 2.55/1.01                [status(thm)],
% 2.55/1.01                [c_1641,c_26,c_28,c_1243,c_2105]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_3396,plain,
% 2.55/1.01      ( k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.55/1.01      | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 2.55/1.01      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.55/1.01      inference(renaming,[status(thm)],[c_3395]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_3399,plain,
% 2.55/1.01      ( k9_relat_1(sK4,sK1) != k9_relat_1(sK4,sK1)
% 2.55/1.01      | sK1 != sK1
% 2.55/1.01      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.55/1.01      inference(demodulation,
% 2.55/1.01                [status(thm)],
% 2.55/1.01                [c_3396,c_2084,c_2200,c_2557,c_2866]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(c_3400,plain,
% 2.55/1.01      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.55/1.01      inference(equality_resolution_simp,[status(thm)],[c_3399]) ).
% 2.55/1.01  
% 2.55/1.01  cnf(contradiction,plain,
% 2.55/1.01      ( $false ),
% 2.55/1.01      inference(minisat,[status(thm)],[c_4117,c_3400]) ).
% 2.55/1.01  
% 2.55/1.01  
% 2.55/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.55/1.01  
% 2.55/1.01  ------                               Statistics
% 2.55/1.01  
% 2.55/1.01  ------ General
% 2.55/1.01  
% 2.55/1.01  abstr_ref_over_cycles:                  0
% 2.55/1.01  abstr_ref_under_cycles:                 0
% 2.55/1.01  gc_basic_clause_elim:                   0
% 2.55/1.01  forced_gc_time:                         0
% 2.55/1.01  parsing_time:                           0.011
% 2.55/1.01  unif_index_cands_time:                  0.
% 2.55/1.01  unif_index_add_time:                    0.
% 2.55/1.01  orderings_time:                         0.
% 2.55/1.01  out_proof_time:                         0.011
% 2.55/1.01  total_time:                             0.184
% 2.55/1.01  num_of_symbols:                         55
% 2.55/1.01  num_of_terms:                           3997
% 2.55/1.01  
% 2.55/1.01  ------ Preprocessing
% 2.55/1.01  
% 2.55/1.01  num_of_splits:                          0
% 2.55/1.01  num_of_split_atoms:                     0
% 2.55/1.01  num_of_reused_defs:                     0
% 2.55/1.01  num_eq_ax_congr_red:                    11
% 2.55/1.01  num_of_sem_filtered_clauses:            1
% 2.55/1.01  num_of_subtypes:                        3
% 2.55/1.01  monotx_restored_types:                  0
% 2.55/1.01  sat_num_of_epr_types:                   0
% 2.55/1.01  sat_num_of_non_cyclic_types:            0
% 2.55/1.01  sat_guarded_non_collapsed_types:        1
% 2.55/1.01  num_pure_diseq_elim:                    0
% 2.55/1.01  simp_replaced_by:                       0
% 2.55/1.01  res_preprocessed:                       109
% 2.55/1.01  prep_upred:                             0
% 2.55/1.01  prep_unflattend:                        56
% 2.55/1.01  smt_new_axioms:                         0
% 2.55/1.01  pred_elim_cands:                        6
% 2.55/1.01  pred_elim:                              3
% 2.55/1.01  pred_elim_cl:                           -4
% 2.55/1.01  pred_elim_cycles:                       6
% 2.55/1.01  merged_defs:                            0
% 2.55/1.01  merged_defs_ncl:                        0
% 2.55/1.01  bin_hyper_res:                          0
% 2.55/1.01  prep_cycles:                            3
% 2.55/1.01  pred_elim_time:                         0.018
% 2.55/1.01  splitting_time:                         0.
% 2.55/1.01  sem_filter_time:                        0.
% 2.55/1.01  monotx_time:                            0.
% 2.55/1.01  subtype_inf_time:                       0.001
% 2.55/1.01  
% 2.55/1.01  ------ Problem properties
% 2.55/1.01  
% 2.55/1.01  clauses:                                28
% 2.55/1.01  conjectures:                            2
% 2.55/1.01  epr:                                    2
% 2.55/1.01  horn:                                   23
% 2.55/1.01  ground:                                 11
% 2.55/1.01  unary:                                  3
% 2.55/1.01  binary:                                 5
% 2.55/1.01  lits:                                   100
% 2.55/1.01  lits_eq:                                50
% 2.55/1.01  fd_pure:                                0
% 2.55/1.01  fd_pseudo:                              0
% 2.55/1.01  fd_cond:                                2
% 2.55/1.01  fd_pseudo_cond:                         0
% 2.55/1.01  ac_symbols:                             0
% 2.55/1.01  
% 2.55/1.01  ------ Propositional Solver
% 2.55/1.01  
% 2.55/1.01  prop_solver_calls:                      25
% 2.55/1.01  prop_fast_solver_calls:                 1086
% 2.55/1.01  smt_solver_calls:                       0
% 2.55/1.01  smt_fast_solver_calls:                  0
% 2.55/1.01  prop_num_of_clauses:                    1398
% 2.55/1.01  prop_preprocess_simplified:             4105
% 2.55/1.01  prop_fo_subsumed:                       26
% 2.55/1.01  prop_solver_time:                       0.
% 2.55/1.01  smt_solver_time:                        0.
% 2.55/1.01  smt_fast_solver_time:                   0.
% 2.55/1.01  prop_fast_solver_time:                  0.
% 2.55/1.01  prop_unsat_core_time:                   0.
% 2.55/1.01  
% 2.55/1.01  ------ QBF
% 2.55/1.01  
% 2.55/1.01  qbf_q_res:                              0
% 2.55/1.01  qbf_num_tautologies:                    0
% 2.55/1.01  qbf_prep_cycles:                        0
% 2.55/1.01  
% 2.55/1.01  ------ BMC1
% 2.55/1.01  
% 2.55/1.01  bmc1_current_bound:                     -1
% 2.55/1.01  bmc1_last_solved_bound:                 -1
% 2.55/1.01  bmc1_unsat_core_size:                   -1
% 2.55/1.01  bmc1_unsat_core_parents_size:           -1
% 2.55/1.01  bmc1_merge_next_fun:                    0
% 2.55/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.55/1.01  
% 2.55/1.01  ------ Instantiation
% 2.55/1.01  
% 2.55/1.01  inst_num_of_clauses:                    388
% 2.55/1.01  inst_num_in_passive:                    76
% 2.55/1.01  inst_num_in_active:                     276
% 2.55/1.01  inst_num_in_unprocessed:                36
% 2.55/1.01  inst_num_of_loops:                      290
% 2.55/1.01  inst_num_of_learning_restarts:          0
% 2.55/1.01  inst_num_moves_active_passive:          9
% 2.55/1.01  inst_lit_activity:                      0
% 2.55/1.01  inst_lit_activity_moves:                0
% 2.55/1.01  inst_num_tautologies:                   0
% 2.55/1.01  inst_num_prop_implied:                  0
% 2.55/1.01  inst_num_existing_simplified:           0
% 2.55/1.01  inst_num_eq_res_simplified:             0
% 2.55/1.01  inst_num_child_elim:                    0
% 2.55/1.01  inst_num_of_dismatching_blockings:      63
% 2.55/1.01  inst_num_of_non_proper_insts:           316
% 2.55/1.01  inst_num_of_duplicates:                 0
% 2.55/1.01  inst_inst_num_from_inst_to_res:         0
% 2.55/1.01  inst_dismatching_checking_time:         0.
% 2.55/1.01  
% 2.55/1.01  ------ Resolution
% 2.55/1.01  
% 2.55/1.01  res_num_of_clauses:                     0
% 2.55/1.01  res_num_in_passive:                     0
% 2.55/1.01  res_num_in_active:                      0
% 2.55/1.01  res_num_of_loops:                       112
% 2.55/1.01  res_forward_subset_subsumed:            33
% 2.55/1.01  res_backward_subset_subsumed:           4
% 2.55/1.01  res_forward_subsumed:                   0
% 2.55/1.01  res_backward_subsumed:                  0
% 2.55/1.01  res_forward_subsumption_resolution:     6
% 2.55/1.01  res_backward_subsumption_resolution:    0
% 2.55/1.01  res_clause_to_clause_subsumption:       129
% 2.55/1.01  res_orphan_elimination:                 0
% 2.55/1.01  res_tautology_del:                      76
% 2.55/1.01  res_num_eq_res_simplified:              0
% 2.55/1.01  res_num_sel_changes:                    0
% 2.55/1.01  res_moves_from_active_to_pass:          0
% 2.55/1.01  
% 2.55/1.01  ------ Superposition
% 2.55/1.01  
% 2.55/1.01  sup_time_total:                         0.
% 2.55/1.01  sup_time_generating:                    0.
% 2.55/1.01  sup_time_sim_full:                      0.
% 2.55/1.01  sup_time_sim_immed:                     0.
% 2.55/1.01  
% 2.55/1.01  sup_num_of_clauses:                     76
% 2.55/1.01  sup_num_in_active:                      49
% 2.55/1.01  sup_num_in_passive:                     27
% 2.55/1.01  sup_num_of_loops:                       56
% 2.55/1.01  sup_fw_superposition:                   25
% 2.55/1.01  sup_bw_superposition:                   29
% 2.55/1.01  sup_immediate_simplified:               4
% 2.55/1.01  sup_given_eliminated:                   0
% 2.55/1.01  comparisons_done:                       0
% 2.55/1.01  comparisons_avoided:                    0
% 2.55/1.01  
% 2.55/1.01  ------ Simplifications
% 2.55/1.01  
% 2.55/1.01  
% 2.55/1.01  sim_fw_subset_subsumed:                 0
% 2.55/1.01  sim_bw_subset_subsumed:                 2
% 2.55/1.01  sim_fw_subsumed:                        1
% 2.55/1.01  sim_bw_subsumed:                        0
% 2.55/1.01  sim_fw_subsumption_res:                 2
% 2.55/1.01  sim_bw_subsumption_res:                 0
% 2.55/1.01  sim_tautology_del:                      0
% 2.55/1.01  sim_eq_tautology_del:                   1
% 2.55/1.01  sim_eq_res_simp:                        2
% 2.55/1.01  sim_fw_demodulated:                     7
% 2.55/1.01  sim_bw_demodulated:                     7
% 2.55/1.01  sim_light_normalised:                   5
% 2.55/1.01  sim_joinable_taut:                      0
% 2.55/1.01  sim_joinable_simp:                      0
% 2.55/1.01  sim_ac_normalised:                      0
% 2.55/1.01  sim_smt_subsumption:                    0
% 2.55/1.01  
%------------------------------------------------------------------------------
