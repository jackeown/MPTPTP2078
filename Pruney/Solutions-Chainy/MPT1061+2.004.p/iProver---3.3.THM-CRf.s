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
% DateTime   : Thu Dec  3 12:09:30 EST 2020

% Result     : Theorem 8.08s
% Output     : CNFRefutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 677 expanded)
%              Number of clauses        :  101 ( 217 expanded)
%              Number of leaves         :   17 ( 163 expanded)
%              Depth                    :   17
%              Number of atoms          :  534 (4110 expanded)
%              Number of equality atoms :  172 ( 283 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f40,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    & v1_funct_2(sK4,sK0,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f39,f38])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
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

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f63,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_967,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_976,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2256,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_976])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1291,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1443,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_1291])).

cnf(c_2720,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2256,c_27,c_25,c_1443])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_974,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(k2_partfun1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X0))) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3275,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK0,sK3) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2720,c_974])).

cnf(c_30,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_31,plain,
    ( v1_funct_2(sK4,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_304,plain,
    ( sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_28])).

cnf(c_5825,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3275,c_30,c_31,c_32,c_304])).

cnf(c_7,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_980,plain,
    ( r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_308,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_28])).

cnf(c_309,plain,
    ( ~ v1_funct_2(X0,X1,sK3)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_9,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_332,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
    | ~ v1_funct_1(X0) ),
    inference(resolution,[status(thm)],[c_309,c_9])).

cnf(c_964,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | v1_funct_2(X0,X1,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_2484,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | v1_funct_2(X0,X1,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_980,c_964])).

cnf(c_16713,plain,
    ( v1_funct_2(k7_relat_1(sK4,X0),X0,X1) = iProver_top
    | v1_funct_2(k7_relat_1(sK4,X0),X0,sK3) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,X0)),X1) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,X0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5825,c_2484])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_986,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1764,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_986])).

cnf(c_1374,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK3))
    | v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_1,c_25])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1379,plain,
    ( v1_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1374,c_2])).

cnf(c_1380,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1379])).

cnf(c_1767,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1764,c_1380])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_984,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1772,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1767,c_984])).

cnf(c_16865,plain,
    ( v1_funct_2(k7_relat_1(sK4,X0),X0,X1) = iProver_top
    | v1_funct_2(k7_relat_1(sK4,X0),X0,sK3) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k9_relat_1(sK4,X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,X0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16713,c_1772])).

cnf(c_4,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2077,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2078,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2077])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1977,plain,
    ( ~ r1_tarski(X0,sK4)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(resolution,[status(thm)],[c_8,c_25])).

cnf(c_1987,plain,
    ( ~ r1_tarski(X0,sK4)
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
    inference(resolution,[status(thm)],[c_1977,c_1])).

cnf(c_1805,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2003,plain,
    ( v1_relat_1(X0)
    | ~ r1_tarski(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1987,c_1805])).

cnf(c_2004,plain,
    ( ~ r1_tarski(X0,sK4)
    | v1_relat_1(X0) ),
    inference(renaming,[status(thm)],[c_2003])).

cnf(c_5,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2146,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0))
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_2004,c_5])).

cnf(c_2147,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2146])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_977,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2128,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_977])).

cnf(c_1226,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK4,X2))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1435,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1226])).

cnf(c_1436,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1435])).

cnf(c_2714,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2128,c_30,c_32,c_1436])).

cnf(c_2725,plain,
    ( v1_funct_1(k7_relat_1(sK4,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2720,c_2714])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_partfun1(X1,X2,X0,X3),X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_972,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(k2_partfun1(X2,X0,X1,X3),X3,X0) = iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2739,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(k7_relat_1(sK4,X0),X0,sK3) = iProver_top
    | v1_funct_2(sK4,sK0,sK3) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2720,c_972])).

cnf(c_5816,plain,
    ( v1_funct_2(k7_relat_1(sK4,X0),X0,sK3) = iProver_top
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2739,c_30,c_31,c_32,c_304])).

cnf(c_30295,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),X1) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | v1_funct_2(k7_relat_1(sK4,X0),X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16865,c_1380,c_2078,c_2147,c_2725,c_5816])).

cnf(c_30296,plain,
    ( v1_funct_2(k7_relat_1(sK4,X0),X0,X1) = iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k9_relat_1(sK4,X0),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_30295])).

cnf(c_22,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_970,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2486,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) != iProver_top
    | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1) != iProver_top
    | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_980,c_970])).

cnf(c_1500,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_1501,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1500])).

cnf(c_2854,plain,
    ( r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) != iProver_top
    | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1) != iProver_top
    | v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2486,c_30,c_32,c_1501])).

cnf(c_2855,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) != iProver_top
    | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1) != iProver_top
    | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2854])).

cnf(c_2858,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) != iProver_top
    | r1_tarski(k9_relat_1(sK4,sK1),sK2) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2855,c_1772,c_2720])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_981,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1900,plain,
    ( k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_967,c_981])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_969,plain,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1965,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1900,c_969])).

cnf(c_2863,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2858,c_1965])).

cnf(c_30306,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
    | r1_tarski(sK1,sK0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_30296,c_2863])).

cnf(c_2076,plain,
    ( r1_tarski(k7_relat_1(sK4,X0),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_29096,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2076])).

cnf(c_29097,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29096])).

cnf(c_1221,plain,
    ( ~ r1_tarski(X0,sK4)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3037,plain,
    ( ~ r1_tarski(k7_relat_1(sK4,X0),sK4)
    | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_17996,plain,
    ( ~ r1_tarski(k7_relat_1(sK4,sK1),sK4)
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(instantiation,[status(thm)],[c_3037])).

cnf(c_17997,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),sK4) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17996])).

cnf(c_1182,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4269,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_relat_1(k7_relat_1(sK4,X0))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
    inference(instantiation,[status(thm)],[c_1182])).

cnf(c_11450,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
    inference(instantiation,[status(thm)],[c_4269])).

cnf(c_11451,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11450])).

cnf(c_6714,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2077])).

cnf(c_6717,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6714])).

cnf(c_1806,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1805])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_33,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30306,c_29097,c_17997,c_11451,c_6717,c_1965,c_1806,c_1380,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:47:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.08/1.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/1.47  
% 8.08/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.08/1.47  
% 8.08/1.47  ------  iProver source info
% 8.08/1.47  
% 8.08/1.47  git: date: 2020-06-30 10:37:57 +0100
% 8.08/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.08/1.47  git: non_committed_changes: false
% 8.08/1.47  git: last_make_outside_of_git: false
% 8.08/1.47  
% 8.08/1.47  ------ 
% 8.08/1.47  ------ Parsing...
% 8.08/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.08/1.47  
% 8.08/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 8.08/1.47  
% 8.08/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.08/1.47  
% 8.08/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.08/1.47  ------ Proving...
% 8.08/1.47  ------ Problem Properties 
% 8.08/1.47  
% 8.08/1.47  
% 8.08/1.47  clauses                                 24
% 8.08/1.47  conjectures                             6
% 8.08/1.47  EPR                                     4
% 8.08/1.47  Horn                                    22
% 8.08/1.47  unary                                   7
% 8.08/1.47  binary                                  4
% 8.08/1.47  lits                                    69
% 8.08/1.47  lits eq                                 6
% 8.08/1.47  fd_pure                                 0
% 8.08/1.47  fd_pseudo                               0
% 8.08/1.47  fd_cond                                 2
% 8.08/1.47  fd_pseudo_cond                          0
% 8.08/1.47  AC symbols                              0
% 8.08/1.47  
% 8.08/1.47  ------ Input Options Time Limit: Unbounded
% 8.08/1.47  
% 8.08/1.47  
% 8.08/1.47  ------ 
% 8.08/1.47  Current options:
% 8.08/1.47  ------ 
% 8.08/1.47  
% 8.08/1.47  
% 8.08/1.47  
% 8.08/1.47  
% 8.08/1.47  ------ Proving...
% 8.08/1.47  
% 8.08/1.47  
% 8.08/1.47  % SZS status Theorem for theBenchmark.p
% 8.08/1.47  
% 8.08/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 8.08/1.47  
% 8.08/1.47  fof(f15,conjecture,(
% 8.08/1.47    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 8.08/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.47  
% 8.08/1.47  fof(f16,negated_conjecture,(
% 8.08/1.47    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 8.08/1.47    inference(negated_conjecture,[],[f15])).
% 8.08/1.47  
% 8.08/1.47  fof(f36,plain,(
% 8.08/1.47    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 8.08/1.47    inference(ennf_transformation,[],[f16])).
% 8.08/1.47  
% 8.08/1.47  fof(f37,plain,(
% 8.08/1.47    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 8.08/1.47    inference(flattening,[],[f36])).
% 8.08/1.47  
% 8.08/1.47  fof(f39,plain,(
% 8.08/1.47    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(X0,X3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,sK4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,sK4,X1))) & r1_tarski(k7_relset_1(X0,X3,sK4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(sK4,X0,X3) & v1_funct_1(sK4))) )),
% 8.08/1.47    introduced(choice_axiom,[])).
% 8.08/1.47  
% 8.08/1.47  fof(f38,plain,(
% 8.08/1.47    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) & ~v1_xboole_0(sK3))),
% 8.08/1.47    introduced(choice_axiom,[])).
% 8.08/1.47  
% 8.08/1.47  fof(f40,plain,(
% 8.08/1.47    ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 8.08/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f39,f38])).
% 8.08/1.47  
% 8.08/1.47  fof(f66,plain,(
% 8.08/1.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 8.08/1.47    inference(cnf_transformation,[],[f40])).
% 8.08/1.47  
% 8.08/1.47  fof(f13,axiom,(
% 8.08/1.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 8.08/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.47  
% 8.08/1.47  fof(f32,plain,(
% 8.08/1.47    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 8.08/1.47    inference(ennf_transformation,[],[f13])).
% 8.08/1.47  
% 8.08/1.47  fof(f33,plain,(
% 8.08/1.47    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 8.08/1.47    inference(flattening,[],[f32])).
% 8.08/1.47  
% 8.08/1.47  fof(f56,plain,(
% 8.08/1.47    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 8.08/1.47    inference(cnf_transformation,[],[f33])).
% 8.08/1.47  
% 8.08/1.47  fof(f64,plain,(
% 8.08/1.47    v1_funct_1(sK4)),
% 8.08/1.47    inference(cnf_transformation,[],[f40])).
% 8.08/1.47  
% 8.08/1.47  fof(f14,axiom,(
% 8.08/1.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 8.08/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.47  
% 8.08/1.47  fof(f34,plain,(
% 8.08/1.47    ! [X0,X1,X2,X3] : ((((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 8.08/1.47    inference(ennf_transformation,[],[f14])).
% 8.08/1.47  
% 8.08/1.47  fof(f35,plain,(
% 8.08/1.47    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 8.08/1.47    inference(flattening,[],[f34])).
% 8.08/1.47  
% 8.08/1.47  fof(f61,plain,(
% 8.08/1.47    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | k1_xboole_0 = X1 | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 8.08/1.47    inference(cnf_transformation,[],[f35])).
% 8.08/1.47  
% 8.08/1.47  fof(f65,plain,(
% 8.08/1.47    v1_funct_2(sK4,sK0,sK3)),
% 8.08/1.47    inference(cnf_transformation,[],[f40])).
% 8.08/1.47  
% 8.08/1.47  fof(f1,axiom,(
% 8.08/1.47    v1_xboole_0(k1_xboole_0)),
% 8.08/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.47  
% 8.08/1.47  fof(f41,plain,(
% 8.08/1.47    v1_xboole_0(k1_xboole_0)),
% 8.08/1.47    inference(cnf_transformation,[],[f1])).
% 8.08/1.47  
% 8.08/1.47  fof(f63,plain,(
% 8.08/1.47    ~v1_xboole_0(sK3)),
% 8.08/1.47    inference(cnf_transformation,[],[f40])).
% 8.08/1.47  
% 8.08/1.47  fof(f8,axiom,(
% 8.08/1.47    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 8.08/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.47  
% 8.08/1.47  fof(f22,plain,(
% 8.08/1.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 8.08/1.47    inference(ennf_transformation,[],[f8])).
% 8.08/1.47  
% 8.08/1.47  fof(f23,plain,(
% 8.08/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 8.08/1.47    inference(flattening,[],[f22])).
% 8.08/1.47  
% 8.08/1.47  fof(f48,plain,(
% 8.08/1.47    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 8.08/1.47    inference(cnf_transformation,[],[f23])).
% 8.08/1.47  
% 8.08/1.47  fof(f11,axiom,(
% 8.08/1.47    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 8.08/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.47  
% 8.08/1.47  fof(f28,plain,(
% 8.08/1.47    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 8.08/1.47    inference(ennf_transformation,[],[f11])).
% 8.08/1.47  
% 8.08/1.47  fof(f29,plain,(
% 8.08/1.47    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 8.08/1.47    inference(flattening,[],[f28])).
% 8.08/1.47  
% 8.08/1.47  fof(f53,plain,(
% 8.08/1.47    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 8.08/1.47    inference(cnf_transformation,[],[f29])).
% 8.08/1.47  
% 8.08/1.47  fof(f10,axiom,(
% 8.08/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 8.08/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.47  
% 8.08/1.47  fof(f26,plain,(
% 8.08/1.47    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.08/1.47    inference(ennf_transformation,[],[f10])).
% 8.08/1.47  
% 8.08/1.47  fof(f27,plain,(
% 8.08/1.47    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.08/1.47    inference(flattening,[],[f26])).
% 8.08/1.47  
% 8.08/1.47  fof(f51,plain,(
% 8.08/1.47    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.08/1.47    inference(cnf_transformation,[],[f27])).
% 8.08/1.47  
% 8.08/1.47  fof(f2,axiom,(
% 8.08/1.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 8.08/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.47  
% 8.08/1.47  fof(f17,plain,(
% 8.08/1.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 8.08/1.47    inference(ennf_transformation,[],[f2])).
% 8.08/1.47  
% 8.08/1.47  fof(f42,plain,(
% 8.08/1.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 8.08/1.47    inference(cnf_transformation,[],[f17])).
% 8.08/1.47  
% 8.08/1.47  fof(f3,axiom,(
% 8.08/1.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 8.08/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.47  
% 8.08/1.47  fof(f43,plain,(
% 8.08/1.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 8.08/1.47    inference(cnf_transformation,[],[f3])).
% 8.08/1.47  
% 8.08/1.47  fof(f4,axiom,(
% 8.08/1.47    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 8.08/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.47  
% 8.08/1.47  fof(f18,plain,(
% 8.08/1.47    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 8.08/1.47    inference(ennf_transformation,[],[f4])).
% 8.08/1.47  
% 8.08/1.47  fof(f44,plain,(
% 8.08/1.47    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 8.08/1.47    inference(cnf_transformation,[],[f18])).
% 8.08/1.47  
% 8.08/1.47  fof(f5,axiom,(
% 8.08/1.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 8.08/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.47  
% 8.08/1.47  fof(f19,plain,(
% 8.08/1.47    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 8.08/1.47    inference(ennf_transformation,[],[f5])).
% 8.08/1.47  
% 8.08/1.47  fof(f45,plain,(
% 8.08/1.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 8.08/1.47    inference(cnf_transformation,[],[f19])).
% 8.08/1.47  
% 8.08/1.47  fof(f9,axiom,(
% 8.08/1.47    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 8.08/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.47  
% 8.08/1.47  fof(f24,plain,(
% 8.08/1.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 8.08/1.47    inference(ennf_transformation,[],[f9])).
% 8.08/1.47  
% 8.08/1.47  fof(f25,plain,(
% 8.08/1.47    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 8.08/1.47    inference(flattening,[],[f24])).
% 8.08/1.47  
% 8.08/1.47  fof(f49,plain,(
% 8.08/1.47    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 8.08/1.47    inference(cnf_transformation,[],[f25])).
% 8.08/1.47  
% 8.08/1.47  fof(f6,axiom,(
% 8.08/1.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 8.08/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.47  
% 8.08/1.47  fof(f20,plain,(
% 8.08/1.47    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 8.08/1.47    inference(ennf_transformation,[],[f6])).
% 8.08/1.47  
% 8.08/1.47  fof(f46,plain,(
% 8.08/1.47    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 8.08/1.47    inference(cnf_transformation,[],[f20])).
% 8.08/1.47  
% 8.08/1.47  fof(f12,axiom,(
% 8.08/1.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 8.08/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.47  
% 8.08/1.47  fof(f30,plain,(
% 8.08/1.47    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 8.08/1.47    inference(ennf_transformation,[],[f12])).
% 8.08/1.47  
% 8.08/1.47  fof(f31,plain,(
% 8.08/1.47    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 8.08/1.47    inference(flattening,[],[f30])).
% 8.08/1.47  
% 8.08/1.47  fof(f54,plain,(
% 8.08/1.47    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 8.08/1.47    inference(cnf_transformation,[],[f31])).
% 8.08/1.47  
% 8.08/1.47  fof(f59,plain,(
% 8.08/1.47    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | k1_xboole_0 = X1 | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 8.08/1.47    inference(cnf_transformation,[],[f35])).
% 8.08/1.47  
% 8.08/1.47  fof(f69,plain,(
% 8.08/1.47    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 8.08/1.47    inference(cnf_transformation,[],[f40])).
% 8.08/1.47  
% 8.08/1.47  fof(f7,axiom,(
% 8.08/1.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 8.08/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.47  
% 8.08/1.47  fof(f21,plain,(
% 8.08/1.47    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.08/1.47    inference(ennf_transformation,[],[f7])).
% 8.08/1.47  
% 8.08/1.47  fof(f47,plain,(
% 8.08/1.47    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.08/1.47    inference(cnf_transformation,[],[f21])).
% 8.08/1.47  
% 8.08/1.47  fof(f68,plain,(
% 8.08/1.47    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 8.08/1.47    inference(cnf_transformation,[],[f40])).
% 8.08/1.47  
% 8.08/1.47  fof(f67,plain,(
% 8.08/1.47    r1_tarski(sK1,sK0)),
% 8.08/1.47    inference(cnf_transformation,[],[f40])).
% 8.08/1.47  
% 8.08/1.47  cnf(c_25,negated_conjecture,
% 8.08/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
% 8.08/1.47      inference(cnf_transformation,[],[f66]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_967,plain,
% 8.08/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_15,plain,
% 8.08/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.08/1.47      | ~ v1_funct_1(X0)
% 8.08/1.47      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 8.08/1.47      inference(cnf_transformation,[],[f56]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_976,plain,
% 8.08/1.47      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 8.08/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.08/1.47      | v1_funct_1(X2) != iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2256,plain,
% 8.08/1.47      ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
% 8.08/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.08/1.47      inference(superposition,[status(thm)],[c_967,c_976]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_27,negated_conjecture,
% 8.08/1.47      ( v1_funct_1(sK4) ),
% 8.08/1.47      inference(cnf_transformation,[],[f64]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1291,plain,
% 8.08/1.47      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.08/1.47      | ~ v1_funct_1(sK4)
% 8.08/1.47      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 8.08/1.47      inference(instantiation,[status(thm)],[c_15]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1443,plain,
% 8.08/1.47      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 8.08/1.47      | ~ v1_funct_1(sK4)
% 8.08/1.47      | k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
% 8.08/1.47      inference(instantiation,[status(thm)],[c_1291]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2720,plain,
% 8.08/1.47      ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
% 8.08/1.47      inference(global_propositional_subsumption,
% 8.08/1.47                [status(thm)],
% 8.08/1.47                [c_2256,c_27,c_25,c_1443]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_17,plain,
% 8.08/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 8.08/1.47      | ~ r1_tarski(X3,X1)
% 8.08/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.08/1.47      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 8.08/1.47      | ~ v1_funct_1(X0)
% 8.08/1.47      | k1_xboole_0 = X2 ),
% 8.08/1.47      inference(cnf_transformation,[],[f61]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_974,plain,
% 8.08/1.47      ( k1_xboole_0 = X0
% 8.08/1.47      | v1_funct_2(X1,X2,X0) != iProver_top
% 8.08/1.47      | r1_tarski(X3,X2) != iProver_top
% 8.08/1.47      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 8.08/1.47      | m1_subset_1(k2_partfun1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X0))) = iProver_top
% 8.08/1.47      | v1_funct_1(X1) != iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_3275,plain,
% 8.08/1.47      ( sK3 = k1_xboole_0
% 8.08/1.47      | v1_funct_2(sK4,sK0,sK3) != iProver_top
% 8.08/1.47      | r1_tarski(X0,sK0) != iProver_top
% 8.08/1.47      | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) = iProver_top
% 8.08/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 8.08/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.08/1.47      inference(superposition,[status(thm)],[c_2720,c_974]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_30,plain,
% 8.08/1.47      ( v1_funct_1(sK4) = iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_26,negated_conjecture,
% 8.08/1.47      ( v1_funct_2(sK4,sK0,sK3) ),
% 8.08/1.47      inference(cnf_transformation,[],[f65]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_31,plain,
% 8.08/1.47      ( v1_funct_2(sK4,sK0,sK3) = iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_32,plain,
% 8.08/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_0,plain,
% 8.08/1.47      ( v1_xboole_0(k1_xboole_0) ),
% 8.08/1.47      inference(cnf_transformation,[],[f41]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_28,negated_conjecture,
% 8.08/1.47      ( ~ v1_xboole_0(sK3) ),
% 8.08/1.47      inference(cnf_transformation,[],[f63]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_304,plain,
% 8.08/1.47      ( sK3 != k1_xboole_0 ),
% 8.08/1.47      inference(resolution_lifted,[status(thm)],[c_0,c_28]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_5825,plain,
% 8.08/1.47      ( r1_tarski(X0,sK0) != iProver_top
% 8.08/1.47      | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) = iProver_top ),
% 8.08/1.47      inference(global_propositional_subsumption,
% 8.08/1.47                [status(thm)],
% 8.08/1.47                [c_3275,c_30,c_31,c_32,c_304]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_7,plain,
% 8.08/1.47      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 8.08/1.47      | ~ r1_tarski(k2_relat_1(X0),X2)
% 8.08/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.08/1.47      | ~ v1_relat_1(X0) ),
% 8.08/1.47      inference(cnf_transformation,[],[f48]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_980,plain,
% 8.08/1.47      ( r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 8.08/1.47      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 8.08/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 8.08/1.47      | v1_relat_1(X0) != iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_11,plain,
% 8.08/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 8.08/1.47      | v1_partfun1(X0,X1)
% 8.08/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.08/1.47      | ~ v1_funct_1(X0)
% 8.08/1.47      | v1_xboole_0(X2) ),
% 8.08/1.47      inference(cnf_transformation,[],[f53]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_308,plain,
% 8.08/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 8.08/1.47      | v1_partfun1(X0,X1)
% 8.08/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.08/1.47      | ~ v1_funct_1(X0)
% 8.08/1.47      | sK3 != X2 ),
% 8.08/1.47      inference(resolution_lifted,[status(thm)],[c_11,c_28]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_309,plain,
% 8.08/1.47      ( ~ v1_funct_2(X0,X1,sK3)
% 8.08/1.47      | v1_partfun1(X0,X1)
% 8.08/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
% 8.08/1.47      | ~ v1_funct_1(X0) ),
% 8.08/1.47      inference(unflattening,[status(thm)],[c_308]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_9,plain,
% 8.08/1.47      ( v1_funct_2(X0,X1,X2)
% 8.08/1.47      | ~ v1_partfun1(X0,X1)
% 8.08/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.08/1.47      | ~ v1_funct_1(X0) ),
% 8.08/1.47      inference(cnf_transformation,[],[f51]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_332,plain,
% 8.08/1.47      ( v1_funct_2(X0,X1,X2)
% 8.08/1.47      | ~ v1_funct_2(X0,X1,sK3)
% 8.08/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.08/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
% 8.08/1.47      | ~ v1_funct_1(X0) ),
% 8.08/1.47      inference(resolution,[status(thm)],[c_309,c_9]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_964,plain,
% 8.08/1.47      ( v1_funct_2(X0,X1,X2) = iProver_top
% 8.08/1.47      | v1_funct_2(X0,X1,sK3) != iProver_top
% 8.08/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.08/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) != iProver_top
% 8.08/1.47      | v1_funct_1(X0) != iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2484,plain,
% 8.08/1.47      ( v1_funct_2(X0,X1,X2) = iProver_top
% 8.08/1.47      | v1_funct_2(X0,X1,sK3) != iProver_top
% 8.08/1.47      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 8.08/1.47      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 8.08/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) != iProver_top
% 8.08/1.47      | v1_funct_1(X0) != iProver_top
% 8.08/1.47      | v1_relat_1(X0) != iProver_top ),
% 8.08/1.47      inference(superposition,[status(thm)],[c_980,c_964]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_16713,plain,
% 8.08/1.47      ( v1_funct_2(k7_relat_1(sK4,X0),X0,X1) = iProver_top
% 8.08/1.47      | v1_funct_2(k7_relat_1(sK4,X0),X0,sK3) != iProver_top
% 8.08/1.47      | r1_tarski(X0,sK0) != iProver_top
% 8.08/1.47      | r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0) != iProver_top
% 8.08/1.47      | r1_tarski(k2_relat_1(k7_relat_1(sK4,X0)),X1) != iProver_top
% 8.08/1.47      | v1_funct_1(k7_relat_1(sK4,X0)) != iProver_top
% 8.08/1.47      | v1_relat_1(k7_relat_1(sK4,X0)) != iProver_top ),
% 8.08/1.47      inference(superposition,[status(thm)],[c_5825,c_2484]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1,plain,
% 8.08/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.08/1.47      | ~ v1_relat_1(X1)
% 8.08/1.47      | v1_relat_1(X0) ),
% 8.08/1.47      inference(cnf_transformation,[],[f42]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_986,plain,
% 8.08/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.08/1.47      | v1_relat_1(X1) != iProver_top
% 8.08/1.47      | v1_relat_1(X0) = iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1764,plain,
% 8.08/1.47      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top
% 8.08/1.47      | v1_relat_1(sK4) = iProver_top ),
% 8.08/1.47      inference(superposition,[status(thm)],[c_967,c_986]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1374,plain,
% 8.08/1.47      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) | v1_relat_1(sK4) ),
% 8.08/1.47      inference(resolution,[status(thm)],[c_1,c_25]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2,plain,
% 8.08/1.47      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 8.08/1.47      inference(cnf_transformation,[],[f43]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1379,plain,
% 8.08/1.47      ( v1_relat_1(sK4) ),
% 8.08/1.47      inference(forward_subsumption_resolution,
% 8.08/1.47                [status(thm)],
% 8.08/1.47                [c_1374,c_2]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1380,plain,
% 8.08/1.47      ( v1_relat_1(sK4) = iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_1379]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1767,plain,
% 8.08/1.47      ( v1_relat_1(sK4) = iProver_top ),
% 8.08/1.47      inference(global_propositional_subsumption,
% 8.08/1.47                [status(thm)],
% 8.08/1.47                [c_1764,c_1380]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_3,plain,
% 8.08/1.47      ( ~ v1_relat_1(X0)
% 8.08/1.47      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 8.08/1.47      inference(cnf_transformation,[],[f44]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_984,plain,
% 8.08/1.47      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 8.08/1.47      | v1_relat_1(X0) != iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1772,plain,
% 8.08/1.47      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 8.08/1.47      inference(superposition,[status(thm)],[c_1767,c_984]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_16865,plain,
% 8.08/1.47      ( v1_funct_2(k7_relat_1(sK4,X0),X0,X1) = iProver_top
% 8.08/1.47      | v1_funct_2(k7_relat_1(sK4,X0),X0,sK3) != iProver_top
% 8.08/1.47      | r1_tarski(X0,sK0) != iProver_top
% 8.08/1.47      | r1_tarski(k9_relat_1(sK4,X0),X1) != iProver_top
% 8.08/1.47      | r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0) != iProver_top
% 8.08/1.47      | v1_funct_1(k7_relat_1(sK4,X0)) != iProver_top
% 8.08/1.47      | v1_relat_1(k7_relat_1(sK4,X0)) != iProver_top ),
% 8.08/1.47      inference(light_normalisation,[status(thm)],[c_16713,c_1772]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_4,plain,
% 8.08/1.47      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 8.08/1.47      inference(cnf_transformation,[],[f45]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2077,plain,
% 8.08/1.47      ( r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)
% 8.08/1.47      | ~ v1_relat_1(sK4) ),
% 8.08/1.47      inference(instantiation,[status(thm)],[c_4]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2078,plain,
% 8.08/1.47      ( r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0) = iProver_top
% 8.08/1.47      | v1_relat_1(sK4) != iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_2077]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_8,plain,
% 8.08/1.47      ( ~ r1_tarski(X0,X1)
% 8.08/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 8.08/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
% 8.08/1.47      inference(cnf_transformation,[],[f49]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1977,plain,
% 8.08/1.47      ( ~ r1_tarski(X0,sK4)
% 8.08/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
% 8.08/1.47      inference(resolution,[status(thm)],[c_8,c_25]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1987,plain,
% 8.08/1.47      ( ~ r1_tarski(X0,sK4)
% 8.08/1.47      | v1_relat_1(X0)
% 8.08/1.47      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
% 8.08/1.47      inference(resolution,[status(thm)],[c_1977,c_1]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1805,plain,
% 8.08/1.47      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
% 8.08/1.47      inference(instantiation,[status(thm)],[c_2]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2003,plain,
% 8.08/1.47      ( v1_relat_1(X0) | ~ r1_tarski(X0,sK4) ),
% 8.08/1.47      inference(global_propositional_subsumption,
% 8.08/1.47                [status(thm)],
% 8.08/1.47                [c_1987,c_1805]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2004,plain,
% 8.08/1.47      ( ~ r1_tarski(X0,sK4) | v1_relat_1(X0) ),
% 8.08/1.47      inference(renaming,[status(thm)],[c_2003]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_5,plain,
% 8.08/1.47      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 8.08/1.47      inference(cnf_transformation,[],[f46]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2146,plain,
% 8.08/1.47      ( v1_relat_1(k7_relat_1(sK4,X0)) | ~ v1_relat_1(sK4) ),
% 8.08/1.47      inference(resolution,[status(thm)],[c_2004,c_5]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2147,plain,
% 8.08/1.47      ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top
% 8.08/1.47      | v1_relat_1(sK4) != iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_2146]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_14,plain,
% 8.08/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.08/1.47      | ~ v1_funct_1(X0)
% 8.08/1.47      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 8.08/1.47      inference(cnf_transformation,[],[f54]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_977,plain,
% 8.08/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.08/1.47      | v1_funct_1(X0) != iProver_top
% 8.08/1.47      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2128,plain,
% 8.08/1.47      ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top
% 8.08/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.08/1.47      inference(superposition,[status(thm)],[c_967,c_977]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1226,plain,
% 8.08/1.47      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.08/1.47      | v1_funct_1(k2_partfun1(X0,X1,sK4,X2))
% 8.08/1.47      | ~ v1_funct_1(sK4) ),
% 8.08/1.47      inference(instantiation,[status(thm)],[c_14]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1435,plain,
% 8.08/1.47      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 8.08/1.47      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))
% 8.08/1.47      | ~ v1_funct_1(sK4) ),
% 8.08/1.47      inference(instantiation,[status(thm)],[c_1226]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1436,plain,
% 8.08/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 8.08/1.47      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top
% 8.08/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_1435]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2714,plain,
% 8.08/1.47      ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top ),
% 8.08/1.47      inference(global_propositional_subsumption,
% 8.08/1.47                [status(thm)],
% 8.08/1.47                [c_2128,c_30,c_32,c_1436]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2725,plain,
% 8.08/1.47      ( v1_funct_1(k7_relat_1(sK4,X0)) = iProver_top ),
% 8.08/1.47      inference(demodulation,[status(thm)],[c_2720,c_2714]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_19,plain,
% 8.08/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 8.08/1.47      | v1_funct_2(k2_partfun1(X1,X2,X0,X3),X3,X2)
% 8.08/1.47      | ~ r1_tarski(X3,X1)
% 8.08/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.08/1.47      | ~ v1_funct_1(X0)
% 8.08/1.47      | k1_xboole_0 = X2 ),
% 8.08/1.47      inference(cnf_transformation,[],[f59]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_972,plain,
% 8.08/1.47      ( k1_xboole_0 = X0
% 8.08/1.47      | v1_funct_2(X1,X2,X0) != iProver_top
% 8.08/1.47      | v1_funct_2(k2_partfun1(X2,X0,X1,X3),X3,X0) = iProver_top
% 8.08/1.47      | r1_tarski(X3,X2) != iProver_top
% 8.08/1.47      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 8.08/1.47      | v1_funct_1(X1) != iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2739,plain,
% 8.08/1.47      ( sK3 = k1_xboole_0
% 8.08/1.47      | v1_funct_2(k7_relat_1(sK4,X0),X0,sK3) = iProver_top
% 8.08/1.47      | v1_funct_2(sK4,sK0,sK3) != iProver_top
% 8.08/1.47      | r1_tarski(X0,sK0) != iProver_top
% 8.08/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 8.08/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.08/1.47      inference(superposition,[status(thm)],[c_2720,c_972]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_5816,plain,
% 8.08/1.47      ( v1_funct_2(k7_relat_1(sK4,X0),X0,sK3) = iProver_top
% 8.08/1.47      | r1_tarski(X0,sK0) != iProver_top ),
% 8.08/1.47      inference(global_propositional_subsumption,
% 8.08/1.47                [status(thm)],
% 8.08/1.47                [c_2739,c_30,c_31,c_32,c_304]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_30295,plain,
% 8.08/1.47      ( r1_tarski(k9_relat_1(sK4,X0),X1) != iProver_top
% 8.08/1.47      | r1_tarski(X0,sK0) != iProver_top
% 8.08/1.47      | v1_funct_2(k7_relat_1(sK4,X0),X0,X1) = iProver_top ),
% 8.08/1.47      inference(global_propositional_subsumption,
% 8.08/1.47                [status(thm)],
% 8.08/1.47                [c_16865,c_1380,c_2078,c_2147,c_2725,c_5816]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_30296,plain,
% 8.08/1.47      ( v1_funct_2(k7_relat_1(sK4,X0),X0,X1) = iProver_top
% 8.08/1.47      | r1_tarski(X0,sK0) != iProver_top
% 8.08/1.47      | r1_tarski(k9_relat_1(sK4,X0),X1) != iProver_top ),
% 8.08/1.47      inference(renaming,[status(thm)],[c_30295]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_22,negated_conjecture,
% 8.08/1.47      ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
% 8.08/1.47      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 8.08/1.47      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
% 8.08/1.47      inference(cnf_transformation,[],[f69]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_970,plain,
% 8.08/1.47      ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) != iProver_top
% 8.08/1.47      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 8.08/1.47      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2486,plain,
% 8.08/1.47      ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) != iProver_top
% 8.08/1.47      | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1) != iProver_top
% 8.08/1.47      | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) != iProver_top
% 8.08/1.47      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
% 8.08/1.47      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 8.08/1.47      inference(superposition,[status(thm)],[c_980,c_970]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1500,plain,
% 8.08/1.47      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 8.08/1.47      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 8.08/1.47      | ~ v1_funct_1(sK4) ),
% 8.08/1.47      inference(instantiation,[status(thm)],[c_1435]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1501,plain,
% 8.08/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 8.08/1.47      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) = iProver_top
% 8.08/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_1500]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2854,plain,
% 8.08/1.47      ( r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) != iProver_top
% 8.08/1.47      | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1) != iProver_top
% 8.08/1.47      | v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) != iProver_top
% 8.08/1.47      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 8.08/1.47      inference(global_propositional_subsumption,
% 8.08/1.47                [status(thm)],
% 8.08/1.47                [c_2486,c_30,c_32,c_1501]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2855,plain,
% 8.08/1.47      ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) != iProver_top
% 8.08/1.47      | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1) != iProver_top
% 8.08/1.47      | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) != iProver_top
% 8.08/1.47      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 8.08/1.47      inference(renaming,[status(thm)],[c_2854]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2858,plain,
% 8.08/1.47      ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) != iProver_top
% 8.08/1.47      | r1_tarski(k9_relat_1(sK4,sK1),sK2) != iProver_top
% 8.08/1.47      | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
% 8.08/1.47      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 8.08/1.47      inference(demodulation,[status(thm)],[c_2855,c_1772,c_2720]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_6,plain,
% 8.08/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.08/1.47      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 8.08/1.47      inference(cnf_transformation,[],[f47]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_981,plain,
% 8.08/1.47      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 8.08/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1900,plain,
% 8.08/1.47      ( k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
% 8.08/1.47      inference(superposition,[status(thm)],[c_967,c_981]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_23,negated_conjecture,
% 8.08/1.47      ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
% 8.08/1.47      inference(cnf_transformation,[],[f68]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_969,plain,
% 8.08/1.47      ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) = iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1965,plain,
% 8.08/1.47      ( r1_tarski(k9_relat_1(sK4,sK1),sK2) = iProver_top ),
% 8.08/1.47      inference(demodulation,[status(thm)],[c_1900,c_969]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2863,plain,
% 8.08/1.47      ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) != iProver_top
% 8.08/1.47      | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
% 8.08/1.47      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 8.08/1.47      inference(forward_subsumption_resolution,
% 8.08/1.47                [status(thm)],
% 8.08/1.47                [c_2858,c_1965]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_30306,plain,
% 8.08/1.47      ( r1_tarski(k9_relat_1(sK4,sK1),sK2) != iProver_top
% 8.08/1.47      | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
% 8.08/1.47      | r1_tarski(sK1,sK0) != iProver_top
% 8.08/1.47      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 8.08/1.47      inference(superposition,[status(thm)],[c_30296,c_2863]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_2076,plain,
% 8.08/1.47      ( r1_tarski(k7_relat_1(sK4,X0),sK4) | ~ v1_relat_1(sK4) ),
% 8.08/1.47      inference(instantiation,[status(thm)],[c_5]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_29096,plain,
% 8.08/1.47      ( r1_tarski(k7_relat_1(sK4,sK1),sK4) | ~ v1_relat_1(sK4) ),
% 8.08/1.47      inference(instantiation,[status(thm)],[c_2076]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_29097,plain,
% 8.08/1.47      ( r1_tarski(k7_relat_1(sK4,sK1),sK4) = iProver_top
% 8.08/1.47      | v1_relat_1(sK4) != iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_29096]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1221,plain,
% 8.08/1.47      ( ~ r1_tarski(X0,sK4)
% 8.08/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 8.08/1.47      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
% 8.08/1.47      inference(instantiation,[status(thm)],[c_8]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_3037,plain,
% 8.08/1.47      ( ~ r1_tarski(k7_relat_1(sK4,X0),sK4)
% 8.08/1.47      | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 8.08/1.47      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
% 8.08/1.47      inference(instantiation,[status(thm)],[c_1221]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_17996,plain,
% 8.08/1.47      ( ~ r1_tarski(k7_relat_1(sK4,sK1),sK4)
% 8.08/1.47      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 8.08/1.47      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
% 8.08/1.47      inference(instantiation,[status(thm)],[c_3037]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_17997,plain,
% 8.08/1.47      ( r1_tarski(k7_relat_1(sK4,sK1),sK4) != iProver_top
% 8.08/1.47      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top
% 8.08/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_17996]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1182,plain,
% 8.08/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.08/1.47      | v1_relat_1(X0)
% 8.08/1.47      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 8.08/1.47      inference(instantiation,[status(thm)],[c_1]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_4269,plain,
% 8.08/1.47      ( ~ m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 8.08/1.47      | v1_relat_1(k7_relat_1(sK4,X0))
% 8.08/1.47      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
% 8.08/1.47      inference(instantiation,[status(thm)],[c_1182]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_11450,plain,
% 8.08/1.47      ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 8.08/1.47      | v1_relat_1(k7_relat_1(sK4,sK1))
% 8.08/1.47      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
% 8.08/1.47      inference(instantiation,[status(thm)],[c_4269]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_11451,plain,
% 8.08/1.47      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 8.08/1.47      | v1_relat_1(k7_relat_1(sK4,sK1)) = iProver_top
% 8.08/1.47      | v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_11450]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_6714,plain,
% 8.08/1.47      ( r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
% 8.08/1.47      | ~ v1_relat_1(sK4) ),
% 8.08/1.47      inference(instantiation,[status(thm)],[c_2077]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_6717,plain,
% 8.08/1.47      ( r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) = iProver_top
% 8.08/1.47      | v1_relat_1(sK4) != iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_6714]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_1806,plain,
% 8.08/1.47      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) = iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_1805]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_24,negated_conjecture,
% 8.08/1.47      ( r1_tarski(sK1,sK0) ),
% 8.08/1.47      inference(cnf_transformation,[],[f67]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(c_33,plain,
% 8.08/1.47      ( r1_tarski(sK1,sK0) = iProver_top ),
% 8.08/1.47      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 8.08/1.47  
% 8.08/1.47  cnf(contradiction,plain,
% 8.08/1.47      ( $false ),
% 8.08/1.47      inference(minisat,
% 8.08/1.47                [status(thm)],
% 8.08/1.47                [c_30306,c_29097,c_17997,c_11451,c_6717,c_1965,c_1806,
% 8.08/1.47                 c_1380,c_33,c_32]) ).
% 8.08/1.47  
% 8.08/1.47  
% 8.08/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 8.08/1.47  
% 8.08/1.47  ------                               Statistics
% 8.08/1.47  
% 8.08/1.47  ------ Selected
% 8.08/1.47  
% 8.08/1.47  total_time:                             0.901
% 8.08/1.47  
%------------------------------------------------------------------------------
