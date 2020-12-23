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
% DateTime   : Thu Dec  3 12:09:33 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 758 expanded)
%              Number of clauses        :  105 ( 282 expanded)
%              Number of leaves         :   14 ( 168 expanded)
%              Depth                    :   17
%              Number of atoms          :  496 (4468 expanded)
%              Number of equality atoms :  191 ( 434 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

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
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f33,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    & v1_funct_2(sK4,sK0,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f29,f32,f31])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f53,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_834,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1327,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_842,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
    | ~ v1_relat_1(X1_49)
    | v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1319,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(X1_49)) != iProver_top
    | v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_1756,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1327,c_1319])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_841,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1846,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_1847,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1846])).

cnf(c_1967,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1756,c_1847])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_840,plain,
    ( ~ v1_relat_1(X0_49)
    | k2_relat_1(k7_relat_1(X0_49,X1_49)) = k9_relat_1(X0_49,X1_49) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1321,plain,
    ( k2_relat_1(k7_relat_1(X0_49,X1_49)) = k9_relat_1(X0_49,X1_49)
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_840])).

cnf(c_1972,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0_49)) = k9_relat_1(sK4,X0_49) ),
    inference(superposition,[status(thm)],[c_1967,c_1321])).

cnf(c_16,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_333,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_334,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_829,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_49),sK2)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_334])).

cnf(c_1331,plain,
    ( k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_49),sK2))) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_829])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_838,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | k7_relset_1(X1_49,X2_49,X0_49,X3_49) = k9_relat_1(X0_49,X3_49) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1323,plain,
    ( k7_relset_1(X0_49,X1_49,X2_49,X3_49) = k9_relat_1(X2_49,X3_49)
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_838])).

cnf(c_1928,plain,
    ( k7_relset_1(sK0,sK3,sK4,X0_49) = k9_relat_1(sK4,X0_49) ),
    inference(superposition,[status(thm)],[c_1327,c_1323])).

cnf(c_1990,plain,
    ( k9_relat_1(sK4,sK1) != k2_relat_1(X0_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_49),sK2))) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1331,c_1928])).

cnf(c_2309,plain,
    ( k9_relat_1(sK4,X0_49) != k9_relat_1(sK4,sK1)
    | m1_subset_1(k7_relat_1(sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X0_49)),sK2))) = iProver_top
    | v1_funct_1(k7_relat_1(sK4,X0_49)) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,X0_49)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1972,c_1990])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_835,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | ~ v1_funct_1(X0_49)
    | k2_partfun1(X1_49,X2_49,X0_49,X3_49) = k7_relat_1(X0_49,X3_49) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1326,plain,
    ( k2_partfun1(X0_49,X1_49,X2_49,X3_49) = k7_relat_1(X2_49,X3_49)
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X2_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_835])).

cnf(c_2246,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0_49) = k7_relat_1(sK4,X0_49)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1327,c_1326])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1690,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_49,X1_49,sK4,X2_49) = k7_relat_1(sK4,X2_49) ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_1809,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK0,sK3,sK4,X0_49) = k7_relat_1(sK4,X0_49) ),
    inference(instantiation,[status(thm)],[c_1690])).

cnf(c_2395,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0_49) = k7_relat_1(sK4,X0_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2246,c_24,c_22,c_1809])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_836,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1325,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_836])).

cnf(c_2222,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0_49)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1327,c_1325])).

cnf(c_27,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_29,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1667,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_funct_1(k2_partfun1(X0_49,X1_49,sK4,X2_49))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_836])).

cnf(c_1804,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0_49))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1667])).

cnf(c_1805,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0_49)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1804])).

cnf(c_2387,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0_49)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2222,c_27,c_29,c_1805])).

cnf(c_2403,plain,
    ( v1_funct_1(k7_relat_1(sK4,X0_49)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2395,c_2387])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_837,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | m1_subset_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1324,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
    | m1_subset_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) = iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_837])).

cnf(c_2445,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2395,c_1324])).

cnf(c_2728,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2445,c_27,c_29])).

cnf(c_2736,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0_49)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2728,c_1319])).

cnf(c_3787,plain,
    ( k9_relat_1(sK4,X0_49) != k9_relat_1(sK4,sK1)
    | m1_subset_1(k7_relat_1(sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X0_49)),sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2309,c_1847,c_2403,c_2736])).

cnf(c_3795,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,sK1)),sK2))) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3787])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_605,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_606,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | k1_relset_1(sK0,sK3,sK4) = sK0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_608,plain,
    ( k1_relset_1(sK0,sK3,sK4) = sK0
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_606,c_22])).

cnf(c_819,plain,
    ( k1_relset_1(sK0,sK3,sK4) = sK0
    | k1_xboole_0 = sK3 ),
    inference(subtyping,[status(esa)],[c_608])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_839,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | k1_relset_1(X1_49,X2_49,X0_49) = k1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1322,plain,
    ( k1_relset_1(X0_49,X1_49,X2_49) = k1_relat_1(X2_49)
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_1822,plain,
    ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1327,c_1322])).

cnf(c_1931,plain,
    ( k1_relat_1(sK4) = sK0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_819,c_1822])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_280,plain,
    ( sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_25])).

cnf(c_832,plain,
    ( sK3 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_280])).

cnf(c_2567,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1931,c_832])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_300,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK0
    | k1_relat_1(k7_relat_1(X0,X1)) = X1
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_301,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK0
    | k1_relat_1(k7_relat_1(X0,sK1)) = sK1 ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_830,plain,
    ( ~ v1_relat_1(X0_49)
    | k1_relat_1(X0_49) != sK0
    | k1_relat_1(k7_relat_1(X0_49,sK1)) = sK1 ),
    inference(subtyping,[status(esa)],[c_301])).

cnf(c_1330,plain,
    ( k1_relat_1(X0_49) != sK0
    | k1_relat_1(k7_relat_1(X0_49,sK1)) = sK1
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_2571,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2567,c_1330])).

cnf(c_1757,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK3))
    | v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1756])).

cnf(c_2020,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k7_relat_1(sK4,sK1)) = sK1
    | k1_relat_1(sK4) != sK0 ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_2636,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2571,c_832,c_1757,c_1846,c_1931,c_2020])).

cnf(c_3796,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3795,c_2636])).

cnf(c_19,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_17,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_315,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_316,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),sK2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_688,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0)
    | k1_relat_1(X0) != sK1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_316])).

cnf(c_689,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_815,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
    inference(subtyping,[status(esa)],[c_689])).

cnf(c_1344,plain,
    ( k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_921,plain,
    ( k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_1849,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1804])).

cnf(c_1850,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1849])).

cnf(c_1654,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | v1_relat_1(X0_49)
    | ~ v1_relat_1(k2_zfmisc_1(X1_49,X2_49)) ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_1902,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,X0_49))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
    inference(instantiation,[status(thm)],[c_1654])).

cnf(c_2071,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
    inference(instantiation,[status(thm)],[c_1902])).

cnf(c_2072,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2071])).

cnf(c_1695,plain,
    ( m1_subset_1(k2_partfun1(X0_49,X1_49,sK4,X2_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_1823,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1695])).

cnf(c_2383,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1823])).

cnf(c_2384,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2383])).

cnf(c_2548,plain,
    ( k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1344,c_27,c_29,c_921,c_1847,c_1850,c_2072,c_2384])).

cnf(c_2552,plain,
    ( k9_relat_1(sK4,sK1) != k9_relat_1(sK4,sK1)
    | k1_relat_1(k7_relat_1(sK4,sK1)) != sK1
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2548,c_1928,c_1972,c_2395])).

cnf(c_2553,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) != sK1
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2552])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3796,c_2553,c_2020,c_1931,c_1846,c_1757,c_832])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:32:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.50/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/0.98  
% 2.50/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.50/0.98  
% 2.50/0.98  ------  iProver source info
% 2.50/0.98  
% 2.50/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.50/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.50/0.98  git: non_committed_changes: false
% 2.50/0.98  git: last_make_outside_of_git: false
% 2.50/0.98  
% 2.50/0.98  ------ 
% 2.50/0.98  
% 2.50/0.98  ------ Input Options
% 2.50/0.98  
% 2.50/0.98  --out_options                           all
% 2.50/0.98  --tptp_safe_out                         true
% 2.50/0.98  --problem_path                          ""
% 2.50/0.98  --include_path                          ""
% 2.50/0.98  --clausifier                            res/vclausify_rel
% 2.50/0.98  --clausifier_options                    --mode clausify
% 2.50/0.98  --stdin                                 false
% 2.50/0.98  --stats_out                             all
% 2.50/0.98  
% 2.50/0.98  ------ General Options
% 2.50/0.98  
% 2.50/0.98  --fof                                   false
% 2.50/0.98  --time_out_real                         305.
% 2.50/0.98  --time_out_virtual                      -1.
% 2.50/0.98  --symbol_type_check                     false
% 2.50/0.98  --clausify_out                          false
% 2.50/0.98  --sig_cnt_out                           false
% 2.50/0.98  --trig_cnt_out                          false
% 2.50/0.98  --trig_cnt_out_tolerance                1.
% 2.50/0.98  --trig_cnt_out_sk_spl                   false
% 2.50/0.98  --abstr_cl_out                          false
% 2.50/0.98  
% 2.50/0.98  ------ Global Options
% 2.50/0.98  
% 2.50/0.98  --schedule                              default
% 2.50/0.98  --add_important_lit                     false
% 2.50/0.98  --prop_solver_per_cl                    1000
% 2.50/0.98  --min_unsat_core                        false
% 2.50/0.98  --soft_assumptions                      false
% 2.50/0.98  --soft_lemma_size                       3
% 2.50/0.98  --prop_impl_unit_size                   0
% 2.50/0.98  --prop_impl_unit                        []
% 2.50/0.98  --share_sel_clauses                     true
% 2.50/0.98  --reset_solvers                         false
% 2.50/0.98  --bc_imp_inh                            [conj_cone]
% 2.50/0.98  --conj_cone_tolerance                   3.
% 2.50/0.98  --extra_neg_conj                        none
% 2.50/0.98  --large_theory_mode                     true
% 2.50/0.98  --prolific_symb_bound                   200
% 2.50/0.98  --lt_threshold                          2000
% 2.50/0.98  --clause_weak_htbl                      true
% 2.50/0.98  --gc_record_bc_elim                     false
% 2.50/0.98  
% 2.50/0.98  ------ Preprocessing Options
% 2.50/0.98  
% 2.50/0.98  --preprocessing_flag                    true
% 2.50/0.98  --time_out_prep_mult                    0.1
% 2.50/0.98  --splitting_mode                        input
% 2.50/0.98  --splitting_grd                         true
% 2.50/0.98  --splitting_cvd                         false
% 2.50/0.98  --splitting_cvd_svl                     false
% 2.50/0.98  --splitting_nvd                         32
% 2.50/0.98  --sub_typing                            true
% 2.50/0.98  --prep_gs_sim                           true
% 2.50/0.98  --prep_unflatten                        true
% 2.50/0.98  --prep_res_sim                          true
% 2.50/0.98  --prep_upred                            true
% 2.50/0.98  --prep_sem_filter                       exhaustive
% 2.50/0.98  --prep_sem_filter_out                   false
% 2.50/0.98  --pred_elim                             true
% 2.50/0.98  --res_sim_input                         true
% 2.50/0.98  --eq_ax_congr_red                       true
% 2.50/0.98  --pure_diseq_elim                       true
% 2.50/0.98  --brand_transform                       false
% 2.50/0.98  --non_eq_to_eq                          false
% 2.50/0.98  --prep_def_merge                        true
% 2.50/0.98  --prep_def_merge_prop_impl              false
% 2.50/0.98  --prep_def_merge_mbd                    true
% 2.50/0.98  --prep_def_merge_tr_red                 false
% 2.50/0.98  --prep_def_merge_tr_cl                  false
% 2.50/0.98  --smt_preprocessing                     true
% 2.50/0.98  --smt_ac_axioms                         fast
% 2.50/0.98  --preprocessed_out                      false
% 2.50/0.98  --preprocessed_stats                    false
% 2.50/0.98  
% 2.50/0.98  ------ Abstraction refinement Options
% 2.50/0.98  
% 2.50/0.98  --abstr_ref                             []
% 2.50/0.98  --abstr_ref_prep                        false
% 2.50/0.98  --abstr_ref_until_sat                   false
% 2.50/0.98  --abstr_ref_sig_restrict                funpre
% 2.50/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/0.98  --abstr_ref_under                       []
% 2.50/0.98  
% 2.50/0.98  ------ SAT Options
% 2.50/0.98  
% 2.50/0.98  --sat_mode                              false
% 2.50/0.98  --sat_fm_restart_options                ""
% 2.50/0.98  --sat_gr_def                            false
% 2.50/0.98  --sat_epr_types                         true
% 2.50/0.98  --sat_non_cyclic_types                  false
% 2.50/0.98  --sat_finite_models                     false
% 2.50/0.98  --sat_fm_lemmas                         false
% 2.50/0.98  --sat_fm_prep                           false
% 2.50/0.98  --sat_fm_uc_incr                        true
% 2.50/0.98  --sat_out_model                         small
% 2.50/0.98  --sat_out_clauses                       false
% 2.50/0.98  
% 2.50/0.98  ------ QBF Options
% 2.50/0.98  
% 2.50/0.98  --qbf_mode                              false
% 2.50/0.98  --qbf_elim_univ                         false
% 2.50/0.98  --qbf_dom_inst                          none
% 2.50/0.98  --qbf_dom_pre_inst                      false
% 2.50/0.98  --qbf_sk_in                             false
% 2.50/0.98  --qbf_pred_elim                         true
% 2.50/0.98  --qbf_split                             512
% 2.50/0.98  
% 2.50/0.98  ------ BMC1 Options
% 2.50/0.98  
% 2.50/0.98  --bmc1_incremental                      false
% 2.50/0.98  --bmc1_axioms                           reachable_all
% 2.50/0.98  --bmc1_min_bound                        0
% 2.50/0.98  --bmc1_max_bound                        -1
% 2.50/0.98  --bmc1_max_bound_default                -1
% 2.50/0.98  --bmc1_symbol_reachability              true
% 2.50/0.98  --bmc1_property_lemmas                  false
% 2.50/0.98  --bmc1_k_induction                      false
% 2.50/0.98  --bmc1_non_equiv_states                 false
% 2.50/0.98  --bmc1_deadlock                         false
% 2.50/0.98  --bmc1_ucm                              false
% 2.50/0.98  --bmc1_add_unsat_core                   none
% 2.50/0.98  --bmc1_unsat_core_children              false
% 2.50/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/0.98  --bmc1_out_stat                         full
% 2.50/0.98  --bmc1_ground_init                      false
% 2.50/0.98  --bmc1_pre_inst_next_state              false
% 2.50/0.98  --bmc1_pre_inst_state                   false
% 2.50/0.98  --bmc1_pre_inst_reach_state             false
% 2.50/0.98  --bmc1_out_unsat_core                   false
% 2.50/0.98  --bmc1_aig_witness_out                  false
% 2.50/0.98  --bmc1_verbose                          false
% 2.50/0.98  --bmc1_dump_clauses_tptp                false
% 2.50/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.50/0.98  --bmc1_dump_file                        -
% 2.50/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.50/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.50/0.98  --bmc1_ucm_extend_mode                  1
% 2.50/0.98  --bmc1_ucm_init_mode                    2
% 2.50/0.98  --bmc1_ucm_cone_mode                    none
% 2.50/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.50/0.98  --bmc1_ucm_relax_model                  4
% 2.50/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.50/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/0.98  --bmc1_ucm_layered_model                none
% 2.50/0.98  --bmc1_ucm_max_lemma_size               10
% 2.50/0.98  
% 2.50/0.98  ------ AIG Options
% 2.50/0.98  
% 2.50/0.98  --aig_mode                              false
% 2.50/0.98  
% 2.50/0.98  ------ Instantiation Options
% 2.50/0.98  
% 2.50/0.98  --instantiation_flag                    true
% 2.50/0.98  --inst_sos_flag                         false
% 2.50/0.98  --inst_sos_phase                        true
% 2.50/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/0.98  --inst_lit_sel_side                     num_symb
% 2.50/0.98  --inst_solver_per_active                1400
% 2.50/0.98  --inst_solver_calls_frac                1.
% 2.50/0.98  --inst_passive_queue_type               priority_queues
% 2.50/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/0.98  --inst_passive_queues_freq              [25;2]
% 2.50/0.98  --inst_dismatching                      true
% 2.50/0.98  --inst_eager_unprocessed_to_passive     true
% 2.50/0.98  --inst_prop_sim_given                   true
% 2.50/0.98  --inst_prop_sim_new                     false
% 2.50/0.98  --inst_subs_new                         false
% 2.50/0.98  --inst_eq_res_simp                      false
% 2.50/0.98  --inst_subs_given                       false
% 2.50/0.98  --inst_orphan_elimination               true
% 2.50/0.98  --inst_learning_loop_flag               true
% 2.50/0.98  --inst_learning_start                   3000
% 2.50/0.98  --inst_learning_factor                  2
% 2.50/0.98  --inst_start_prop_sim_after_learn       3
% 2.50/0.98  --inst_sel_renew                        solver
% 2.50/0.98  --inst_lit_activity_flag                true
% 2.50/0.98  --inst_restr_to_given                   false
% 2.50/0.98  --inst_activity_threshold               500
% 2.50/0.98  --inst_out_proof                        true
% 2.50/0.98  
% 2.50/0.98  ------ Resolution Options
% 2.50/0.98  
% 2.50/0.98  --resolution_flag                       true
% 2.50/0.98  --res_lit_sel                           adaptive
% 2.50/0.98  --res_lit_sel_side                      none
% 2.50/0.98  --res_ordering                          kbo
% 2.50/0.98  --res_to_prop_solver                    active
% 2.50/0.98  --res_prop_simpl_new                    false
% 2.50/0.98  --res_prop_simpl_given                  true
% 2.50/0.98  --res_passive_queue_type                priority_queues
% 2.50/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/0.98  --res_passive_queues_freq               [15;5]
% 2.50/0.98  --res_forward_subs                      full
% 2.50/0.98  --res_backward_subs                     full
% 2.50/0.98  --res_forward_subs_resolution           true
% 2.50/0.98  --res_backward_subs_resolution          true
% 2.50/0.98  --res_orphan_elimination                true
% 2.50/0.98  --res_time_limit                        2.
% 2.50/0.98  --res_out_proof                         true
% 2.50/0.98  
% 2.50/0.98  ------ Superposition Options
% 2.50/0.98  
% 2.50/0.98  --superposition_flag                    true
% 2.50/0.98  --sup_passive_queue_type                priority_queues
% 2.50/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.50/0.98  --demod_completeness_check              fast
% 2.50/0.98  --demod_use_ground                      true
% 2.50/0.98  --sup_to_prop_solver                    passive
% 2.50/0.98  --sup_prop_simpl_new                    true
% 2.50/0.98  --sup_prop_simpl_given                  true
% 2.50/0.98  --sup_fun_splitting                     false
% 2.50/0.98  --sup_smt_interval                      50000
% 2.50/0.98  
% 2.50/0.98  ------ Superposition Simplification Setup
% 2.50/0.98  
% 2.50/0.98  --sup_indices_passive                   []
% 2.50/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.98  --sup_full_bw                           [BwDemod]
% 2.50/0.98  --sup_immed_triv                        [TrivRules]
% 2.50/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.98  --sup_immed_bw_main                     []
% 2.50/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.98  
% 2.50/0.98  ------ Combination Options
% 2.50/0.98  
% 2.50/0.98  --comb_res_mult                         3
% 2.50/0.98  --comb_sup_mult                         2
% 2.50/0.98  --comb_inst_mult                        10
% 2.50/0.98  
% 2.50/0.98  ------ Debug Options
% 2.50/0.98  
% 2.50/0.98  --dbg_backtrace                         false
% 2.50/0.98  --dbg_dump_prop_clauses                 false
% 2.50/0.98  --dbg_dump_prop_clauses_file            -
% 2.50/0.98  --dbg_out_stat                          false
% 2.50/0.98  ------ Parsing...
% 2.50/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.50/0.98  
% 2.50/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.50/0.98  
% 2.50/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.50/0.98  
% 2.50/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.50/0.98  ------ Proving...
% 2.50/0.98  ------ Problem Properties 
% 2.50/0.98  
% 2.50/0.98  
% 2.50/0.98  clauses                                 29
% 2.50/0.98  conjectures                             2
% 2.50/0.98  EPR                                     2
% 2.50/0.98  Horn                                    24
% 2.50/0.98  unary                                   4
% 2.50/0.98  binary                                  4
% 2.50/0.98  lits                                    108
% 2.50/0.98  lits eq                                 50
% 2.50/0.98  fd_pure                                 0
% 2.50/0.98  fd_pseudo                               0
% 2.50/0.98  fd_cond                                 2
% 2.50/0.98  fd_pseudo_cond                          0
% 2.50/0.98  AC symbols                              0
% 2.50/0.98  
% 2.50/0.98  ------ Schedule dynamic 5 is on 
% 2.50/0.98  
% 2.50/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.50/0.98  
% 2.50/0.98  
% 2.50/0.98  ------ 
% 2.50/0.98  Current options:
% 2.50/0.98  ------ 
% 2.50/0.98  
% 2.50/0.98  ------ Input Options
% 2.50/0.98  
% 2.50/0.98  --out_options                           all
% 2.50/0.98  --tptp_safe_out                         true
% 2.50/0.98  --problem_path                          ""
% 2.50/0.98  --include_path                          ""
% 2.50/0.98  --clausifier                            res/vclausify_rel
% 2.50/0.98  --clausifier_options                    --mode clausify
% 2.50/0.98  --stdin                                 false
% 2.50/0.98  --stats_out                             all
% 2.50/0.98  
% 2.50/0.98  ------ General Options
% 2.50/0.98  
% 2.50/0.99  --fof                                   false
% 2.50/0.99  --time_out_real                         305.
% 2.50/0.99  --time_out_virtual                      -1.
% 2.50/0.99  --symbol_type_check                     false
% 2.50/0.99  --clausify_out                          false
% 2.50/0.99  --sig_cnt_out                           false
% 2.50/0.99  --trig_cnt_out                          false
% 2.50/0.99  --trig_cnt_out_tolerance                1.
% 2.50/0.99  --trig_cnt_out_sk_spl                   false
% 2.50/0.99  --abstr_cl_out                          false
% 2.50/0.99  
% 2.50/0.99  ------ Global Options
% 2.50/0.99  
% 2.50/0.99  --schedule                              default
% 2.50/0.99  --add_important_lit                     false
% 2.50/0.99  --prop_solver_per_cl                    1000
% 2.50/0.99  --min_unsat_core                        false
% 2.50/0.99  --soft_assumptions                      false
% 2.50/0.99  --soft_lemma_size                       3
% 2.50/0.99  --prop_impl_unit_size                   0
% 2.50/0.99  --prop_impl_unit                        []
% 2.50/0.99  --share_sel_clauses                     true
% 2.50/0.99  --reset_solvers                         false
% 2.50/0.99  --bc_imp_inh                            [conj_cone]
% 2.50/0.99  --conj_cone_tolerance                   3.
% 2.50/0.99  --extra_neg_conj                        none
% 2.50/0.99  --large_theory_mode                     true
% 2.50/0.99  --prolific_symb_bound                   200
% 2.50/0.99  --lt_threshold                          2000
% 2.50/0.99  --clause_weak_htbl                      true
% 2.50/0.99  --gc_record_bc_elim                     false
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing Options
% 2.50/0.99  
% 2.50/0.99  --preprocessing_flag                    true
% 2.50/0.99  --time_out_prep_mult                    0.1
% 2.50/0.99  --splitting_mode                        input
% 2.50/0.99  --splitting_grd                         true
% 2.50/0.99  --splitting_cvd                         false
% 2.50/0.99  --splitting_cvd_svl                     false
% 2.50/0.99  --splitting_nvd                         32
% 2.50/0.99  --sub_typing                            true
% 2.50/0.99  --prep_gs_sim                           true
% 2.50/0.99  --prep_unflatten                        true
% 2.50/0.99  --prep_res_sim                          true
% 2.50/0.99  --prep_upred                            true
% 2.50/0.99  --prep_sem_filter                       exhaustive
% 2.50/0.99  --prep_sem_filter_out                   false
% 2.50/0.99  --pred_elim                             true
% 2.50/0.99  --res_sim_input                         true
% 2.50/0.99  --eq_ax_congr_red                       true
% 2.50/0.99  --pure_diseq_elim                       true
% 2.50/0.99  --brand_transform                       false
% 2.50/0.99  --non_eq_to_eq                          false
% 2.50/0.99  --prep_def_merge                        true
% 2.50/0.99  --prep_def_merge_prop_impl              false
% 2.50/0.99  --prep_def_merge_mbd                    true
% 2.50/0.99  --prep_def_merge_tr_red                 false
% 2.50/0.99  --prep_def_merge_tr_cl                  false
% 2.50/0.99  --smt_preprocessing                     true
% 2.50/0.99  --smt_ac_axioms                         fast
% 2.50/0.99  --preprocessed_out                      false
% 2.50/0.99  --preprocessed_stats                    false
% 2.50/0.99  
% 2.50/0.99  ------ Abstraction refinement Options
% 2.50/0.99  
% 2.50/0.99  --abstr_ref                             []
% 2.50/0.99  --abstr_ref_prep                        false
% 2.50/0.99  --abstr_ref_until_sat                   false
% 2.50/0.99  --abstr_ref_sig_restrict                funpre
% 2.50/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/0.99  --abstr_ref_under                       []
% 2.50/0.99  
% 2.50/0.99  ------ SAT Options
% 2.50/0.99  
% 2.50/0.99  --sat_mode                              false
% 2.50/0.99  --sat_fm_restart_options                ""
% 2.50/0.99  --sat_gr_def                            false
% 2.50/0.99  --sat_epr_types                         true
% 2.50/0.99  --sat_non_cyclic_types                  false
% 2.50/0.99  --sat_finite_models                     false
% 2.50/0.99  --sat_fm_lemmas                         false
% 2.50/0.99  --sat_fm_prep                           false
% 2.50/0.99  --sat_fm_uc_incr                        true
% 2.50/0.99  --sat_out_model                         small
% 2.50/0.99  --sat_out_clauses                       false
% 2.50/0.99  
% 2.50/0.99  ------ QBF Options
% 2.50/0.99  
% 2.50/0.99  --qbf_mode                              false
% 2.50/0.99  --qbf_elim_univ                         false
% 2.50/0.99  --qbf_dom_inst                          none
% 2.50/0.99  --qbf_dom_pre_inst                      false
% 2.50/0.99  --qbf_sk_in                             false
% 2.50/0.99  --qbf_pred_elim                         true
% 2.50/0.99  --qbf_split                             512
% 2.50/0.99  
% 2.50/0.99  ------ BMC1 Options
% 2.50/0.99  
% 2.50/0.99  --bmc1_incremental                      false
% 2.50/0.99  --bmc1_axioms                           reachable_all
% 2.50/0.99  --bmc1_min_bound                        0
% 2.50/0.99  --bmc1_max_bound                        -1
% 2.50/0.99  --bmc1_max_bound_default                -1
% 2.50/0.99  --bmc1_symbol_reachability              true
% 2.50/0.99  --bmc1_property_lemmas                  false
% 2.50/0.99  --bmc1_k_induction                      false
% 2.50/0.99  --bmc1_non_equiv_states                 false
% 2.50/0.99  --bmc1_deadlock                         false
% 2.50/0.99  --bmc1_ucm                              false
% 2.50/0.99  --bmc1_add_unsat_core                   none
% 2.50/0.99  --bmc1_unsat_core_children              false
% 2.50/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/0.99  --bmc1_out_stat                         full
% 2.50/0.99  --bmc1_ground_init                      false
% 2.50/0.99  --bmc1_pre_inst_next_state              false
% 2.50/0.99  --bmc1_pre_inst_state                   false
% 2.50/0.99  --bmc1_pre_inst_reach_state             false
% 2.50/0.99  --bmc1_out_unsat_core                   false
% 2.50/0.99  --bmc1_aig_witness_out                  false
% 2.50/0.99  --bmc1_verbose                          false
% 2.50/0.99  --bmc1_dump_clauses_tptp                false
% 2.50/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.50/0.99  --bmc1_dump_file                        -
% 2.50/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.50/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.50/0.99  --bmc1_ucm_extend_mode                  1
% 2.50/0.99  --bmc1_ucm_init_mode                    2
% 2.50/0.99  --bmc1_ucm_cone_mode                    none
% 2.50/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.50/0.99  --bmc1_ucm_relax_model                  4
% 2.50/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.50/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/0.99  --bmc1_ucm_layered_model                none
% 2.50/0.99  --bmc1_ucm_max_lemma_size               10
% 2.50/0.99  
% 2.50/0.99  ------ AIG Options
% 2.50/0.99  
% 2.50/0.99  --aig_mode                              false
% 2.50/0.99  
% 2.50/0.99  ------ Instantiation Options
% 2.50/0.99  
% 2.50/0.99  --instantiation_flag                    true
% 2.50/0.99  --inst_sos_flag                         false
% 2.50/0.99  --inst_sos_phase                        true
% 2.50/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/0.99  --inst_lit_sel_side                     none
% 2.50/0.99  --inst_solver_per_active                1400
% 2.50/0.99  --inst_solver_calls_frac                1.
% 2.50/0.99  --inst_passive_queue_type               priority_queues
% 2.50/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/0.99  --inst_passive_queues_freq              [25;2]
% 2.50/0.99  --inst_dismatching                      true
% 2.50/0.99  --inst_eager_unprocessed_to_passive     true
% 2.50/0.99  --inst_prop_sim_given                   true
% 2.50/0.99  --inst_prop_sim_new                     false
% 2.50/0.99  --inst_subs_new                         false
% 2.50/0.99  --inst_eq_res_simp                      false
% 2.50/0.99  --inst_subs_given                       false
% 2.50/0.99  --inst_orphan_elimination               true
% 2.50/0.99  --inst_learning_loop_flag               true
% 2.50/0.99  --inst_learning_start                   3000
% 2.50/0.99  --inst_learning_factor                  2
% 2.50/0.99  --inst_start_prop_sim_after_learn       3
% 2.50/0.99  --inst_sel_renew                        solver
% 2.50/0.99  --inst_lit_activity_flag                true
% 2.50/0.99  --inst_restr_to_given                   false
% 2.50/0.99  --inst_activity_threshold               500
% 2.50/0.99  --inst_out_proof                        true
% 2.50/0.99  
% 2.50/0.99  ------ Resolution Options
% 2.50/0.99  
% 2.50/0.99  --resolution_flag                       false
% 2.50/0.99  --res_lit_sel                           adaptive
% 2.50/0.99  --res_lit_sel_side                      none
% 2.50/0.99  --res_ordering                          kbo
% 2.50/0.99  --res_to_prop_solver                    active
% 2.50/0.99  --res_prop_simpl_new                    false
% 2.50/0.99  --res_prop_simpl_given                  true
% 2.50/0.99  --res_passive_queue_type                priority_queues
% 2.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/0.99  --res_passive_queues_freq               [15;5]
% 2.50/0.99  --res_forward_subs                      full
% 2.50/0.99  --res_backward_subs                     full
% 2.50/0.99  --res_forward_subs_resolution           true
% 2.50/0.99  --res_backward_subs_resolution          true
% 2.50/0.99  --res_orphan_elimination                true
% 2.50/0.99  --res_time_limit                        2.
% 2.50/0.99  --res_out_proof                         true
% 2.50/0.99  
% 2.50/0.99  ------ Superposition Options
% 2.50/0.99  
% 2.50/0.99  --superposition_flag                    true
% 2.50/0.99  --sup_passive_queue_type                priority_queues
% 2.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.50/0.99  --demod_completeness_check              fast
% 2.50/0.99  --demod_use_ground                      true
% 2.50/0.99  --sup_to_prop_solver                    passive
% 2.50/0.99  --sup_prop_simpl_new                    true
% 2.50/0.99  --sup_prop_simpl_given                  true
% 2.50/0.99  --sup_fun_splitting                     false
% 2.50/0.99  --sup_smt_interval                      50000
% 2.50/0.99  
% 2.50/0.99  ------ Superposition Simplification Setup
% 2.50/0.99  
% 2.50/0.99  --sup_indices_passive                   []
% 2.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_full_bw                           [BwDemod]
% 2.50/0.99  --sup_immed_triv                        [TrivRules]
% 2.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_immed_bw_main                     []
% 2.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.99  
% 2.50/0.99  ------ Combination Options
% 2.50/0.99  
% 2.50/0.99  --comb_res_mult                         3
% 2.50/0.99  --comb_sup_mult                         2
% 2.50/0.99  --comb_inst_mult                        10
% 2.50/0.99  
% 2.50/0.99  ------ Debug Options
% 2.50/0.99  
% 2.50/0.99  --dbg_backtrace                         false
% 2.50/0.99  --dbg_dump_prop_clauses                 false
% 2.50/0.99  --dbg_dump_prop_clauses_file            -
% 2.50/0.99  --dbg_out_stat                          false
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  ------ Proving...
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  % SZS status Theorem for theBenchmark.p
% 2.50/0.99  
% 2.50/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.50/0.99  
% 2.50/0.99  fof(f12,conjecture,(
% 2.50/0.99    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 2.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f13,negated_conjecture,(
% 2.50/0.99    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 2.50/0.99    inference(negated_conjecture,[],[f12])).
% 2.50/0.99  
% 2.50/0.99  fof(f28,plain,(
% 2.50/0.99    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 2.50/0.99    inference(ennf_transformation,[],[f13])).
% 2.50/0.99  
% 2.50/0.99  fof(f29,plain,(
% 2.50/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 2.50/0.99    inference(flattening,[],[f28])).
% 2.50/0.99  
% 2.50/0.99  fof(f32,plain,(
% 2.50/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(X0,X3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,sK4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,sK4,X1))) & r1_tarski(k7_relset_1(X0,X3,sK4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(sK4,X0,X3) & v1_funct_1(sK4))) )),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f31,plain,(
% 2.50/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) & ~v1_xboole_0(sK3))),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f33,plain,(
% 2.50/0.99    ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 2.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f29,f32,f31])).
% 2.50/0.99  
% 2.50/0.99  fof(f56,plain,(
% 2.50/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 2.50/0.99    inference(cnf_transformation,[],[f33])).
% 2.50/0.99  
% 2.50/0.99  fof(f2,axiom,(
% 2.50/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f14,plain,(
% 2.50/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.50/0.99    inference(ennf_transformation,[],[f2])).
% 2.50/0.99  
% 2.50/0.99  fof(f35,plain,(
% 2.50/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f14])).
% 2.50/0.99  
% 2.50/0.99  fof(f3,axiom,(
% 2.50/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f36,plain,(
% 2.50/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.50/0.99    inference(cnf_transformation,[],[f3])).
% 2.50/0.99  
% 2.50/0.99  fof(f4,axiom,(
% 2.50/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f15,plain,(
% 2.50/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.50/0.99    inference(ennf_transformation,[],[f4])).
% 2.50/0.99  
% 2.50/0.99  fof(f37,plain,(
% 2.50/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f15])).
% 2.50/0.99  
% 2.50/0.99  fof(f11,axiom,(
% 2.50/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f26,plain,(
% 2.50/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.50/0.99    inference(ennf_transformation,[],[f11])).
% 2.50/0.99  
% 2.50/0.99  fof(f27,plain,(
% 2.50/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.50/0.99    inference(flattening,[],[f26])).
% 2.50/0.99  
% 2.50/0.99  fof(f52,plain,(
% 2.50/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f27])).
% 2.50/0.99  
% 2.50/0.99  fof(f58,plain,(
% 2.50/0.99    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 2.50/0.99    inference(cnf_transformation,[],[f33])).
% 2.50/0.99  
% 2.50/0.99  fof(f7,axiom,(
% 2.50/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f19,plain,(
% 2.50/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.50/0.99    inference(ennf_transformation,[],[f7])).
% 2.50/0.99  
% 2.50/0.99  fof(f40,plain,(
% 2.50/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.50/0.99    inference(cnf_transformation,[],[f19])).
% 2.50/0.99  
% 2.50/0.99  fof(f10,axiom,(
% 2.50/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f24,plain,(
% 2.50/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.50/0.99    inference(ennf_transformation,[],[f10])).
% 2.50/0.99  
% 2.50/0.99  fof(f25,plain,(
% 2.50/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.50/0.99    inference(flattening,[],[f24])).
% 2.50/0.99  
% 2.50/0.99  fof(f49,plain,(
% 2.50/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f25])).
% 2.50/0.99  
% 2.50/0.99  fof(f54,plain,(
% 2.50/0.99    v1_funct_1(sK4)),
% 2.50/0.99    inference(cnf_transformation,[],[f33])).
% 2.50/0.99  
% 2.50/0.99  fof(f9,axiom,(
% 2.50/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 2.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f22,plain,(
% 2.50/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.50/0.99    inference(ennf_transformation,[],[f9])).
% 2.50/0.99  
% 2.50/0.99  fof(f23,plain,(
% 2.50/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.50/0.99    inference(flattening,[],[f22])).
% 2.50/0.99  
% 2.50/0.99  fof(f47,plain,(
% 2.50/0.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f23])).
% 2.50/0.99  
% 2.50/0.99  fof(f48,plain,(
% 2.50/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f23])).
% 2.50/0.99  
% 2.50/0.99  fof(f8,axiom,(
% 2.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f20,plain,(
% 2.50/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.50/0.99    inference(ennf_transformation,[],[f8])).
% 2.50/0.99  
% 2.50/0.99  fof(f21,plain,(
% 2.50/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.50/0.99    inference(flattening,[],[f20])).
% 2.50/0.99  
% 2.50/0.99  fof(f30,plain,(
% 2.50/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.50/0.99    inference(nnf_transformation,[],[f21])).
% 2.50/0.99  
% 2.50/0.99  fof(f41,plain,(
% 2.50/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.50/0.99    inference(cnf_transformation,[],[f30])).
% 2.50/0.99  
% 2.50/0.99  fof(f55,plain,(
% 2.50/0.99    v1_funct_2(sK4,sK0,sK3)),
% 2.50/0.99    inference(cnf_transformation,[],[f33])).
% 2.50/0.99  
% 2.50/0.99  fof(f6,axiom,(
% 2.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f18,plain,(
% 2.50/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.50/0.99    inference(ennf_transformation,[],[f6])).
% 2.50/0.99  
% 2.50/0.99  fof(f39,plain,(
% 2.50/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.50/0.99    inference(cnf_transformation,[],[f18])).
% 2.50/0.99  
% 2.50/0.99  fof(f1,axiom,(
% 2.50/0.99    v1_xboole_0(k1_xboole_0)),
% 2.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f34,plain,(
% 2.50/0.99    v1_xboole_0(k1_xboole_0)),
% 2.50/0.99    inference(cnf_transformation,[],[f1])).
% 2.50/0.99  
% 2.50/0.99  fof(f53,plain,(
% 2.50/0.99    ~v1_xboole_0(sK3)),
% 2.50/0.99    inference(cnf_transformation,[],[f33])).
% 2.50/0.99  
% 2.50/0.99  fof(f5,axiom,(
% 2.50/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f16,plain,(
% 2.50/0.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.50/0.99    inference(ennf_transformation,[],[f5])).
% 2.50/0.99  
% 2.50/0.99  fof(f17,plain,(
% 2.50/0.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.50/0.99    inference(flattening,[],[f16])).
% 2.50/0.99  
% 2.50/0.99  fof(f38,plain,(
% 2.50/0.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f17])).
% 2.50/0.99  
% 2.50/0.99  fof(f57,plain,(
% 2.50/0.99    r1_tarski(sK1,sK0)),
% 2.50/0.99    inference(cnf_transformation,[],[f33])).
% 2.50/0.99  
% 2.50/0.99  fof(f59,plain,(
% 2.50/0.99    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 2.50/0.99    inference(cnf_transformation,[],[f33])).
% 2.50/0.99  
% 2.50/0.99  fof(f51,plain,(
% 2.50/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f27])).
% 2.50/0.99  
% 2.50/0.99  cnf(c_22,negated_conjecture,
% 2.50/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
% 2.50/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_834,negated_conjecture,
% 2.50/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1327,plain,
% 2.50/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_834]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.50/0.99      | ~ v1_relat_1(X1)
% 2.50/0.99      | v1_relat_1(X0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_842,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
% 2.50/0.99      | ~ v1_relat_1(X1_49)
% 2.50/0.99      | v1_relat_1(X0_49) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1319,plain,
% 2.50/0.99      ( m1_subset_1(X0_49,k1_zfmisc_1(X1_49)) != iProver_top
% 2.50/0.99      | v1_relat_1(X1_49) != iProver_top
% 2.50/0.99      | v1_relat_1(X0_49) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_842]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1756,plain,
% 2.50/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top
% 2.50/0.99      | v1_relat_1(sK4) = iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1327,c_1319]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2,plain,
% 2.50/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.50/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_841,plain,
% 2.50/0.99      ( v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1846,plain,
% 2.50/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_841]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1847,plain,
% 2.50/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1846]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1967,plain,
% 2.50/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_1756,c_1847]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3,plain,
% 2.50/0.99      ( ~ v1_relat_1(X0)
% 2.50/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.50/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_840,plain,
% 2.50/0.99      ( ~ v1_relat_1(X0_49)
% 2.50/0.99      | k2_relat_1(k7_relat_1(X0_49,X1_49)) = k9_relat_1(X0_49,X1_49) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1321,plain,
% 2.50/0.99      ( k2_relat_1(k7_relat_1(X0_49,X1_49)) = k9_relat_1(X0_49,X1_49)
% 2.50/0.99      | v1_relat_1(X0_49) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_840]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1972,plain,
% 2.50/0.99      ( k2_relat_1(k7_relat_1(sK4,X0_49)) = k9_relat_1(sK4,X0_49) ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1967,c_1321]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_16,plain,
% 2.50/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.50/0.99      | ~ v1_funct_1(X0)
% 2.50/0.99      | ~ v1_relat_1(X0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_20,negated_conjecture,
% 2.50/0.99      ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
% 2.50/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_333,plain,
% 2.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.50/0.99      | ~ v1_funct_1(X0)
% 2.50/0.99      | ~ v1_relat_1(X0)
% 2.50/0.99      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0)
% 2.50/0.99      | sK2 != X1 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_334,plain,
% 2.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),sK2)))
% 2.50/0.99      | ~ v1_funct_1(X0)
% 2.50/0.99      | ~ v1_relat_1(X0)
% 2.50/0.99      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0) ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_333]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_829,plain,
% 2.50/0.99      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_49),sK2)))
% 2.50/0.99      | ~ v1_funct_1(X0_49)
% 2.50/0.99      | ~ v1_relat_1(X0_49)
% 2.50/0.99      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0_49) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_334]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1331,plain,
% 2.50/0.99      ( k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0_49)
% 2.50/0.99      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_49),sK2))) = iProver_top
% 2.50/0.99      | v1_funct_1(X0_49) != iProver_top
% 2.50/0.99      | v1_relat_1(X0_49) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_829]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_6,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.50/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_838,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.50/0.99      | k7_relset_1(X1_49,X2_49,X0_49,X3_49) = k9_relat_1(X0_49,X3_49) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1323,plain,
% 2.50/0.99      ( k7_relset_1(X0_49,X1_49,X2_49,X3_49) = k9_relat_1(X2_49,X3_49)
% 2.50/0.99      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_838]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1928,plain,
% 2.50/0.99      ( k7_relset_1(sK0,sK3,sK4,X0_49) = k9_relat_1(sK4,X0_49) ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1327,c_1323]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1990,plain,
% 2.50/0.99      ( k9_relat_1(sK4,sK1) != k2_relat_1(X0_49)
% 2.50/0.99      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_49),sK2))) = iProver_top
% 2.50/0.99      | v1_funct_1(X0_49) != iProver_top
% 2.50/0.99      | v1_relat_1(X0_49) != iProver_top ),
% 2.50/0.99      inference(demodulation,[status(thm)],[c_1331,c_1928]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2309,plain,
% 2.50/0.99      ( k9_relat_1(sK4,X0_49) != k9_relat_1(sK4,sK1)
% 2.50/0.99      | m1_subset_1(k7_relat_1(sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X0_49)),sK2))) = iProver_top
% 2.50/0.99      | v1_funct_1(k7_relat_1(sK4,X0_49)) != iProver_top
% 2.50/0.99      | v1_relat_1(k7_relat_1(sK4,X0_49)) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1972,c_1990]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_15,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.99      | ~ v1_funct_1(X0)
% 2.50/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.50/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_835,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.50/0.99      | ~ v1_funct_1(X0_49)
% 2.50/0.99      | k2_partfun1(X1_49,X2_49,X0_49,X3_49) = k7_relat_1(X0_49,X3_49) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1326,plain,
% 2.50/0.99      ( k2_partfun1(X0_49,X1_49,X2_49,X3_49) = k7_relat_1(X2_49,X3_49)
% 2.50/0.99      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 2.50/0.99      | v1_funct_1(X2_49) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_835]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2246,plain,
% 2.50/0.99      ( k2_partfun1(sK0,sK3,sK4,X0_49) = k7_relat_1(sK4,X0_49)
% 2.50/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1327,c_1326]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_24,negated_conjecture,
% 2.50/0.99      ( v1_funct_1(sK4) ),
% 2.50/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1690,plain,
% 2.50/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 2.50/0.99      | ~ v1_funct_1(sK4)
% 2.50/0.99      | k2_partfun1(X0_49,X1_49,sK4,X2_49) = k7_relat_1(sK4,X2_49) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_835]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1809,plain,
% 2.50/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.50/0.99      | ~ v1_funct_1(sK4)
% 2.50/0.99      | k2_partfun1(sK0,sK3,sK4,X0_49) = k7_relat_1(sK4,X0_49) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1690]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2395,plain,
% 2.50/0.99      ( k2_partfun1(sK0,sK3,sK4,X0_49) = k7_relat_1(sK4,X0_49) ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_2246,c_24,c_22,c_1809]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_14,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.99      | ~ v1_funct_1(X0)
% 2.50/0.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 2.50/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_836,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.50/0.99      | ~ v1_funct_1(X0_49)
% 2.50/0.99      | v1_funct_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49)) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1325,plain,
% 2.50/0.99      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
% 2.50/0.99      | v1_funct_1(X0_49) != iProver_top
% 2.50/0.99      | v1_funct_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49)) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_836]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2222,plain,
% 2.50/0.99      ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0_49)) = iProver_top
% 2.50/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1327,c_1325]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_27,plain,
% 2.50/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_29,plain,
% 2.50/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1667,plain,
% 2.50/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 2.50/0.99      | v1_funct_1(k2_partfun1(X0_49,X1_49,sK4,X2_49))
% 2.50/0.99      | ~ v1_funct_1(sK4) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_836]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1804,plain,
% 2.50/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.50/0.99      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0_49))
% 2.50/0.99      | ~ v1_funct_1(sK4) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1667]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1805,plain,
% 2.50/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 2.50/0.99      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0_49)) = iProver_top
% 2.50/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1804]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2387,plain,
% 2.50/0.99      ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0_49)) = iProver_top ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_2222,c_27,c_29,c_1805]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2403,plain,
% 2.50/0.99      ( v1_funct_1(k7_relat_1(sK4,X0_49)) = iProver_top ),
% 2.50/0.99      inference(demodulation,[status(thm)],[c_2395,c_2387]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_13,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.99      | ~ v1_funct_1(X0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_837,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.50/0.99      | m1_subset_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.50/0.99      | ~ v1_funct_1(X0_49) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1324,plain,
% 2.50/0.99      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
% 2.50/0.99      | m1_subset_1(k2_partfun1(X1_49,X2_49,X0_49,X3_49),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) = iProver_top
% 2.50/0.99      | v1_funct_1(X0_49) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_837]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2445,plain,
% 2.50/0.99      ( m1_subset_1(k7_relat_1(sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top
% 2.50/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 2.50/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2395,c_1324]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2728,plain,
% 2.50/0.99      ( m1_subset_1(k7_relat_1(sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_2445,c_27,c_29]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2736,plain,
% 2.50/0.99      ( v1_relat_1(k7_relat_1(sK4,X0_49)) = iProver_top
% 2.50/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2728,c_1319]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3787,plain,
% 2.50/0.99      ( k9_relat_1(sK4,X0_49) != k9_relat_1(sK4,sK1)
% 2.50/0.99      | m1_subset_1(k7_relat_1(sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X0_49)),sK2))) = iProver_top ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_2309,c_1847,c_2403,c_2736]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3795,plain,
% 2.50/0.99      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,sK1)),sK2))) = iProver_top ),
% 2.50/0.99      inference(equality_resolution,[status(thm)],[c_3787]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_12,plain,
% 2.50/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.50/0.99      | k1_xboole_0 = X2 ),
% 2.50/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_23,negated_conjecture,
% 2.50/0.99      ( v1_funct_2(sK4,sK0,sK3) ),
% 2.50/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_605,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.50/0.99      | sK4 != X0
% 2.50/0.99      | sK3 != X2
% 2.50/0.99      | sK0 != X1
% 2.50/0.99      | k1_xboole_0 = X2 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_606,plain,
% 2.50/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.50/0.99      | k1_relset_1(sK0,sK3,sK4) = sK0
% 2.50/0.99      | k1_xboole_0 = sK3 ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_605]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_608,plain,
% 2.50/0.99      ( k1_relset_1(sK0,sK3,sK4) = sK0 | k1_xboole_0 = sK3 ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_606,c_22]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_819,plain,
% 2.50/0.99      ( k1_relset_1(sK0,sK3,sK4) = sK0 | k1_xboole_0 = sK3 ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_608]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_5,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_839,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.50/0.99      | k1_relset_1(X1_49,X2_49,X0_49) = k1_relat_1(X0_49) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1322,plain,
% 2.50/0.99      ( k1_relset_1(X0_49,X1_49,X2_49) = k1_relat_1(X2_49)
% 2.50/0.99      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_839]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1822,plain,
% 2.50/0.99      ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1327,c_1322]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1931,plain,
% 2.50/0.99      ( k1_relat_1(sK4) = sK0 | sK3 = k1_xboole_0 ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_819,c_1822]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_0,plain,
% 2.50/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_25,negated_conjecture,
% 2.50/0.99      ( ~ v1_xboole_0(sK3) ),
% 2.50/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_280,plain,
% 2.50/0.99      ( sK3 != k1_xboole_0 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_25]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_832,plain,
% 2.50/0.99      ( sK3 != k1_xboole_0 ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_280]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2567,plain,
% 2.50/0.99      ( k1_relat_1(sK4) = sK0 ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_1931,c_832]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_4,plain,
% 2.50/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 2.50/0.99      | ~ v1_relat_1(X1)
% 2.50/0.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 2.50/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_21,negated_conjecture,
% 2.50/0.99      ( r1_tarski(sK1,sK0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_300,plain,
% 2.50/0.99      ( ~ v1_relat_1(X0)
% 2.50/0.99      | k1_relat_1(X0) != sK0
% 2.50/0.99      | k1_relat_1(k7_relat_1(X0,X1)) = X1
% 2.50/0.99      | sK1 != X1 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_21]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_301,plain,
% 2.50/0.99      ( ~ v1_relat_1(X0)
% 2.50/0.99      | k1_relat_1(X0) != sK0
% 2.50/0.99      | k1_relat_1(k7_relat_1(X0,sK1)) = sK1 ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_300]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_830,plain,
% 2.50/0.99      ( ~ v1_relat_1(X0_49)
% 2.50/0.99      | k1_relat_1(X0_49) != sK0
% 2.50/0.99      | k1_relat_1(k7_relat_1(X0_49,sK1)) = sK1 ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_301]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1330,plain,
% 2.50/0.99      ( k1_relat_1(X0_49) != sK0
% 2.50/0.99      | k1_relat_1(k7_relat_1(X0_49,sK1)) = sK1
% 2.50/0.99      | v1_relat_1(X0_49) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_830]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2571,plain,
% 2.50/0.99      ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1
% 2.50/0.99      | v1_relat_1(sK4) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2567,c_1330]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1757,plain,
% 2.50/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) | v1_relat_1(sK4) ),
% 2.50/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1756]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2020,plain,
% 2.50/0.99      ( ~ v1_relat_1(sK4)
% 2.50/0.99      | k1_relat_1(k7_relat_1(sK4,sK1)) = sK1
% 2.50/0.99      | k1_relat_1(sK4) != sK0 ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_830]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2636,plain,
% 2.50/0.99      ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1 ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_2571,c_832,c_1757,c_1846,c_1931,c_2020]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3796,plain,
% 2.50/0.99      ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.50/0.99      inference(light_normalisation,[status(thm)],[c_3795,c_2636]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_19,negated_conjecture,
% 2.50/0.99      ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
% 2.50/0.99      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.50/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
% 2.50/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_17,plain,
% 2.50/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.50/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.50/0.99      | ~ v1_funct_1(X0)
% 2.50/0.99      | ~ v1_relat_1(X0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_315,plain,
% 2.50/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.50/0.99      | ~ v1_funct_1(X0)
% 2.50/0.99      | ~ v1_relat_1(X0)
% 2.50/0.99      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0)
% 2.50/0.99      | sK2 != X1 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_316,plain,
% 2.50/0.99      ( v1_funct_2(X0,k1_relat_1(X0),sK2)
% 2.50/0.99      | ~ v1_funct_1(X0)
% 2.50/0.99      | ~ v1_relat_1(X0)
% 2.50/0.99      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0) ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_315]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_688,plain,
% 2.50/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.50/0.99      | ~ v1_funct_1(X0)
% 2.50/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.50/0.99      | ~ v1_relat_1(X0)
% 2.50/0.99      | k2_partfun1(sK0,sK3,sK4,sK1) != X0
% 2.50/0.99      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(X0)
% 2.50/0.99      | k1_relat_1(X0) != sK1
% 2.50/0.99      | sK2 != sK2 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_316]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_689,plain,
% 2.50/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.50/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.50/0.99      | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.50/0.99      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.50/0.99      | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_688]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_815,plain,
% 2.50/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.50/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.50/0.99      | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.50/0.99      | k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.50/0.99      | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1 ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_689]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1344,plain,
% 2.50/0.99      ( k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.50/0.99      | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 2.50/0.99      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.50/0.99      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
% 2.50/0.99      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_921,plain,
% 2.50/0.99      ( k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.50/0.99      | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 2.50/0.99      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.50/0.99      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
% 2.50/0.99      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1849,plain,
% 2.50/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.50/0.99      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.50/0.99      | ~ v1_funct_1(sK4) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1804]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1850,plain,
% 2.50/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 2.50/0.99      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) = iProver_top
% 2.50/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1849]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1654,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 2.50/0.99      | v1_relat_1(X0_49)
% 2.50/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1_49,X2_49)) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_842]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1902,plain,
% 2.50/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.50/0.99      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,X0_49))
% 2.50/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1654]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2071,plain,
% 2.50/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.50/0.99      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.50/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1902]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2072,plain,
% 2.50/0.99      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 2.50/0.99      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) = iProver_top
% 2.50/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2071]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1695,plain,
% 2.50/0.99      ( m1_subset_1(k2_partfun1(X0_49,X1_49,sK4,X2_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 2.50/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 2.50/0.99      | ~ v1_funct_1(sK4) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_837]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1823,plain,
% 2.50/0.99      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,X0_49),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.50/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.50/0.99      | ~ v1_funct_1(sK4) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1695]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2383,plain,
% 2.50/0.99      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.50/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 2.50/0.99      | ~ v1_funct_1(sK4) ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_1823]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2384,plain,
% 2.50/0.99      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top
% 2.50/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 2.50/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2383]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2548,plain,
% 2.50/0.99      ( k7_relset_1(sK0,sK3,sK4,sK1) != k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 2.50/0.99      | k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != sK1
% 2.50/0.99      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_1344,c_27,c_29,c_921,c_1847,c_1850,c_2072,c_2384]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2552,plain,
% 2.50/0.99      ( k9_relat_1(sK4,sK1) != k9_relat_1(sK4,sK1)
% 2.50/0.99      | k1_relat_1(k7_relat_1(sK4,sK1)) != sK1
% 2.50/0.99      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.50/0.99      inference(demodulation,[status(thm)],[c_2548,c_1928,c_1972,c_2395]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2553,plain,
% 2.50/0.99      ( k1_relat_1(k7_relat_1(sK4,sK1)) != sK1
% 2.50/0.99      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.50/0.99      inference(equality_resolution_simp,[status(thm)],[c_2552]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(contradiction,plain,
% 2.50/0.99      ( $false ),
% 2.50/0.99      inference(minisat,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_3796,c_2553,c_2020,c_1931,c_1846,c_1757,c_832]) ).
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.50/0.99  
% 2.50/0.99  ------                               Statistics
% 2.50/0.99  
% 2.50/0.99  ------ General
% 2.50/0.99  
% 2.50/0.99  abstr_ref_over_cycles:                  0
% 2.50/0.99  abstr_ref_under_cycles:                 0
% 2.50/0.99  gc_basic_clause_elim:                   0
% 2.50/0.99  forced_gc_time:                         0
% 2.50/0.99  parsing_time:                           0.021
% 2.50/0.99  unif_index_cands_time:                  0.
% 2.50/0.99  unif_index_add_time:                    0.
% 2.50/0.99  orderings_time:                         0.
% 2.50/0.99  out_proof_time:                         0.011
% 2.50/0.99  total_time:                             0.165
% 2.50/0.99  num_of_symbols:                         54
% 2.50/0.99  num_of_terms:                           3861
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing
% 2.50/0.99  
% 2.50/0.99  num_of_splits:                          0
% 2.50/0.99  num_of_split_atoms:                     0
% 2.50/0.99  num_of_reused_defs:                     0
% 2.50/0.99  num_eq_ax_congr_red:                    9
% 2.50/0.99  num_of_sem_filtered_clauses:            1
% 2.50/0.99  num_of_subtypes:                        2
% 2.50/0.99  monotx_restored_types:                  0
% 2.50/0.99  sat_num_of_epr_types:                   0
% 2.50/0.99  sat_num_of_non_cyclic_types:            0
% 2.50/0.99  sat_guarded_non_collapsed_types:        1
% 2.50/0.99  num_pure_diseq_elim:                    0
% 2.50/0.99  simp_replaced_by:                       0
% 2.50/0.99  res_preprocessed:                       112
% 2.50/0.99  prep_upred:                             0
% 2.50/0.99  prep_unflattend:                        55
% 2.50/0.99  smt_new_axioms:                         0
% 2.50/0.99  pred_elim_cands:                        6
% 2.50/0.99  pred_elim:                              3
% 2.50/0.99  pred_elim_cl:                           -4
% 2.50/0.99  pred_elim_cycles:                       4
% 2.50/0.99  merged_defs:                            0
% 2.50/0.99  merged_defs_ncl:                        0
% 2.50/0.99  bin_hyper_res:                          0
% 2.50/0.99  prep_cycles:                            3
% 2.50/0.99  pred_elim_time:                         0.013
% 2.50/0.99  splitting_time:                         0.
% 2.50/0.99  sem_filter_time:                        0.
% 2.50/0.99  monotx_time:                            0.
% 2.50/0.99  subtype_inf_time:                       0.
% 2.50/0.99  
% 2.50/0.99  ------ Problem properties
% 2.50/0.99  
% 2.50/0.99  clauses:                                29
% 2.50/0.99  conjectures:                            2
% 2.50/0.99  epr:                                    2
% 2.50/0.99  horn:                                   24
% 2.50/0.99  ground:                                 11
% 2.50/0.99  unary:                                  4
% 2.50/0.99  binary:                                 4
% 2.50/0.99  lits:                                   108
% 2.50/0.99  lits_eq:                                50
% 2.50/0.99  fd_pure:                                0
% 2.50/0.99  fd_pseudo:                              0
% 2.50/0.99  fd_cond:                                2
% 2.50/0.99  fd_pseudo_cond:                         0
% 2.50/0.99  ac_symbols:                             0
% 2.50/0.99  
% 2.50/0.99  ------ Propositional Solver
% 2.50/0.99  
% 2.50/0.99  prop_solver_calls:                      25
% 2.50/0.99  prop_fast_solver_calls:                 1083
% 2.50/0.99  smt_solver_calls:                       0
% 2.50/0.99  smt_fast_solver_calls:                  0
% 2.50/0.99  prop_num_of_clauses:                    1224
% 2.50/0.99  prop_preprocess_simplified:             3906
% 2.50/0.99  prop_fo_subsumed:                       40
% 2.50/0.99  prop_solver_time:                       0.
% 2.50/0.99  smt_solver_time:                        0.
% 2.50/0.99  smt_fast_solver_time:                   0.
% 2.50/0.99  prop_fast_solver_time:                  0.
% 2.50/0.99  prop_unsat_core_time:                   0.
% 2.50/0.99  
% 2.50/0.99  ------ QBF
% 2.50/0.99  
% 2.50/0.99  qbf_q_res:                              0
% 2.50/0.99  qbf_num_tautologies:                    0
% 2.50/0.99  qbf_prep_cycles:                        0
% 2.50/0.99  
% 2.50/0.99  ------ BMC1
% 2.50/0.99  
% 2.50/0.99  bmc1_current_bound:                     -1
% 2.50/0.99  bmc1_last_solved_bound:                 -1
% 2.50/0.99  bmc1_unsat_core_size:                   -1
% 2.50/0.99  bmc1_unsat_core_parents_size:           -1
% 2.50/0.99  bmc1_merge_next_fun:                    0
% 2.50/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.50/0.99  
% 2.50/0.99  ------ Instantiation
% 2.50/0.99  
% 2.50/0.99  inst_num_of_clauses:                    349
% 2.50/0.99  inst_num_in_passive:                    39
% 2.50/0.99  inst_num_in_active:                     261
% 2.50/0.99  inst_num_in_unprocessed:                49
% 2.50/0.99  inst_num_of_loops:                      280
% 2.50/0.99  inst_num_of_learning_restarts:          0
% 2.50/0.99  inst_num_moves_active_passive:          14
% 2.50/0.99  inst_lit_activity:                      0
% 2.50/0.99  inst_lit_activity_moves:                0
% 2.50/0.99  inst_num_tautologies:                   0
% 2.50/0.99  inst_num_prop_implied:                  0
% 2.50/0.99  inst_num_existing_simplified:           0
% 2.50/0.99  inst_num_eq_res_simplified:             0
% 2.50/0.99  inst_num_child_elim:                    0
% 2.50/0.99  inst_num_of_dismatching_blockings:      68
% 2.50/0.99  inst_num_of_non_proper_insts:           310
% 2.50/0.99  inst_num_of_duplicates:                 0
% 2.50/0.99  inst_inst_num_from_inst_to_res:         0
% 2.50/0.99  inst_dismatching_checking_time:         0.
% 2.50/0.99  
% 2.50/0.99  ------ Resolution
% 2.50/0.99  
% 2.50/0.99  res_num_of_clauses:                     0
% 2.50/0.99  res_num_in_passive:                     0
% 2.50/0.99  res_num_in_active:                      0
% 2.50/0.99  res_num_of_loops:                       115
% 2.50/0.99  res_forward_subset_subsumed:            34
% 2.50/0.99  res_backward_subset_subsumed:           4
% 2.50/0.99  res_forward_subsumed:                   0
% 2.50/0.99  res_backward_subsumed:                  0
% 2.50/0.99  res_forward_subsumption_resolution:     0
% 2.50/0.99  res_backward_subsumption_resolution:    0
% 2.50/0.99  res_clause_to_clause_subsumption:       107
% 2.50/0.99  res_orphan_elimination:                 0
% 2.50/0.99  res_tautology_del:                      75
% 2.50/0.99  res_num_eq_res_simplified:              0
% 2.50/0.99  res_num_sel_changes:                    0
% 2.50/0.99  res_moves_from_active_to_pass:          0
% 2.50/0.99  
% 2.50/0.99  ------ Superposition
% 2.50/0.99  
% 2.50/0.99  sup_time_total:                         0.
% 2.50/0.99  sup_time_generating:                    0.
% 2.50/0.99  sup_time_sim_full:                      0.
% 2.50/0.99  sup_time_sim_immed:                     0.
% 2.50/0.99  
% 2.50/0.99  sup_num_of_clauses:                     74
% 2.50/0.99  sup_num_in_active:                      46
% 2.50/0.99  sup_num_in_passive:                     28
% 2.50/0.99  sup_num_of_loops:                       54
% 2.50/0.99  sup_fw_superposition:                   29
% 2.50/0.99  sup_bw_superposition:                   23
% 2.50/0.99  sup_immediate_simplified:               4
% 2.50/0.99  sup_given_eliminated:                   0
% 2.50/0.99  comparisons_done:                       0
% 2.50/0.99  comparisons_avoided:                    0
% 2.50/0.99  
% 2.50/0.99  ------ Simplifications
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  sim_fw_subset_subsumed:                 1
% 2.50/0.99  sim_bw_subset_subsumed:                 1
% 2.50/0.99  sim_fw_subsumed:                        1
% 2.50/0.99  sim_bw_subsumed:                        0
% 2.50/0.99  sim_fw_subsumption_res:                 3
% 2.50/0.99  sim_bw_subsumption_res:                 0
% 2.50/0.99  sim_tautology_del:                      0
% 2.50/0.99  sim_eq_tautology_del:                   0
% 2.50/0.99  sim_eq_res_simp:                        1
% 2.50/0.99  sim_fw_demodulated:                     6
% 2.50/0.99  sim_bw_demodulated:                     8
% 2.50/0.99  sim_light_normalised:                   2
% 2.50/0.99  sim_joinable_taut:                      0
% 2.50/0.99  sim_joinable_simp:                      0
% 2.50/0.99  sim_ac_normalised:                      0
% 2.50/0.99  sim_smt_subsumption:                    0
% 2.50/0.99  
%------------------------------------------------------------------------------
