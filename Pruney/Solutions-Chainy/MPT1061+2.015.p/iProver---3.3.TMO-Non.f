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
% DateTime   : Thu Dec  3 12:09:32 EST 2020

% Result     : Timeout 59.38s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  342 (3924 expanded)
%              Number of clauses        :  249 (1463 expanded)
%              Number of leaves         :   30 ( 872 expanded)
%              Depth                    :   27
%              Number of atoms          :  960 (20087 expanded)
%              Number of equality atoms :  486 (2268 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f56,plain,(
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

fof(f55,plain,
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

fof(f57,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) )
    & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    & v1_funct_2(sK4,sK0,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f47,f56,f55])).

fof(f97,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f99,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f98,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f18,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f94,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f100,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f65])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f104,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f108,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f85])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1522,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1494,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1510,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3751,plain,
    ( k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1494,c_1510])).

cnf(c_37,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1496,plain,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3893,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3751,c_1496])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1525,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1521,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2368,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK0,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1494,c_1521])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_265,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_266,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_265])).

cnf(c_332,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_266])).

cnf(c_1490,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_2608,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2368,c_1490])).

cnf(c_2007,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK0,sK3)) ),
    inference(resolution,[status(thm)],[c_10,c_39])).

cnf(c_2400,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK3))
    | v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_332,c_2007])).

cnf(c_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2542,plain,
    ( v1_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2400,c_17])).

cnf(c_2543,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2542])).

cnf(c_3174,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2608,c_2543])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1514,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3179,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_3174,c_1514])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1509,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1511,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8258,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1511])).

cnf(c_195757,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,X2)) = k1_relat_1(k7_relat_1(sK4,X2))
    | r1_tarski(k9_relat_1(sK4,X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,X2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3179,c_8258])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1512,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2774,plain,
    ( v4_relat_1(sK4,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1494,c_1512])).

cnf(c_16,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1516,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4769,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2774,c_1516])).

cnf(c_2021,plain,
    ( v4_relat_1(sK4,sK0) ),
    inference(resolution,[status(thm)],[c_20,c_39])).

cnf(c_2844,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0))
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_16,c_2021])).

cnf(c_2845,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2844])).

cnf(c_5073,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4769,c_2543,c_2845])).

cnf(c_225512,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK4,X2)) = k1_relat_1(k7_relat_1(sK4,X2))
    | r1_tarski(k9_relat_1(sK4,X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,X2)),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_195757,c_5073])).

cnf(c_225516,plain,
    ( k1_relset_1(k1_relat_1(k7_relat_1(sK4,X0)),X1,k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0))
    | r1_tarski(k9_relat_1(sK4,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_225512])).

cnf(c_225851,plain,
    ( k1_relset_1(k1_relat_1(k7_relat_1(sK4,sK1)),sK2,k7_relat_1(sK4,sK1)) = k1_relat_1(k7_relat_1(sK4,sK1)) ),
    inference(superposition,[status(thm)],[c_3893,c_225516])).

cnf(c_38,negated_conjecture,
    ( r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1495,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1503,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_10004,plain,
    ( k1_relset_1(sK0,sK3,sK4) = sK0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1494,c_1503])).

cnf(c_2952,plain,
    ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1494,c_1511])).

cnf(c_10032,plain,
    ( k1_relat_1(sK4) = sK0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10004,c_2952])).

cnf(c_42,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_45,plain,
    ( v1_funct_2(sK4,sK0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_673,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1845,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_1847,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1845])).

cnf(c_10437,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10032,c_42,c_45,c_0,c_1847])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1513,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10441,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10437,c_1513])).

cnf(c_12242,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | k1_relat_1(k7_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10441,c_2543])).

cnf(c_12243,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12242])).

cnf(c_12253,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1495,c_12243])).

cnf(c_225857,plain,
    ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_225851,c_12253])).

cnf(c_27,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1505,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_226126,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) = iProver_top
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_225857,c_1505])).

cnf(c_36,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1497,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_8261,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) != iProver_top
    | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) != iProver_top
    | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1497])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1500,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_8773,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1494,c_1500])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1985,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_2108,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_1985])).

cnf(c_8861,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8773,c_41,c_39,c_2108])).

cnf(c_9055,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) != iProver_top
    | r1_tarski(k9_relat_1(sK4,sK1),sK2) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8261,c_3179,c_8861])).

cnf(c_9061,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9055,c_5073,c_3893])).

cnf(c_12270,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12253,c_9061])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1501,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5962,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1494,c_1501])).

cnf(c_44,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_46,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_1942,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK4,X2))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2102,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1942])).

cnf(c_2103,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2102])).

cnf(c_6402,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5962,c_44,c_46,c_2103])).

cnf(c_8867,plain,
    ( v1_funct_1(k7_relat_1(sK4,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8861,c_6402])).

cnf(c_14582,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12270,c_8867,c_1525])).

cnf(c_226953,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_226126,c_14582])).

cnf(c_226959,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1522,c_226953])).

cnf(c_6681,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK0,sK3,sK4,sK1) = k7_relat_1(sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_2108])).

cnf(c_672,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3090,plain,
    ( X0 != X1
    | X0 = k2_partfun1(sK0,sK3,sK4,X2)
    | k2_partfun1(sK0,sK3,sK4,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_4128,plain,
    ( X0 = k2_partfun1(sK0,sK3,sK4,X1)
    | X0 != k7_relat_1(sK4,X1)
    | k2_partfun1(sK0,sK3,sK4,X1) != k7_relat_1(sK4,X1) ),
    inference(instantiation,[status(thm)],[c_3090])).

cnf(c_5781,plain,
    ( k2_partfun1(sK0,sK3,sK4,X0) != k7_relat_1(sK4,X0)
    | k7_relat_1(sK4,X0) = k2_partfun1(sK0,sK3,sK4,X0)
    | k7_relat_1(sK4,X0) != k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_4128])).

cnf(c_22975,plain,
    ( k2_partfun1(sK0,sK3,sK4,sK1) != k7_relat_1(sK4,sK1)
    | k7_relat_1(sK4,sK1) = k2_partfun1(sK0,sK3,sK4,sK1)
    | k7_relat_1(sK4,sK1) != k7_relat_1(sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_5781])).

cnf(c_671,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5782,plain,
    ( k7_relat_1(sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_61817,plain,
    ( k7_relat_1(sK4,sK1) = k7_relat_1(sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_5782])).

cnf(c_101584,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(X0))
    | r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_103038,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK0,sK3)) ),
    inference(instantiation,[status(thm)],[c_101584])).

cnf(c_103040,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK0,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_103038])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_103039,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_103042,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_103039])).

cnf(c_106636,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_106641,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_106636])).

cnf(c_107712,plain,
    ( ~ r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_137097,plain,
    ( ~ r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK0,sK3))
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
    inference(instantiation,[status(thm)],[c_107712])).

cnf(c_137098,plain,
    ( r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK0,sK3)) != iProver_top
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_137097])).

cnf(c_678,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_126546,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(sK4,sK1))
    | k7_relat_1(sK4,sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_161618,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | v1_relat_1(k7_relat_1(sK4,sK1))
    | k7_relat_1(sK4,sK1) != k2_partfun1(sK0,sK3,sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_126546])).

cnf(c_161634,plain,
    ( k7_relat_1(sK4,sK1) != k2_partfun1(sK0,sK3,sK4,sK1)
    | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_161618])).

cnf(c_195209,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_195210,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_195209])).

cnf(c_226960,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_226953])).

cnf(c_226965,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_226960,c_12253])).

cnf(c_226966,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k9_relat_1(sK4,sK1),sK2) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_226965,c_3179])).

cnf(c_227303,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_226959,c_41,c_44,c_39,c_46,c_3893,c_6681,c_22975,c_61817,c_103040,c_103042,c_106641,c_137098,c_161634,c_195210,c_226966])).

cnf(c_227337,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_227303,c_3893])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_8254,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1509])).

cnf(c_11704,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_8254])).

cnf(c_46143,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK4,X0),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3179,c_11704])).

cnf(c_48583,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k1_xboole_0) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46143,c_2543,c_2845])).

cnf(c_48584,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK4,X0),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_48583])).

cnf(c_2775,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1512])).

cnf(c_48596,plain,
    ( v4_relat_1(k7_relat_1(sK4,X0),X1) = iProver_top
    | r1_tarski(k9_relat_1(sK4,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_48584,c_2775])).

cnf(c_228006,plain,
    ( v4_relat_1(k7_relat_1(sK4,sK1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_227337,c_48596])).

cnf(c_228764,plain,
    ( v4_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_228006])).

cnf(c_684,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_125533,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,sK1,sK2)
    | X3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_125535,plain,
    ( v1_funct_2(k1_xboole_0,sK1,sK2)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | sK2 != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_125533])).

cnf(c_119440,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_104635,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_111618,plain,
    ( ~ v1_funct_2(X0,sK1,X1)
    | v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0
    | sK2 != X1
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_104635])).

cnf(c_113992,plain,
    ( ~ v1_funct_2(X0,sK1,sK2)
    | v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0
    | sK2 != sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_111618])).

cnf(c_113994,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ v1_funct_2(k1_xboole_0,sK1,sK2)
    | k2_partfun1(sK0,sK3,sK4,sK1) != k1_xboole_0
    | sK2 != sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_113992])).

cnf(c_4123,plain,
    ( X0 != X1
    | k2_partfun1(sK0,sK3,sK4,X2) != X1
    | k2_partfun1(sK0,sK3,sK4,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_31314,plain,
    ( X0 != X1
    | k2_partfun1(sK0,sK3,sK4,sK1) != X1
    | k2_partfun1(sK0,sK3,sK4,sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_4123])).

cnf(c_91542,plain,
    ( X0 != k2_partfun1(sK0,sK3,sK4,X1)
    | k2_partfun1(sK0,sK3,sK4,sK1) = X0
    | k2_partfun1(sK0,sK3,sK4,sK1) != k2_partfun1(sK0,sK3,sK4,X1) ),
    inference(instantiation,[status(thm)],[c_31314])).

cnf(c_91544,plain,
    ( k2_partfun1(sK0,sK3,sK4,sK1) != k2_partfun1(sK0,sK3,sK4,k1_xboole_0)
    | k2_partfun1(sK0,sK3,sK4,sK1) = k1_xboole_0
    | k1_xboole_0 != k2_partfun1(sK0,sK3,sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_91542])).

cnf(c_685,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_partfun1(X0,X2,X4,X6) = k2_partfun1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_3093,plain,
    ( X0 != X1
    | X2 != sK4
    | X3 != sK3
    | X4 != sK0
    | k2_partfun1(X4,X3,X2,X0) = k2_partfun1(sK0,sK3,sK4,X1) ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_4221,plain,
    ( X0 != X1
    | X2 != sK3
    | X3 != sK0
    | k2_partfun1(X3,X2,sK4,X0) = k2_partfun1(sK0,sK3,sK4,X1)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3093])).

cnf(c_8747,plain,
    ( X0 != X1
    | X2 != sK3
    | k2_partfun1(sK0,X2,sK4,X0) = k2_partfun1(sK0,sK3,sK4,X1)
    | sK4 != sK4
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_4221])).

cnf(c_13299,plain,
    ( X0 != X1
    | k2_partfun1(sK0,sK3,sK4,X0) = k2_partfun1(sK0,sK3,sK4,X1)
    | sK4 != sK4
    | sK3 != sK3
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_8747])).

cnf(c_47711,plain,
    ( k2_partfun1(sK0,sK3,sK4,sK1) = k2_partfun1(sK0,sK3,sK4,X0)
    | sK1 != X0
    | sK4 != sK4
    | sK3 != sK3
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_13299])).

cnf(c_47712,plain,
    ( k2_partfun1(sK0,sK3,sK4,sK1) = k2_partfun1(sK0,sK3,sK4,k1_xboole_0)
    | sK1 != k1_xboole_0
    | sK4 != sK4
    | sK3 != sK3
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_47711])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1519,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1526,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4786,plain,
    ( k1_relat_1(X0) = X1
    | v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1519,c_1526])).

cnf(c_32176,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = X0
    | v4_relat_1(k7_relat_1(sK4,sK1),X0) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12253,c_4786])).

cnf(c_32315,plain,
    ( sK1 = X0
    | v4_relat_1(k7_relat_1(sK4,sK1),X0) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_32176,c_12253])).

cnf(c_32401,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_32315])).

cnf(c_674,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2031,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK1,sK2))
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0
    | k2_zfmisc_1(sK1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_2450,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK1,sK2))
    | k2_partfun1(sK0,sK3,sK4,sK1) != X0
    | k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_23127,plain,
    ( ~ r1_tarski(k2_partfun1(sK0,sK3,sK4,X0),k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK1,sK2))
    | k2_partfun1(sK0,sK3,sK4,sK1) != k2_partfun1(sK0,sK3,sK4,X0)
    | k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2450])).

cnf(c_23130,plain,
    ( r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK1,sK2))
    | ~ r1_tarski(k2_partfun1(sK0,sK3,sK4,k1_xboole_0),k2_zfmisc_1(sK1,sK2))
    | k2_partfun1(sK0,sK3,sK4,sK1) != k2_partfun1(sK0,sK3,sK4,k1_xboole_0)
    | k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_23127])).

cnf(c_18425,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_7278,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_18424,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_7278])).

cnf(c_2195,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | X2 != X0
    | k2_zfmisc_1(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_3509,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_zfmisc_1(sK1,sK2))
    | X2 != X0
    | k2_zfmisc_1(sK1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_2195])).

cnf(c_8117,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2))
    | r1_tarski(X1,k2_zfmisc_1(sK1,sK2))
    | X1 != X0
    | k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3509])).

cnf(c_15495,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k2_partfun1(sK0,sK3,sK4,X1),k2_zfmisc_1(sK1,sK2))
    | k2_partfun1(sK0,sK3,sK4,X1) != X0
    | k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_8117])).

cnf(c_15499,plain,
    ( r1_tarski(k2_partfun1(sK0,sK3,sK4,k1_xboole_0),k2_zfmisc_1(sK1,sK2))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK2))
    | k2_partfun1(sK0,sK3,sK4,k1_xboole_0) != k1_xboole_0
    | k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_15495])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1524,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_12251,plain,
    ( k1_relat_1(k7_relat_1(sK4,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1524,c_12243])).

cnf(c_33,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1499,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4258,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X0)),k9_relat_1(sK4,X0)))) = iProver_top
    | v1_funct_1(k7_relat_1(sK4,X0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3179,c_1499])).

cnf(c_5444,plain,
    ( v1_funct_1(k7_relat_1(sK4,X0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X0)),k9_relat_1(sK4,X0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4258,c_2543,c_2845])).

cnf(c_5445,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X0)),k9_relat_1(sK4,X0)))) = iProver_top
    | v1_funct_1(k7_relat_1(sK4,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5444])).

cnf(c_13618,plain,
    ( m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k9_relat_1(sK4,k1_xboole_0)))) = iProver_top
    | v1_funct_1(k7_relat_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12251,c_5445])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_13626,plain,
    ( m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k7_relat_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13618,c_6])).

cnf(c_13062,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(X1))
    | r1_tarski(k7_relat_1(sK4,X0),X1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_13063,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k7_relat_1(sK4,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13062])).

cnf(c_13065,plain,
    ( m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_13063])).

cnf(c_11771,plain,
    ( r1_tarski(k1_xboole_0,k7_relat_1(sK4,X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_11774,plain,
    ( r1_tarski(k1_xboole_0,k7_relat_1(sK4,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11771])).

cnf(c_11776,plain,
    ( r1_tarski(k1_xboole_0,k7_relat_1(sK4,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11774])).

cnf(c_8883,plain,
    ( v1_funct_1(k7_relat_1(sK4,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8867])).

cnf(c_8389,plain,
    ( X0 != k7_relat_1(sK4,X1)
    | k2_partfun1(sK0,sK3,sK4,X1) = X0
    | k2_partfun1(sK0,sK3,sK4,X1) != k7_relat_1(sK4,X1) ),
    inference(instantiation,[status(thm)],[c_4123])).

cnf(c_8390,plain,
    ( k2_partfun1(sK0,sK3,sK4,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | k2_partfun1(sK0,sK3,sK4,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8389])).

cnf(c_7729,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7732,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7729])).

cnf(c_7380,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X3,k1_relset_1(X1,X2,X0))
    | ~ r1_tarski(X4,k1_relat_1(X0))
    | X3 != X4 ),
    inference(resolution,[status(thm)],[c_674,c_21])).

cnf(c_7382,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | r1_tarski(k1_xboole_0,k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7380])).

cnf(c_5756,plain,
    ( ~ r1_tarski(X0,k7_relat_1(sK4,X1))
    | ~ r1_tarski(k7_relat_1(sK4,X1),X0)
    | X0 = k7_relat_1(sK4,X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5757,plain,
    ( X0 = k7_relat_1(sK4,X1)
    | r1_tarski(X0,k7_relat_1(sK4,X1)) != iProver_top
    | r1_tarski(k7_relat_1(sK4,X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5756])).

cnf(c_5759,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k7_relat_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5757])).

cnf(c_2700,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relset_1(k1_xboole_0,X2,X3),k1_xboole_0)
    | k1_relset_1(k1_xboole_0,X2,X3) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_4676,plain,
    ( r1_tarski(k1_relset_1(k1_xboole_0,X0,X1),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | k1_relset_1(k1_xboole_0,X0,X1) != k1_relat_1(X1)
    | k1_xboole_0 != X2 ),
    inference(instantiation,[status(thm)],[c_2700])).

cnf(c_4678,plain,
    ( r1_tarski(k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4676])).

cnf(c_4129,plain,
    ( k2_partfun1(sK0,sK3,sK4,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | k1_xboole_0 = k2_partfun1(sK0,sK3,sK4,k1_xboole_0)
    | k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4128])).

cnf(c_3855,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_2188,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3504,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2188])).

cnf(c_2573,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2577,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2573])).

cnf(c_2515,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) != iProver_top
    | r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1522,c_1497])).

cnf(c_2522,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK1,sK2))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2515])).

cnf(c_2451,plain,
    ( k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_2424,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2082,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2423,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2082])).

cnf(c_2408,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2075,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2407,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2075])).

cnf(c_2175,plain,
    ( ~ r1_tarski(k1_relset_1(k1_xboole_0,X0,X1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_relset_1(k1_xboole_0,X0,X1))
    | k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2177,plain,
    ( ~ r1_tarski(k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2175])).

cnf(c_1515,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2147,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1515])).

cnf(c_2149,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2147])).

cnf(c_2130,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_2110,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK0,sK3,sK4,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2108])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1881,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1885,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_1881])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1506,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1664,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1506,c_6])).

cnf(c_1757,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1664])).

cnf(c_1759,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1757])).

cnf(c_129,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_128,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_126,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_113,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_94,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_91,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_228764,c_226966,c_195210,c_161634,c_137098,c_125535,c_119440,c_113994,c_106641,c_103042,c_103040,c_91544,c_61817,c_47712,c_32401,c_23130,c_22975,c_18425,c_18424,c_15499,c_13626,c_13065,c_11776,c_8883,c_8390,c_7732,c_7382,c_6681,c_5759,c_4678,c_4129,c_3893,c_3855,c_3504,c_2577,c_2522,c_2451,c_2424,c_2423,c_2408,c_2407,c_2177,c_2149,c_2130,c_2110,c_1885,c_1759,c_129,c_128,c_126,c_113,c_94,c_91,c_46,c_39,c_44,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 59.38/8.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.38/8.00  
% 59.38/8.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.38/8.00  
% 59.38/8.00  ------  iProver source info
% 59.38/8.00  
% 59.38/8.00  git: date: 2020-06-30 10:37:57 +0100
% 59.38/8.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.38/8.00  git: non_committed_changes: false
% 59.38/8.00  git: last_make_outside_of_git: false
% 59.38/8.00  
% 59.38/8.00  ------ 
% 59.38/8.00  ------ Parsing...
% 59.38/8.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.38/8.00  
% 59.38/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 59.38/8.00  
% 59.38/8.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.38/8.00  
% 59.38/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.38/8.00  ------ Proving...
% 59.38/8.00  ------ Problem Properties 
% 59.38/8.00  
% 59.38/8.00  
% 59.38/8.00  clauses                                 41
% 59.38/8.00  conjectures                             7
% 59.38/8.00  EPR                                     9
% 59.38/8.00  Horn                                    36
% 59.38/8.00  unary                                   13
% 59.38/8.00  binary                                  6
% 59.38/8.00  lits                                    95
% 59.38/8.00  lits eq                                 20
% 59.38/8.00  fd_pure                                 0
% 59.38/8.00  fd_pseudo                               0
% 59.38/8.00  fd_cond                                 4
% 59.38/8.00  fd_pseudo_cond                          1
% 59.38/8.00  AC symbols                              0
% 59.38/8.00  
% 59.38/8.00  ------ Input Options Time Limit: Unbounded
% 59.38/8.00  
% 59.38/8.00  
% 59.38/8.00  ------ 
% 59.38/8.00  Current options:
% 59.38/8.00  ------ 
% 59.38/8.00  
% 59.38/8.00  
% 59.38/8.00  
% 59.38/8.00  
% 59.38/8.00  ------ Proving...
% 59.38/8.00  
% 59.38/8.00  
% 59.38/8.00  % SZS status Theorem for theBenchmark.p
% 59.38/8.00  
% 59.38/8.00  % SZS output start CNFRefutation for theBenchmark.p
% 59.38/8.00  
% 59.38/8.00  fof(f6,axiom,(
% 59.38/8.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f52,plain,(
% 59.38/8.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 59.38/8.00    inference(nnf_transformation,[],[f6])).
% 59.38/8.00  
% 59.38/8.00  fof(f68,plain,(
% 59.38/8.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 59.38/8.00    inference(cnf_transformation,[],[f52])).
% 59.38/8.00  
% 59.38/8.00  fof(f22,conjecture,(
% 59.38/8.00    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f23,negated_conjecture,(
% 59.38/8.00    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 59.38/8.00    inference(negated_conjecture,[],[f22])).
% 59.38/8.00  
% 59.38/8.00  fof(f46,plain,(
% 59.38/8.00    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 59.38/8.00    inference(ennf_transformation,[],[f23])).
% 59.38/8.00  
% 59.38/8.00  fof(f47,plain,(
% 59.38/8.00    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 59.38/8.00    inference(flattening,[],[f46])).
% 59.38/8.00  
% 59.38/8.00  fof(f56,plain,(
% 59.38/8.00    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(X0,X3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,sK4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,sK4,X1))) & r1_tarski(k7_relset_1(X0,X3,sK4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(sK4,X0,X3) & v1_funct_1(sK4))) )),
% 59.38/8.00    introduced(choice_axiom,[])).
% 59.38/8.00  
% 59.38/8.00  fof(f55,plain,(
% 59.38/8.00    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK0,sK3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,X4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,X4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,X4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(X4,sK0,sK3) & v1_funct_1(X4)) & ~v1_xboole_0(sK3))),
% 59.38/8.00    introduced(choice_axiom,[])).
% 59.38/8.00  
% 59.38/8.00  fof(f57,plain,(
% 59.38/8.00    ((~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))) & r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) & r1_tarski(sK1,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) & v1_funct_2(sK4,sK0,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 59.38/8.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f47,f56,f55])).
% 59.38/8.00  
% 59.38/8.00  fof(f97,plain,(
% 59.38/8.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 59.38/8.00    inference(cnf_transformation,[],[f57])).
% 59.38/8.00  
% 59.38/8.00  fof(f16,axiom,(
% 59.38/8.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f35,plain,(
% 59.38/8.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.38/8.00    inference(ennf_transformation,[],[f16])).
% 59.38/8.00  
% 59.38/8.00  fof(f80,plain,(
% 59.38/8.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.38/8.00    inference(cnf_transformation,[],[f35])).
% 59.38/8.00  
% 59.38/8.00  fof(f99,plain,(
% 59.38/8.00    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 59.38/8.00    inference(cnf_transformation,[],[f57])).
% 59.38/8.00  
% 59.38/8.00  fof(f2,axiom,(
% 59.38/8.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f48,plain,(
% 59.38/8.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 59.38/8.00    inference(nnf_transformation,[],[f2])).
% 59.38/8.00  
% 59.38/8.00  fof(f49,plain,(
% 59.38/8.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 59.38/8.00    inference(flattening,[],[f48])).
% 59.38/8.00  
% 59.38/8.00  fof(f59,plain,(
% 59.38/8.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 59.38/8.00    inference(cnf_transformation,[],[f49])).
% 59.38/8.00  
% 59.38/8.00  fof(f102,plain,(
% 59.38/8.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 59.38/8.00    inference(equality_resolution,[],[f59])).
% 59.38/8.00  
% 59.38/8.00  fof(f67,plain,(
% 59.38/8.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 59.38/8.00    inference(cnf_transformation,[],[f52])).
% 59.38/8.00  
% 59.38/8.00  fof(f8,axiom,(
% 59.38/8.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f26,plain,(
% 59.38/8.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 59.38/8.00    inference(ennf_transformation,[],[f8])).
% 59.38/8.00  
% 59.38/8.00  fof(f69,plain,(
% 59.38/8.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 59.38/8.00    inference(cnf_transformation,[],[f26])).
% 59.38/8.00  
% 59.38/8.00  fof(f11,axiom,(
% 59.38/8.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f75,plain,(
% 59.38/8.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 59.38/8.00    inference(cnf_transformation,[],[f11])).
% 59.38/8.00  
% 59.38/8.00  fof(f12,axiom,(
% 59.38/8.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f30,plain,(
% 59.38/8.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 59.38/8.00    inference(ennf_transformation,[],[f12])).
% 59.38/8.00  
% 59.38/8.00  fof(f76,plain,(
% 59.38/8.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 59.38/8.00    inference(cnf_transformation,[],[f30])).
% 59.38/8.00  
% 59.38/8.00  fof(f17,axiom,(
% 59.38/8.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f36,plain,(
% 59.38/8.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 59.38/8.00    inference(ennf_transformation,[],[f17])).
% 59.38/8.00  
% 59.38/8.00  fof(f37,plain,(
% 59.38/8.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 59.38/8.00    inference(flattening,[],[f36])).
% 59.38/8.00  
% 59.38/8.00  fof(f81,plain,(
% 59.38/8.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 59.38/8.00    inference(cnf_transformation,[],[f37])).
% 59.38/8.00  
% 59.38/8.00  fof(f15,axiom,(
% 59.38/8.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f34,plain,(
% 59.38/8.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.38/8.00    inference(ennf_transformation,[],[f15])).
% 59.38/8.00  
% 59.38/8.00  fof(f79,plain,(
% 59.38/8.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.38/8.00    inference(cnf_transformation,[],[f34])).
% 59.38/8.00  
% 59.38/8.00  fof(f14,axiom,(
% 59.38/8.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f24,plain,(
% 59.38/8.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 59.38/8.00    inference(pure_predicate_removal,[],[f14])).
% 59.38/8.00  
% 59.38/8.00  fof(f33,plain,(
% 59.38/8.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.38/8.00    inference(ennf_transformation,[],[f24])).
% 59.38/8.00  
% 59.38/8.00  fof(f78,plain,(
% 59.38/8.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.38/8.00    inference(cnf_transformation,[],[f33])).
% 59.38/8.00  
% 59.38/8.00  fof(f10,axiom,(
% 59.38/8.00    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f28,plain,(
% 59.38/8.00    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 59.38/8.00    inference(ennf_transformation,[],[f10])).
% 59.38/8.00  
% 59.38/8.00  fof(f29,plain,(
% 59.38/8.00    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 59.38/8.00    inference(flattening,[],[f28])).
% 59.38/8.00  
% 59.38/8.00  fof(f72,plain,(
% 59.38/8.00    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 59.38/8.00    inference(cnf_transformation,[],[f29])).
% 59.38/8.00  
% 59.38/8.00  fof(f98,plain,(
% 59.38/8.00    r1_tarski(sK1,sK0)),
% 59.38/8.00    inference(cnf_transformation,[],[f57])).
% 59.38/8.00  
% 59.38/8.00  fof(f18,axiom,(
% 59.38/8.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f38,plain,(
% 59.38/8.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.38/8.00    inference(ennf_transformation,[],[f18])).
% 59.38/8.00  
% 59.38/8.00  fof(f39,plain,(
% 59.38/8.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.38/8.00    inference(flattening,[],[f38])).
% 59.38/8.00  
% 59.38/8.00  fof(f54,plain,(
% 59.38/8.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.38/8.00    inference(nnf_transformation,[],[f39])).
% 59.38/8.00  
% 59.38/8.00  fof(f82,plain,(
% 59.38/8.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.38/8.00    inference(cnf_transformation,[],[f54])).
% 59.38/8.00  
% 59.38/8.00  fof(f94,plain,(
% 59.38/8.00    ~v1_xboole_0(sK3)),
% 59.38/8.00    inference(cnf_transformation,[],[f57])).
% 59.38/8.00  
% 59.38/8.00  fof(f96,plain,(
% 59.38/8.00    v1_funct_2(sK4,sK0,sK3)),
% 59.38/8.00    inference(cnf_transformation,[],[f57])).
% 59.38/8.00  
% 59.38/8.00  fof(f1,axiom,(
% 59.38/8.00    v1_xboole_0(k1_xboole_0)),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f58,plain,(
% 59.38/8.00    v1_xboole_0(k1_xboole_0)),
% 59.38/8.00    inference(cnf_transformation,[],[f1])).
% 59.38/8.00  
% 59.38/8.00  fof(f13,axiom,(
% 59.38/8.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f31,plain,(
% 59.38/8.00    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 59.38/8.00    inference(ennf_transformation,[],[f13])).
% 59.38/8.00  
% 59.38/8.00  fof(f32,plain,(
% 59.38/8.00    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 59.38/8.00    inference(flattening,[],[f31])).
% 59.38/8.00  
% 59.38/8.00  fof(f77,plain,(
% 59.38/8.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 59.38/8.00    inference(cnf_transformation,[],[f32])).
% 59.38/8.00  
% 59.38/8.00  fof(f84,plain,(
% 59.38/8.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.38/8.00    inference(cnf_transformation,[],[f54])).
% 59.38/8.00  
% 59.38/8.00  fof(f100,plain,(
% 59.38/8.00    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 59.38/8.00    inference(cnf_transformation,[],[f57])).
% 59.38/8.00  
% 59.38/8.00  fof(f20,axiom,(
% 59.38/8.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f42,plain,(
% 59.38/8.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 59.38/8.00    inference(ennf_transformation,[],[f20])).
% 59.38/8.00  
% 59.38/8.00  fof(f43,plain,(
% 59.38/8.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 59.38/8.00    inference(flattening,[],[f42])).
% 59.38/8.00  
% 59.38/8.00  fof(f90,plain,(
% 59.38/8.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 59.38/8.00    inference(cnf_transformation,[],[f43])).
% 59.38/8.00  
% 59.38/8.00  fof(f95,plain,(
% 59.38/8.00    v1_funct_1(sK4)),
% 59.38/8.00    inference(cnf_transformation,[],[f57])).
% 59.38/8.00  
% 59.38/8.00  fof(f19,axiom,(
% 59.38/8.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f40,plain,(
% 59.38/8.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 59.38/8.00    inference(ennf_transformation,[],[f19])).
% 59.38/8.00  
% 59.38/8.00  fof(f41,plain,(
% 59.38/8.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 59.38/8.00    inference(flattening,[],[f40])).
% 59.38/8.00  
% 59.38/8.00  fof(f88,plain,(
% 59.38/8.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 59.38/8.00    inference(cnf_transformation,[],[f41])).
% 59.38/8.00  
% 59.38/8.00  fof(f89,plain,(
% 59.38/8.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 59.38/8.00    inference(cnf_transformation,[],[f41])).
% 59.38/8.00  
% 59.38/8.00  fof(f4,axiom,(
% 59.38/8.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f50,plain,(
% 59.38/8.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 59.38/8.00    inference(nnf_transformation,[],[f4])).
% 59.38/8.00  
% 59.38/8.00  fof(f51,plain,(
% 59.38/8.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 59.38/8.00    inference(flattening,[],[f50])).
% 59.38/8.00  
% 59.38/8.00  fof(f65,plain,(
% 59.38/8.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 59.38/8.00    inference(cnf_transformation,[],[f51])).
% 59.38/8.00  
% 59.38/8.00  fof(f103,plain,(
% 59.38/8.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 59.38/8.00    inference(equality_resolution,[],[f65])).
% 59.38/8.00  
% 59.38/8.00  fof(f9,axiom,(
% 59.38/8.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f27,plain,(
% 59.38/8.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 59.38/8.00    inference(ennf_transformation,[],[f9])).
% 59.38/8.00  
% 59.38/8.00  fof(f53,plain,(
% 59.38/8.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 59.38/8.00    inference(nnf_transformation,[],[f27])).
% 59.38/8.00  
% 59.38/8.00  fof(f70,plain,(
% 59.38/8.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 59.38/8.00    inference(cnf_transformation,[],[f53])).
% 59.38/8.00  
% 59.38/8.00  fof(f61,plain,(
% 59.38/8.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 59.38/8.00    inference(cnf_transformation,[],[f49])).
% 59.38/8.00  
% 59.38/8.00  fof(f3,axiom,(
% 59.38/8.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f62,plain,(
% 59.38/8.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 59.38/8.00    inference(cnf_transformation,[],[f3])).
% 59.38/8.00  
% 59.38/8.00  fof(f21,axiom,(
% 59.38/8.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f44,plain,(
% 59.38/8.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 59.38/8.00    inference(ennf_transformation,[],[f21])).
% 59.38/8.00  
% 59.38/8.00  fof(f45,plain,(
% 59.38/8.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 59.38/8.00    inference(flattening,[],[f44])).
% 59.38/8.00  
% 59.38/8.00  fof(f93,plain,(
% 59.38/8.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 59.38/8.00    inference(cnf_transformation,[],[f45])).
% 59.38/8.00  
% 59.38/8.00  fof(f64,plain,(
% 59.38/8.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 59.38/8.00    inference(cnf_transformation,[],[f51])).
% 59.38/8.00  
% 59.38/8.00  fof(f104,plain,(
% 59.38/8.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 59.38/8.00    inference(equality_resolution,[],[f64])).
% 59.38/8.00  
% 59.38/8.00  fof(f5,axiom,(
% 59.38/8.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 59.38/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.38/8.00  
% 59.38/8.00  fof(f66,plain,(
% 59.38/8.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 59.38/8.00    inference(cnf_transformation,[],[f5])).
% 59.38/8.00  
% 59.38/8.00  fof(f85,plain,(
% 59.38/8.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.38/8.00    inference(cnf_transformation,[],[f54])).
% 59.38/8.00  
% 59.38/8.00  fof(f108,plain,(
% 59.38/8.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 59.38/8.00    inference(equality_resolution,[],[f85])).
% 59.38/8.00  
% 59.38/8.00  fof(f63,plain,(
% 59.38/8.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 59.38/8.00    inference(cnf_transformation,[],[f51])).
% 59.38/8.00  
% 59.38/8.00  cnf(c_9,plain,
% 59.38/8.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 59.38/8.00      inference(cnf_transformation,[],[f68]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1522,plain,
% 59.38/8.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 59.38/8.00      | r1_tarski(X0,X1) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_39,negated_conjecture,
% 59.38/8.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
% 59.38/8.00      inference(cnf_transformation,[],[f97]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1494,plain,
% 59.38/8.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_22,plain,
% 59.38/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.38/8.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 59.38/8.00      inference(cnf_transformation,[],[f80]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1510,plain,
% 59.38/8.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 59.38/8.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_3751,plain,
% 59.38/8.00      ( k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1494,c_1510]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_37,negated_conjecture,
% 59.38/8.00      ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
% 59.38/8.00      inference(cnf_transformation,[],[f99]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1496,plain,
% 59.38/8.00      ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_3893,plain,
% 59.38/8.00      ( r1_tarski(k9_relat_1(sK4,sK1),sK2) = iProver_top ),
% 59.38/8.00      inference(demodulation,[status(thm)],[c_3751,c_1496]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_3,plain,
% 59.38/8.00      ( r1_tarski(X0,X0) ),
% 59.38/8.00      inference(cnf_transformation,[],[f102]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1525,plain,
% 59.38/8.00      ( r1_tarski(X0,X0) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_10,plain,
% 59.38/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 59.38/8.00      inference(cnf_transformation,[],[f67]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1521,plain,
% 59.38/8.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 59.38/8.00      | r1_tarski(X0,X1) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2368,plain,
% 59.38/8.00      ( r1_tarski(sK4,k2_zfmisc_1(sK0,sK3)) = iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1494,c_1521]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_11,plain,
% 59.38/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 59.38/8.00      | ~ v1_relat_1(X1)
% 59.38/8.00      | v1_relat_1(X0) ),
% 59.38/8.00      inference(cnf_transformation,[],[f69]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_265,plain,
% 59.38/8.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 59.38/8.00      inference(prop_impl,[status(thm)],[c_9]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_266,plain,
% 59.38/8.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 59.38/8.00      inference(renaming,[status(thm)],[c_265]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_332,plain,
% 59.38/8.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 59.38/8.00      inference(bin_hyper_res,[status(thm)],[c_11,c_266]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1490,plain,
% 59.38/8.00      ( r1_tarski(X0,X1) != iProver_top
% 59.38/8.00      | v1_relat_1(X1) != iProver_top
% 59.38/8.00      | v1_relat_1(X0) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2608,plain,
% 59.38/8.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top
% 59.38/8.00      | v1_relat_1(sK4) = iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_2368,c_1490]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2007,plain,
% 59.38/8.00      ( r1_tarski(sK4,k2_zfmisc_1(sK0,sK3)) ),
% 59.38/8.00      inference(resolution,[status(thm)],[c_10,c_39]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2400,plain,
% 59.38/8.00      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) | v1_relat_1(sK4) ),
% 59.38/8.00      inference(resolution,[status(thm)],[c_332,c_2007]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_17,plain,
% 59.38/8.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 59.38/8.00      inference(cnf_transformation,[],[f75]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2542,plain,
% 59.38/8.00      ( v1_relat_1(sK4) ),
% 59.38/8.00      inference(forward_subsumption_resolution,
% 59.38/8.00                [status(thm)],
% 59.38/8.00                [c_2400,c_17]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2543,plain,
% 59.38/8.00      ( v1_relat_1(sK4) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_2542]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_3174,plain,
% 59.38/8.00      ( v1_relat_1(sK4) = iProver_top ),
% 59.38/8.00      inference(global_propositional_subsumption,
% 59.38/8.00                [status(thm)],
% 59.38/8.00                [c_2608,c_2543]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_18,plain,
% 59.38/8.00      ( ~ v1_relat_1(X0)
% 59.38/8.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 59.38/8.00      inference(cnf_transformation,[],[f76]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1514,plain,
% 59.38/8.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 59.38/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_3179,plain,
% 59.38/8.00      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_3174,c_1514]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_23,plain,
% 59.38/8.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.38/8.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 59.38/8.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 59.38/8.00      | ~ v1_relat_1(X0) ),
% 59.38/8.00      inference(cnf_transformation,[],[f81]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1509,plain,
% 59.38/8.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 59.38/8.00      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 59.38/8.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 59.38/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_21,plain,
% 59.38/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.38/8.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 59.38/8.00      inference(cnf_transformation,[],[f79]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1511,plain,
% 59.38/8.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 59.38/8.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_8258,plain,
% 59.38/8.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 59.38/8.00      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 59.38/8.00      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 59.38/8.00      | v1_relat_1(X2) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1509,c_1511]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_195757,plain,
% 59.38/8.00      ( k1_relset_1(X0,X1,k7_relat_1(sK4,X2)) = k1_relat_1(k7_relat_1(sK4,X2))
% 59.38/8.00      | r1_tarski(k9_relat_1(sK4,X2),X1) != iProver_top
% 59.38/8.00      | r1_tarski(k1_relat_1(k7_relat_1(sK4,X2)),X0) != iProver_top
% 59.38/8.00      | v1_relat_1(k7_relat_1(sK4,X2)) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_3179,c_8258]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_20,plain,
% 59.38/8.00      ( v4_relat_1(X0,X1)
% 59.38/8.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 59.38/8.00      inference(cnf_transformation,[],[f78]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1512,plain,
% 59.38/8.00      ( v4_relat_1(X0,X1) = iProver_top
% 59.38/8.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2774,plain,
% 59.38/8.00      ( v4_relat_1(sK4,sK0) = iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1494,c_1512]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_16,plain,
% 59.38/8.00      ( ~ v4_relat_1(X0,X1)
% 59.38/8.00      | ~ v1_relat_1(X0)
% 59.38/8.00      | v1_relat_1(k7_relat_1(X0,X2)) ),
% 59.38/8.00      inference(cnf_transformation,[],[f72]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1516,plain,
% 59.38/8.00      ( v4_relat_1(X0,X1) != iProver_top
% 59.38/8.00      | v1_relat_1(X0) != iProver_top
% 59.38/8.00      | v1_relat_1(k7_relat_1(X0,X2)) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_4769,plain,
% 59.38/8.00      ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top
% 59.38/8.00      | v1_relat_1(sK4) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_2774,c_1516]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2021,plain,
% 59.38/8.00      ( v4_relat_1(sK4,sK0) ),
% 59.38/8.00      inference(resolution,[status(thm)],[c_20,c_39]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2844,plain,
% 59.38/8.00      ( v1_relat_1(k7_relat_1(sK4,X0)) | ~ v1_relat_1(sK4) ),
% 59.38/8.00      inference(resolution,[status(thm)],[c_16,c_2021]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2845,plain,
% 59.38/8.00      ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top
% 59.38/8.00      | v1_relat_1(sK4) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_2844]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_5073,plain,
% 59.38/8.00      ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top ),
% 59.38/8.00      inference(global_propositional_subsumption,
% 59.38/8.00                [status(thm)],
% 59.38/8.00                [c_4769,c_2543,c_2845]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_225512,plain,
% 59.38/8.00      ( k1_relset_1(X0,X1,k7_relat_1(sK4,X2)) = k1_relat_1(k7_relat_1(sK4,X2))
% 59.38/8.00      | r1_tarski(k9_relat_1(sK4,X2),X1) != iProver_top
% 59.38/8.00      | r1_tarski(k1_relat_1(k7_relat_1(sK4,X2)),X0) != iProver_top ),
% 59.38/8.00      inference(forward_subsumption_resolution,
% 59.38/8.00                [status(thm)],
% 59.38/8.00                [c_195757,c_5073]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_225516,plain,
% 59.38/8.00      ( k1_relset_1(k1_relat_1(k7_relat_1(sK4,X0)),X1,k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0))
% 59.38/8.00      | r1_tarski(k9_relat_1(sK4,X0),X1) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1525,c_225512]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_225851,plain,
% 59.38/8.00      ( k1_relset_1(k1_relat_1(k7_relat_1(sK4,sK1)),sK2,k7_relat_1(sK4,sK1)) = k1_relat_1(k7_relat_1(sK4,sK1)) ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_3893,c_225516]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_38,negated_conjecture,
% 59.38/8.00      ( r1_tarski(sK1,sK0) ),
% 59.38/8.00      inference(cnf_transformation,[],[f98]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1495,plain,
% 59.38/8.00      ( r1_tarski(sK1,sK0) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_29,plain,
% 59.38/8.00      ( ~ v1_funct_2(X0,X1,X2)
% 59.38/8.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.38/8.00      | k1_relset_1(X1,X2,X0) = X1
% 59.38/8.00      | k1_xboole_0 = X2 ),
% 59.38/8.00      inference(cnf_transformation,[],[f82]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1503,plain,
% 59.38/8.00      ( k1_relset_1(X0,X1,X2) = X0
% 59.38/8.00      | k1_xboole_0 = X1
% 59.38/8.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 59.38/8.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_10004,plain,
% 59.38/8.00      ( k1_relset_1(sK0,sK3,sK4) = sK0
% 59.38/8.00      | sK3 = k1_xboole_0
% 59.38/8.00      | v1_funct_2(sK4,sK0,sK3) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1494,c_1503]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2952,plain,
% 59.38/8.00      ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1494,c_1511]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_10032,plain,
% 59.38/8.00      ( k1_relat_1(sK4) = sK0
% 59.38/8.00      | sK3 = k1_xboole_0
% 59.38/8.00      | v1_funct_2(sK4,sK0,sK3) != iProver_top ),
% 59.38/8.00      inference(demodulation,[status(thm)],[c_10004,c_2952]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_42,negated_conjecture,
% 59.38/8.00      ( ~ v1_xboole_0(sK3) ),
% 59.38/8.00      inference(cnf_transformation,[],[f94]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_40,negated_conjecture,
% 59.38/8.00      ( v1_funct_2(sK4,sK0,sK3) ),
% 59.38/8.00      inference(cnf_transformation,[],[f96]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_45,plain,
% 59.38/8.00      ( v1_funct_2(sK4,sK0,sK3) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_0,plain,
% 59.38/8.00      ( v1_xboole_0(k1_xboole_0) ),
% 59.38/8.00      inference(cnf_transformation,[],[f58]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_673,plain,
% 59.38/8.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 59.38/8.00      theory(equality) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1845,plain,
% 59.38/8.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_673]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1847,plain,
% 59.38/8.00      ( v1_xboole_0(sK3)
% 59.38/8.00      | ~ v1_xboole_0(k1_xboole_0)
% 59.38/8.00      | sK3 != k1_xboole_0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_1845]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_10437,plain,
% 59.38/8.00      ( k1_relat_1(sK4) = sK0 ),
% 59.38/8.00      inference(global_propositional_subsumption,
% 59.38/8.00                [status(thm)],
% 59.38/8.00                [c_10032,c_42,c_45,c_0,c_1847]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_19,plain,
% 59.38/8.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 59.38/8.00      | ~ v1_relat_1(X1)
% 59.38/8.00      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 59.38/8.00      inference(cnf_transformation,[],[f77]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1513,plain,
% 59.38/8.00      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 59.38/8.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 59.38/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_10441,plain,
% 59.38/8.00      ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
% 59.38/8.00      | r1_tarski(X0,sK0) != iProver_top
% 59.38/8.00      | v1_relat_1(sK4) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_10437,c_1513]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_12242,plain,
% 59.38/8.00      ( r1_tarski(X0,sK0) != iProver_top
% 59.38/8.00      | k1_relat_1(k7_relat_1(sK4,X0)) = X0 ),
% 59.38/8.00      inference(global_propositional_subsumption,
% 59.38/8.00                [status(thm)],
% 59.38/8.00                [c_10441,c_2543]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_12243,plain,
% 59.38/8.00      ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
% 59.38/8.00      | r1_tarski(X0,sK0) != iProver_top ),
% 59.38/8.00      inference(renaming,[status(thm)],[c_12242]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_12253,plain,
% 59.38/8.00      ( k1_relat_1(k7_relat_1(sK4,sK1)) = sK1 ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1495,c_12243]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_225857,plain,
% 59.38/8.00      ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) = sK1 ),
% 59.38/8.00      inference(light_normalisation,[status(thm)],[c_225851,c_12253]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_27,plain,
% 59.38/8.00      ( v1_funct_2(X0,X1,X2)
% 59.38/8.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.38/8.00      | k1_relset_1(X1,X2,X0) != X1
% 59.38/8.00      | k1_xboole_0 = X2 ),
% 59.38/8.00      inference(cnf_transformation,[],[f84]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1505,plain,
% 59.38/8.00      ( k1_relset_1(X0,X1,X2) != X0
% 59.38/8.00      | k1_xboole_0 = X1
% 59.38/8.00      | v1_funct_2(X2,X0,X1) = iProver_top
% 59.38/8.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_226126,plain,
% 59.38/8.00      ( sK2 = k1_xboole_0
% 59.38/8.00      | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) = iProver_top
% 59.38/8.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_225857,c_1505]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_36,negated_conjecture,
% 59.38/8.00      ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
% 59.38/8.00      | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 59.38/8.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
% 59.38/8.00      inference(cnf_transformation,[],[f100]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1497,plain,
% 59.38/8.00      ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) != iProver_top
% 59.38/8.00      | m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 59.38/8.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_8261,plain,
% 59.38/8.00      ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) != iProver_top
% 59.38/8.00      | r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) != iProver_top
% 59.38/8.00      | r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1) != iProver_top
% 59.38/8.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
% 59.38/8.00      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1509,c_1497]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_32,plain,
% 59.38/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.38/8.00      | ~ v1_funct_1(X0)
% 59.38/8.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 59.38/8.00      inference(cnf_transformation,[],[f90]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1500,plain,
% 59.38/8.00      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 59.38/8.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.38/8.00      | v1_funct_1(X2) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_8773,plain,
% 59.38/8.00      ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
% 59.38/8.00      | v1_funct_1(sK4) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1494,c_1500]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_41,negated_conjecture,
% 59.38/8.00      ( v1_funct_1(sK4) ),
% 59.38/8.00      inference(cnf_transformation,[],[f95]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1985,plain,
% 59.38/8.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 59.38/8.00      | ~ v1_funct_1(sK4)
% 59.38/8.00      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_32]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2108,plain,
% 59.38/8.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 59.38/8.00      | ~ v1_funct_1(sK4)
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_1985]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_8861,plain,
% 59.38/8.00      ( k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
% 59.38/8.00      inference(global_propositional_subsumption,
% 59.38/8.00                [status(thm)],
% 59.38/8.00                [c_8773,c_41,c_39,c_2108]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_9055,plain,
% 59.38/8.00      ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) != iProver_top
% 59.38/8.00      | r1_tarski(k9_relat_1(sK4,sK1),sK2) != iProver_top
% 59.38/8.00      | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
% 59.38/8.00      | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top
% 59.38/8.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 59.38/8.00      inference(demodulation,[status(thm)],[c_8261,c_3179,c_8861]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_9061,plain,
% 59.38/8.00      ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) != iProver_top
% 59.38/8.00      | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
% 59.38/8.00      | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 59.38/8.00      inference(forward_subsumption_resolution,
% 59.38/8.00                [status(thm)],
% 59.38/8.00                [c_9055,c_5073,c_3893]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_12270,plain,
% 59.38/8.00      ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) != iProver_top
% 59.38/8.00      | r1_tarski(sK1,sK1) != iProver_top
% 59.38/8.00      | v1_funct_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 59.38/8.00      inference(demodulation,[status(thm)],[c_12253,c_9061]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_31,plain,
% 59.38/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.38/8.00      | ~ v1_funct_1(X0)
% 59.38/8.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 59.38/8.00      inference(cnf_transformation,[],[f88]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1501,plain,
% 59.38/8.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 59.38/8.00      | v1_funct_1(X0) != iProver_top
% 59.38/8.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_5962,plain,
% 59.38/8.00      ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top
% 59.38/8.00      | v1_funct_1(sK4) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1494,c_1501]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_44,plain,
% 59.38/8.00      ( v1_funct_1(sK4) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_46,plain,
% 59.38/8.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1942,plain,
% 59.38/8.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 59.38/8.00      | v1_funct_1(k2_partfun1(X0,X1,sK4,X2))
% 59.38/8.00      | ~ v1_funct_1(sK4) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_31]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2102,plain,
% 59.38/8.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 59.38/8.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))
% 59.38/8.00      | ~ v1_funct_1(sK4) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_1942]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2103,plain,
% 59.38/8.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 59.38/8.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top
% 59.38/8.00      | v1_funct_1(sK4) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_2102]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_6402,plain,
% 59.38/8.00      ( v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) = iProver_top ),
% 59.38/8.00      inference(global_propositional_subsumption,
% 59.38/8.00                [status(thm)],
% 59.38/8.00                [c_5962,c_44,c_46,c_2103]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_8867,plain,
% 59.38/8.00      ( v1_funct_1(k7_relat_1(sK4,X0)) = iProver_top ),
% 59.38/8.00      inference(demodulation,[status(thm)],[c_8861,c_6402]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_14582,plain,
% 59.38/8.00      ( v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) != iProver_top ),
% 59.38/8.00      inference(forward_subsumption_resolution,
% 59.38/8.00                [status(thm)],
% 59.38/8.00                [c_12270,c_8867,c_1525]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_226953,plain,
% 59.38/8.00      ( sK2 = k1_xboole_0
% 59.38/8.00      | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 59.38/8.00      inference(global_propositional_subsumption,
% 59.38/8.00                [status(thm)],
% 59.38/8.00                [c_226126,c_14582]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_226959,plain,
% 59.38/8.00      ( sK2 = k1_xboole_0
% 59.38/8.00      | r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2)) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1522,c_226953]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_6681,plain,
% 59.38/8.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 59.38/8.00      | ~ v1_funct_1(sK4)
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,sK1) = k7_relat_1(sK4,sK1) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_2108]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_672,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_3090,plain,
% 59.38/8.00      ( X0 != X1
% 59.38/8.00      | X0 = k2_partfun1(sK0,sK3,sK4,X2)
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,X2) != X1 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_672]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_4128,plain,
% 59.38/8.00      ( X0 = k2_partfun1(sK0,sK3,sK4,X1)
% 59.38/8.00      | X0 != k7_relat_1(sK4,X1)
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,X1) != k7_relat_1(sK4,X1) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_3090]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_5781,plain,
% 59.38/8.00      ( k2_partfun1(sK0,sK3,sK4,X0) != k7_relat_1(sK4,X0)
% 59.38/8.00      | k7_relat_1(sK4,X0) = k2_partfun1(sK0,sK3,sK4,X0)
% 59.38/8.00      | k7_relat_1(sK4,X0) != k7_relat_1(sK4,X0) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_4128]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_22975,plain,
% 59.38/8.00      ( k2_partfun1(sK0,sK3,sK4,sK1) != k7_relat_1(sK4,sK1)
% 59.38/8.00      | k7_relat_1(sK4,sK1) = k2_partfun1(sK0,sK3,sK4,sK1)
% 59.38/8.00      | k7_relat_1(sK4,sK1) != k7_relat_1(sK4,sK1) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_5781]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_671,plain,( X0 = X0 ),theory(equality) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_5782,plain,
% 59.38/8.00      ( k7_relat_1(sK4,X0) = k7_relat_1(sK4,X0) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_671]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_61817,plain,
% 59.38/8.00      ( k7_relat_1(sK4,sK1) = k7_relat_1(sK4,sK1) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_5782]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_101584,plain,
% 59.38/8.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(X0))
% 59.38/8.00      | r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),X0) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_10]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_103038,plain,
% 59.38/8.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 59.38/8.00      | r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK0,sK3)) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_101584]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_103040,plain,
% 59.38/8.00      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 59.38/8.00      | r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK0,sK3)) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_103038]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_30,plain,
% 59.38/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.38/8.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.38/8.00      | ~ v1_funct_1(X0) ),
% 59.38/8.00      inference(cnf_transformation,[],[f89]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_103039,plain,
% 59.38/8.00      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 59.38/8.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 59.38/8.00      | ~ v1_funct_1(sK4) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_30]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_103042,plain,
% 59.38/8.00      ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) = iProver_top
% 59.38/8.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) != iProver_top
% 59.38/8.00      | v1_funct_1(sK4) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_103039]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_106636,plain,
% 59.38/8.00      ( r1_tarski(sK1,sK1) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_3]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_106641,plain,
% 59.38/8.00      ( r1_tarski(sK1,sK1) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_106636]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_107712,plain,
% 59.38/8.00      ( ~ r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),X0)
% 59.38/8.00      | ~ v1_relat_1(X0)
% 59.38/8.00      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_332]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_137097,plain,
% 59.38/8.00      ( ~ r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK0,sK3))
% 59.38/8.00      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 59.38/8.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_107712]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_137098,plain,
% 59.38/8.00      ( r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK0,sK3)) != iProver_top
% 59.38/8.00      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) = iProver_top
% 59.38/8.00      | v1_relat_1(k2_zfmisc_1(sK0,sK3)) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_137097]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_678,plain,
% 59.38/8.00      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 59.38/8.00      theory(equality) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_126546,plain,
% 59.38/8.00      ( ~ v1_relat_1(X0)
% 59.38/8.00      | v1_relat_1(k7_relat_1(sK4,sK1))
% 59.38/8.00      | k7_relat_1(sK4,sK1) != X0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_678]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_161618,plain,
% 59.38/8.00      ( ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 59.38/8.00      | v1_relat_1(k7_relat_1(sK4,sK1))
% 59.38/8.00      | k7_relat_1(sK4,sK1) != k2_partfun1(sK0,sK3,sK4,sK1) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_126546]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_161634,plain,
% 59.38/8.00      ( k7_relat_1(sK4,sK1) != k2_partfun1(sK0,sK3,sK4,sK1)
% 59.38/8.00      | v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top
% 59.38/8.00      | v1_relat_1(k7_relat_1(sK4,sK1)) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_161618]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_195209,plain,
% 59.38/8.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_17]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_195210,plain,
% 59.38/8.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK3)) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_195209]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_226960,plain,
% 59.38/8.00      ( sK2 = k1_xboole_0
% 59.38/8.00      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
% 59.38/8.00      | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) != iProver_top
% 59.38/8.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1509,c_226953]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_226965,plain,
% 59.38/8.00      ( sK2 = k1_xboole_0
% 59.38/8.00      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) != iProver_top
% 59.38/8.00      | r1_tarski(sK1,sK1) != iProver_top
% 59.38/8.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 59.38/8.00      inference(light_normalisation,[status(thm)],[c_226960,c_12253]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_226966,plain,
% 59.38/8.00      ( sK2 = k1_xboole_0
% 59.38/8.00      | r1_tarski(k9_relat_1(sK4,sK1),sK2) != iProver_top
% 59.38/8.00      | r1_tarski(sK1,sK1) != iProver_top
% 59.38/8.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 59.38/8.00      inference(demodulation,[status(thm)],[c_226965,c_3179]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_227303,plain,
% 59.38/8.00      ( sK2 = k1_xboole_0 ),
% 59.38/8.00      inference(global_propositional_subsumption,
% 59.38/8.00                [status(thm)],
% 59.38/8.00                [c_226959,c_41,c_44,c_39,c_46,c_3893,c_6681,c_22975,
% 59.38/8.00                 c_61817,c_103040,c_103042,c_106641,c_137098,c_161634,
% 59.38/8.00                 c_195210,c_226966]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_227337,plain,
% 59.38/8.00      ( r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) = iProver_top ),
% 59.38/8.00      inference(demodulation,[status(thm)],[c_227303,c_3893]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_5,plain,
% 59.38/8.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 59.38/8.00      inference(cnf_transformation,[],[f103]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_8254,plain,
% 59.38/8.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 59.38/8.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 59.38/8.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 59.38/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_5,c_1509]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_11704,plain,
% 59.38/8.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 59.38/8.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 59.38/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1525,c_8254]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_46143,plain,
% 59.38/8.00      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 59.38/8.00      | r1_tarski(k9_relat_1(sK4,X0),k1_xboole_0) != iProver_top
% 59.38/8.00      | v1_relat_1(k7_relat_1(sK4,X0)) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_3179,c_11704]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_48583,plain,
% 59.38/8.00      ( r1_tarski(k9_relat_1(sK4,X0),k1_xboole_0) != iProver_top
% 59.38/8.00      | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 59.38/8.00      inference(global_propositional_subsumption,
% 59.38/8.00                [status(thm)],
% 59.38/8.00                [c_46143,c_2543,c_2845]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_48584,plain,
% 59.38/8.00      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 59.38/8.00      | r1_tarski(k9_relat_1(sK4,X0),k1_xboole_0) != iProver_top ),
% 59.38/8.00      inference(renaming,[status(thm)],[c_48583]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2775,plain,
% 59.38/8.00      ( v4_relat_1(X0,X1) = iProver_top
% 59.38/8.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_5,c_1512]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_48596,plain,
% 59.38/8.00      ( v4_relat_1(k7_relat_1(sK4,X0),X1) = iProver_top
% 59.38/8.00      | r1_tarski(k9_relat_1(sK4,X0),k1_xboole_0) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_48584,c_2775]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_228006,plain,
% 59.38/8.00      ( v4_relat_1(k7_relat_1(sK4,sK1),X0) = iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_227337,c_48596]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_228764,plain,
% 59.38/8.00      ( v4_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0) = iProver_top ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_228006]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_684,plain,
% 59.38/8.00      ( ~ v1_funct_2(X0,X1,X2)
% 59.38/8.00      | v1_funct_2(X3,X4,X5)
% 59.38/8.00      | X3 != X0
% 59.38/8.00      | X4 != X1
% 59.38/8.00      | X5 != X2 ),
% 59.38/8.00      theory(equality) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_125533,plain,
% 59.38/8.00      ( ~ v1_funct_2(X0,X1,X2)
% 59.38/8.00      | v1_funct_2(X3,sK1,sK2)
% 59.38/8.00      | X3 != X0
% 59.38/8.00      | sK2 != X2
% 59.38/8.00      | sK1 != X1 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_684]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_125535,plain,
% 59.38/8.00      ( v1_funct_2(k1_xboole_0,sK1,sK2)
% 59.38/8.00      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 59.38/8.00      | sK2 != k1_xboole_0
% 59.38/8.00      | sK1 != k1_xboole_0
% 59.38/8.00      | k1_xboole_0 != k1_xboole_0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_125533]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_119440,plain,
% 59.38/8.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 59.38/8.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
% 59.38/8.00      | ~ v1_funct_1(sK4) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_31]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_104635,plain,
% 59.38/8.00      ( ~ v1_funct_2(X0,X1,X2)
% 59.38/8.00      | v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,sK1) != X0
% 59.38/8.00      | sK2 != X2
% 59.38/8.00      | sK1 != X1 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_684]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_111618,plain,
% 59.38/8.00      ( ~ v1_funct_2(X0,sK1,X1)
% 59.38/8.00      | v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,sK1) != X0
% 59.38/8.00      | sK2 != X1
% 59.38/8.00      | sK1 != sK1 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_104635]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_113992,plain,
% 59.38/8.00      ( ~ v1_funct_2(X0,sK1,sK2)
% 59.38/8.00      | v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,sK1) != X0
% 59.38/8.00      | sK2 != sK2
% 59.38/8.00      | sK1 != sK1 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_111618]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_113994,plain,
% 59.38/8.00      ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
% 59.38/8.00      | ~ v1_funct_2(k1_xboole_0,sK1,sK2)
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,sK1) != k1_xboole_0
% 59.38/8.00      | sK2 != sK2
% 59.38/8.00      | sK1 != sK1 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_113992]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_4123,plain,
% 59.38/8.00      ( X0 != X1
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,X2) != X1
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,X2) = X0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_672]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_31314,plain,
% 59.38/8.00      ( X0 != X1
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,sK1) != X1
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,sK1) = X0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_4123]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_91542,plain,
% 59.38/8.00      ( X0 != k2_partfun1(sK0,sK3,sK4,X1)
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,sK1) = X0
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,sK1) != k2_partfun1(sK0,sK3,sK4,X1) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_31314]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_91544,plain,
% 59.38/8.00      ( k2_partfun1(sK0,sK3,sK4,sK1) != k2_partfun1(sK0,sK3,sK4,k1_xboole_0)
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,sK1) = k1_xboole_0
% 59.38/8.00      | k1_xboole_0 != k2_partfun1(sK0,sK3,sK4,k1_xboole_0) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_91542]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_685,plain,
% 59.38/8.00      ( X0 != X1
% 59.38/8.00      | X2 != X3
% 59.38/8.00      | X4 != X5
% 59.38/8.00      | X6 != X7
% 59.38/8.00      | k2_partfun1(X0,X2,X4,X6) = k2_partfun1(X1,X3,X5,X7) ),
% 59.38/8.00      theory(equality) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_3093,plain,
% 59.38/8.00      ( X0 != X1
% 59.38/8.00      | X2 != sK4
% 59.38/8.00      | X3 != sK3
% 59.38/8.00      | X4 != sK0
% 59.38/8.00      | k2_partfun1(X4,X3,X2,X0) = k2_partfun1(sK0,sK3,sK4,X1) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_685]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_4221,plain,
% 59.38/8.00      ( X0 != X1
% 59.38/8.00      | X2 != sK3
% 59.38/8.00      | X3 != sK0
% 59.38/8.00      | k2_partfun1(X3,X2,sK4,X0) = k2_partfun1(sK0,sK3,sK4,X1)
% 59.38/8.00      | sK4 != sK4 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_3093]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_8747,plain,
% 59.38/8.00      ( X0 != X1
% 59.38/8.00      | X2 != sK3
% 59.38/8.00      | k2_partfun1(sK0,X2,sK4,X0) = k2_partfun1(sK0,sK3,sK4,X1)
% 59.38/8.00      | sK4 != sK4
% 59.38/8.00      | sK0 != sK0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_4221]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_13299,plain,
% 59.38/8.00      ( X0 != X1
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,X0) = k2_partfun1(sK0,sK3,sK4,X1)
% 59.38/8.00      | sK4 != sK4
% 59.38/8.00      | sK3 != sK3
% 59.38/8.00      | sK0 != sK0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_8747]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_47711,plain,
% 59.38/8.00      ( k2_partfun1(sK0,sK3,sK4,sK1) = k2_partfun1(sK0,sK3,sK4,X0)
% 59.38/8.00      | sK1 != X0
% 59.38/8.00      | sK4 != sK4
% 59.38/8.00      | sK3 != sK3
% 59.38/8.00      | sK0 != sK0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_13299]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_47712,plain,
% 59.38/8.00      ( k2_partfun1(sK0,sK3,sK4,sK1) = k2_partfun1(sK0,sK3,sK4,k1_xboole_0)
% 59.38/8.00      | sK1 != k1_xboole_0
% 59.38/8.00      | sK4 != sK4
% 59.38/8.00      | sK3 != sK3
% 59.38/8.00      | sK0 != sK0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_47711]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_13,plain,
% 59.38/8.00      ( ~ v4_relat_1(X0,X1)
% 59.38/8.00      | r1_tarski(k1_relat_1(X0),X1)
% 59.38/8.00      | ~ v1_relat_1(X0) ),
% 59.38/8.00      inference(cnf_transformation,[],[f70]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1519,plain,
% 59.38/8.00      ( v4_relat_1(X0,X1) != iProver_top
% 59.38/8.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 59.38/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1,plain,
% 59.38/8.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 59.38/8.00      inference(cnf_transformation,[],[f61]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1526,plain,
% 59.38/8.00      ( X0 = X1
% 59.38/8.00      | r1_tarski(X0,X1) != iProver_top
% 59.38/8.00      | r1_tarski(X1,X0) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_4786,plain,
% 59.38/8.00      ( k1_relat_1(X0) = X1
% 59.38/8.00      | v4_relat_1(X0,X1) != iProver_top
% 59.38/8.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 59.38/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1519,c_1526]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_32176,plain,
% 59.38/8.00      ( k1_relat_1(k7_relat_1(sK4,sK1)) = X0
% 59.38/8.00      | v4_relat_1(k7_relat_1(sK4,sK1),X0) != iProver_top
% 59.38/8.00      | r1_tarski(X0,sK1) != iProver_top
% 59.38/8.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_12253,c_4786]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_32315,plain,
% 59.38/8.00      ( sK1 = X0
% 59.38/8.00      | v4_relat_1(k7_relat_1(sK4,sK1),X0) != iProver_top
% 59.38/8.00      | r1_tarski(X0,sK1) != iProver_top
% 59.38/8.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 59.38/8.00      inference(demodulation,[status(thm)],[c_32176,c_12253]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_32401,plain,
% 59.38/8.00      ( sK1 = k1_xboole_0
% 59.38/8.00      | v4_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0) != iProver_top
% 59.38/8.00      | r1_tarski(k1_xboole_0,sK1) != iProver_top
% 59.38/8.00      | v1_relat_1(k7_relat_1(sK4,sK1)) != iProver_top ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_32315]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_674,plain,
% 59.38/8.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 59.38/8.00      theory(equality) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2031,plain,
% 59.38/8.00      ( ~ r1_tarski(X0,X1)
% 59.38/8.00      | r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK1,sK2))
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,sK1) != X0
% 59.38/8.00      | k2_zfmisc_1(sK1,sK2) != X1 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_674]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2450,plain,
% 59.38/8.00      ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2))
% 59.38/8.00      | r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK1,sK2))
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,sK1) != X0
% 59.38/8.00      | k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_2031]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_23127,plain,
% 59.38/8.00      ( ~ r1_tarski(k2_partfun1(sK0,sK3,sK4,X0),k2_zfmisc_1(sK1,sK2))
% 59.38/8.00      | r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK1,sK2))
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,sK1) != k2_partfun1(sK0,sK3,sK4,X0)
% 59.38/8.00      | k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_2450]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_23130,plain,
% 59.38/8.00      ( r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK1,sK2))
% 59.38/8.00      | ~ r1_tarski(k2_partfun1(sK0,sK3,sK4,k1_xboole_0),k2_zfmisc_1(sK1,sK2))
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,sK1) != k2_partfun1(sK0,sK3,sK4,k1_xboole_0)
% 59.38/8.00      | k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_23127]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_18425,plain,
% 59.38/8.00      ( r1_tarski(sK2,sK2) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_3]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_7278,plain,
% 59.38/8.00      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_1]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_18424,plain,
% 59.38/8.00      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_7278]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2195,plain,
% 59.38/8.00      ( ~ r1_tarski(X0,X1)
% 59.38/8.00      | r1_tarski(X2,k2_zfmisc_1(X3,X4))
% 59.38/8.00      | X2 != X0
% 59.38/8.00      | k2_zfmisc_1(X3,X4) != X1 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_674]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_3509,plain,
% 59.38/8.00      ( ~ r1_tarski(X0,X1)
% 59.38/8.00      | r1_tarski(X2,k2_zfmisc_1(sK1,sK2))
% 59.38/8.00      | X2 != X0
% 59.38/8.00      | k2_zfmisc_1(sK1,sK2) != X1 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_2195]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_8117,plain,
% 59.38/8.00      ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2))
% 59.38/8.00      | r1_tarski(X1,k2_zfmisc_1(sK1,sK2))
% 59.38/8.00      | X1 != X0
% 59.38/8.00      | k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_3509]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_15495,plain,
% 59.38/8.00      ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2))
% 59.38/8.00      | r1_tarski(k2_partfun1(sK0,sK3,sK4,X1),k2_zfmisc_1(sK1,sK2))
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,X1) != X0
% 59.38/8.00      | k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_8117]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_15499,plain,
% 59.38/8.00      ( r1_tarski(k2_partfun1(sK0,sK3,sK4,k1_xboole_0),k2_zfmisc_1(sK1,sK2))
% 59.38/8.00      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK2))
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,k1_xboole_0) != k1_xboole_0
% 59.38/8.00      | k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_15495]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_4,plain,
% 59.38/8.00      ( r1_tarski(k1_xboole_0,X0) ),
% 59.38/8.00      inference(cnf_transformation,[],[f62]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1524,plain,
% 59.38/8.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_12251,plain,
% 59.38/8.00      ( k1_relat_1(k7_relat_1(sK4,k1_xboole_0)) = k1_xboole_0 ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1524,c_12243]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_33,plain,
% 59.38/8.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 59.38/8.00      | ~ v1_funct_1(X0)
% 59.38/8.00      | ~ v1_relat_1(X0) ),
% 59.38/8.00      inference(cnf_transformation,[],[f93]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1499,plain,
% 59.38/8.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 59.38/8.00      | v1_funct_1(X0) != iProver_top
% 59.38/8.00      | v1_relat_1(X0) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_4258,plain,
% 59.38/8.00      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X0)),k9_relat_1(sK4,X0)))) = iProver_top
% 59.38/8.00      | v1_funct_1(k7_relat_1(sK4,X0)) != iProver_top
% 59.38/8.00      | v1_relat_1(k7_relat_1(sK4,X0)) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_3179,c_1499]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_5444,plain,
% 59.38/8.00      ( v1_funct_1(k7_relat_1(sK4,X0)) != iProver_top
% 59.38/8.00      | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X0)),k9_relat_1(sK4,X0)))) = iProver_top ),
% 59.38/8.00      inference(global_propositional_subsumption,
% 59.38/8.00                [status(thm)],
% 59.38/8.00                [c_4258,c_2543,c_2845]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_5445,plain,
% 59.38/8.00      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X0)),k9_relat_1(sK4,X0)))) = iProver_top
% 59.38/8.00      | v1_funct_1(k7_relat_1(sK4,X0)) != iProver_top ),
% 59.38/8.00      inference(renaming,[status(thm)],[c_5444]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_13618,plain,
% 59.38/8.00      ( m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k9_relat_1(sK4,k1_xboole_0)))) = iProver_top
% 59.38/8.00      | v1_funct_1(k7_relat_1(sK4,k1_xboole_0)) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_12251,c_5445]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_6,plain,
% 59.38/8.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 59.38/8.00      inference(cnf_transformation,[],[f104]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_13626,plain,
% 59.38/8.00      ( m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 59.38/8.00      | v1_funct_1(k7_relat_1(sK4,k1_xboole_0)) != iProver_top ),
% 59.38/8.00      inference(demodulation,[status(thm)],[c_13618,c_6]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_13062,plain,
% 59.38/8.00      ( ~ m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(X1))
% 59.38/8.00      | r1_tarski(k7_relat_1(sK4,X0),X1) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_10]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_13063,plain,
% 59.38/8.00      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(X1)) != iProver_top
% 59.38/8.00      | r1_tarski(k7_relat_1(sK4,X0),X1) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_13062]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_13065,plain,
% 59.38/8.00      ( m1_subset_1(k7_relat_1(sK4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 59.38/8.00      | r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_13063]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_11771,plain,
% 59.38/8.00      ( r1_tarski(k1_xboole_0,k7_relat_1(sK4,X0)) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_4]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_11774,plain,
% 59.38/8.00      ( r1_tarski(k1_xboole_0,k7_relat_1(sK4,X0)) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_11771]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_11776,plain,
% 59.38/8.00      ( r1_tarski(k1_xboole_0,k7_relat_1(sK4,k1_xboole_0)) = iProver_top ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_11774]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_8883,plain,
% 59.38/8.00      ( v1_funct_1(k7_relat_1(sK4,k1_xboole_0)) = iProver_top ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_8867]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_8389,plain,
% 59.38/8.00      ( X0 != k7_relat_1(sK4,X1)
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,X1) = X0
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,X1) != k7_relat_1(sK4,X1) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_4123]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_8390,plain,
% 59.38/8.00      ( k2_partfun1(sK0,sK3,sK4,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,k1_xboole_0) = k1_xboole_0
% 59.38/8.00      | k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_8389]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_7729,plain,
% 59.38/8.00      ( r1_tarski(k1_xboole_0,sK1) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_4]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_7732,plain,
% 59.38/8.00      ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_7729]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_7380,plain,
% 59.38/8.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.38/8.00      | r1_tarski(X3,k1_relset_1(X1,X2,X0))
% 59.38/8.00      | ~ r1_tarski(X4,k1_relat_1(X0))
% 59.38/8.00      | X3 != X4 ),
% 59.38/8.00      inference(resolution,[status(thm)],[c_674,c_21]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_7382,plain,
% 59.38/8.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 59.38/8.00      | r1_tarski(k1_xboole_0,k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 59.38/8.00      | ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))
% 59.38/8.00      | k1_xboole_0 != k1_xboole_0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_7380]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_5756,plain,
% 59.38/8.00      ( ~ r1_tarski(X0,k7_relat_1(sK4,X1))
% 59.38/8.00      | ~ r1_tarski(k7_relat_1(sK4,X1),X0)
% 59.38/8.00      | X0 = k7_relat_1(sK4,X1) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_1]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_5757,plain,
% 59.38/8.00      ( X0 = k7_relat_1(sK4,X1)
% 59.38/8.00      | r1_tarski(X0,k7_relat_1(sK4,X1)) != iProver_top
% 59.38/8.00      | r1_tarski(k7_relat_1(sK4,X1),X0) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_5756]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_5759,plain,
% 59.38/8.00      ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
% 59.38/8.00      | r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0) != iProver_top
% 59.38/8.00      | r1_tarski(k1_xboole_0,k7_relat_1(sK4,k1_xboole_0)) != iProver_top ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_5757]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2700,plain,
% 59.38/8.00      ( ~ r1_tarski(X0,X1)
% 59.38/8.00      | r1_tarski(k1_relset_1(k1_xboole_0,X2,X3),k1_xboole_0)
% 59.38/8.00      | k1_relset_1(k1_xboole_0,X2,X3) != X0
% 59.38/8.00      | k1_xboole_0 != X1 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_674]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_4676,plain,
% 59.38/8.00      ( r1_tarski(k1_relset_1(k1_xboole_0,X0,X1),k1_xboole_0)
% 59.38/8.00      | ~ r1_tarski(k1_relat_1(X1),X2)
% 59.38/8.00      | k1_relset_1(k1_xboole_0,X0,X1) != k1_relat_1(X1)
% 59.38/8.00      | k1_xboole_0 != X2 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_2700]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_4678,plain,
% 59.38/8.00      ( r1_tarski(k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 59.38/8.00      | ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
% 59.38/8.00      | k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_relat_1(k1_xboole_0)
% 59.38/8.00      | k1_xboole_0 != k1_xboole_0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_4676]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_4129,plain,
% 59.38/8.00      ( k2_partfun1(sK0,sK3,sK4,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
% 59.38/8.00      | k1_xboole_0 = k2_partfun1(sK0,sK3,sK4,k1_xboole_0)
% 59.38/8.00      | k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_4128]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_3855,plain,
% 59.38/8.00      ( sK1 = sK1 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_671]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2188,plain,
% 59.38/8.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_4]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_3504,plain,
% 59.38/8.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,sK2)) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_2188]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2573,plain,
% 59.38/8.00      ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_4]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2577,plain,
% 59.38/8.00      ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_2573]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2515,plain,
% 59.38/8.00      ( v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) != iProver_top
% 59.38/8.00      | r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK1,sK2)) != iProver_top
% 59.38/8.00      | v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) != iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_1522,c_1497]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2522,plain,
% 59.38/8.00      ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
% 59.38/8.00      | ~ r1_tarski(k2_partfun1(sK0,sK3,sK4,sK1),k2_zfmisc_1(sK1,sK2))
% 59.38/8.00      | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
% 59.38/8.00      inference(predicate_to_equality_rev,[status(thm)],[c_2515]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2451,plain,
% 59.38/8.00      ( k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK1,sK2) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_671]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2424,plain,
% 59.38/8.00      ( r1_tarski(sK4,sK4) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_3]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2082,plain,
% 59.38/8.00      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_1]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2423,plain,
% 59.38/8.00      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_2082]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2408,plain,
% 59.38/8.00      ( r1_tarski(sK3,sK3) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_3]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2075,plain,
% 59.38/8.00      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_1]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2407,plain,
% 59.38/8.00      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_2075]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2175,plain,
% 59.38/8.00      ( ~ r1_tarski(k1_relset_1(k1_xboole_0,X0,X1),k1_xboole_0)
% 59.38/8.00      | ~ r1_tarski(k1_xboole_0,k1_relset_1(k1_xboole_0,X0,X1))
% 59.38/8.00      | k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_1]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2177,plain,
% 59.38/8.00      ( ~ r1_tarski(k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 59.38/8.00      | ~ r1_tarski(k1_xboole_0,k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 59.38/8.00      | k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_2175]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1515,plain,
% 59.38/8.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2147,plain,
% 59.38/8.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 59.38/8.00      inference(superposition,[status(thm)],[c_5,c_1515]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2149,plain,
% 59.38/8.00      ( v1_relat_1(k1_xboole_0) ),
% 59.38/8.00      inference(predicate_to_equality_rev,[status(thm)],[c_2147]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2130,plain,
% 59.38/8.00      ( sK0 = sK0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_671]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_2110,plain,
% 59.38/8.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
% 59.38/8.00      | ~ v1_funct_1(sK4)
% 59.38/8.00      | k2_partfun1(sK0,sK3,sK4,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_2108]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_8,plain,
% 59.38/8.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 59.38/8.00      inference(cnf_transformation,[],[f66]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1881,plain,
% 59.38/8.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_8]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1885,plain,
% 59.38/8.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_1881]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_26,plain,
% 59.38/8.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 59.38/8.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 59.38/8.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 59.38/8.00      inference(cnf_transformation,[],[f108]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1506,plain,
% 59.38/8.00      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 59.38/8.00      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 59.38/8.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 59.38/8.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1664,plain,
% 59.38/8.00      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 59.38/8.00      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 59.38/8.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 59.38/8.00      inference(light_normalisation,[status(thm)],[c_1506,c_6]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1757,plain,
% 59.38/8.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 59.38/8.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 59.38/8.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 59.38/8.00      inference(predicate_to_equality_rev,[status(thm)],[c_1664]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_1759,plain,
% 59.38/8.00      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 59.38/8.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 59.38/8.00      | k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_1757]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_129,plain,
% 59.38/8.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_6]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_7,plain,
% 59.38/8.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 59.38/8.00      | k1_xboole_0 = X1
% 59.38/8.00      | k1_xboole_0 = X0 ),
% 59.38/8.00      inference(cnf_transformation,[],[f63]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_128,plain,
% 59.38/8.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 59.38/8.00      | k1_xboole_0 = k1_xboole_0 ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_7]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_126,plain,
% 59.38/8.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_8]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_113,plain,
% 59.38/8.00      ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
% 59.38/8.00      | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
% 59.38/8.00      | ~ v1_relat_1(k1_xboole_0) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_13]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_94,plain,
% 59.38/8.00      ( v4_relat_1(k1_xboole_0,k1_xboole_0)
% 59.38/8.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_20]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(c_91,plain,
% 59.38/8.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 59.38/8.00      | k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 59.38/8.00      inference(instantiation,[status(thm)],[c_21]) ).
% 59.38/8.00  
% 59.38/8.00  cnf(contradiction,plain,
% 59.38/8.00      ( $false ),
% 59.38/8.00      inference(minisat,
% 59.38/8.00                [status(thm)],
% 59.38/8.00                [c_228764,c_226966,c_195210,c_161634,c_137098,c_125535,
% 59.38/8.00                 c_119440,c_113994,c_106641,c_103042,c_103040,c_91544,
% 59.38/8.00                 c_61817,c_47712,c_32401,c_23130,c_22975,c_18425,c_18424,
% 59.38/8.00                 c_15499,c_13626,c_13065,c_11776,c_8883,c_8390,c_7732,
% 59.38/8.00                 c_7382,c_6681,c_5759,c_4678,c_4129,c_3893,c_3855,c_3504,
% 59.38/8.00                 c_2577,c_2522,c_2451,c_2424,c_2423,c_2408,c_2407,c_2177,
% 59.38/8.00                 c_2149,c_2130,c_2110,c_1885,c_1759,c_129,c_128,c_126,
% 59.38/8.00                 c_113,c_94,c_91,c_46,c_39,c_44,c_41]) ).
% 59.38/8.00  
% 59.38/8.00  
% 59.38/8.00  % SZS output end CNFRefutation for theBenchmark.p
% 59.38/8.00  
% 59.38/8.00  ------                               Statistics
% 59.38/8.00  
% 59.38/8.00  ------ Selected
% 59.38/8.00  
% 59.38/8.00  total_time:                             7.061
% 59.38/8.00  
%------------------------------------------------------------------------------
