%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:31 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :  254 (3450 expanded)
%              Number of clauses        :  162 (1180 expanded)
%              Number of leaves         :   25 ( 792 expanded)
%              Depth                    :   32
%              Number of atoms          :  749 (19960 expanded)
%              Number of equality atoms :  371 (2516 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f57,plain,(
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
     => ( ( ~ m1_subset_1(k2_partfun1(X0,X3,sK5,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(k2_partfun1(X0,X3,sK5,X1),X1,X2)
          | ~ v1_funct_1(k2_partfun1(X0,X3,sK5,X1)) )
        & r1_tarski(k7_relset_1(X0,X3,sK5,X1),X2)
        & r1_tarski(X1,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_2(sK5,X0,X3)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
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
          ( ( ~ m1_subset_1(k2_partfun1(sK1,sK4,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
            | ~ v1_funct_2(k2_partfun1(sK1,sK4,X4,sK2),sK2,sK3)
            | ~ v1_funct_1(k2_partfun1(sK1,sK4,X4,sK2)) )
          & r1_tarski(k7_relset_1(sK1,sK4,X4,sK2),sK3)
          & r1_tarski(sK2,sK1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
          & v1_funct_2(X4,sK1,sK4)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)
      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) )
    & r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3)
    & r1_tarski(sK2,sK1)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    & v1_funct_2(sK5,sK1,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f44,f57,f56])).

fof(f95,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) ),
    inference(cnf_transformation,[],[f58])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f97,plain,(
    r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f96,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f17,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f37])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f94,plain,(
    v1_funct_2(sK5,sK1,sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f98,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f106,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f86])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f102,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1791,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1794,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3718,plain,
    ( k2_partfun1(sK1,sK4,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1791,c_1794])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_41,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4220,plain,
    ( k2_partfun1(sK1,sK4,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3718,c_41])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1796,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5194,plain,
    ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4220,c_1796])).

cnf(c_43,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5695,plain,
    ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5194,c_41,c_43])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1801,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5704,plain,
    ( v1_relat_1(k7_relat_1(sK5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5695,c_1801])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1797,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1807,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1798,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3945,plain,
    ( k7_relset_1(sK1,sK4,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1791,c_1798])).

cnf(c_34,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1793,plain,
    ( r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4109,plain,
    ( r1_tarski(k9_relat_1(sK5,sK2),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3945,c_1793])).

cnf(c_35,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1792,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK5,sK1,sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_653,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_37])).

cnf(c_654,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | k1_relset_1(sK1,sK4,sK5) = sK1
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_656,plain,
    ( k1_relset_1(sK1,sK4,sK5) = sK1
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_654,c_36])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1799,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3159,plain,
    ( k1_relset_1(sK1,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1791,c_1799])).

cnf(c_3269,plain,
    ( k1_relat_1(sK5) = sK1
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_656,c_3159])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1057,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1870,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_1872,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1870])).

cnf(c_3394,plain,
    ( k1_relat_1(sK5) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3269,c_39,c_3,c_1872])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1802,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5242,plain,
    ( k1_relat_1(k7_relat_1(sK5,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3394,c_1802])).

cnf(c_2733,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1791,c_1801])).

cnf(c_5554,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | k1_relat_1(k7_relat_1(sK5,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5242,c_2733])).

cnf(c_5555,plain,
    ( k1_relat_1(k7_relat_1(sK5,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5554])).

cnf(c_5562,plain,
    ( k1_relat_1(k7_relat_1(sK5,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1792,c_5555])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1803,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3077,plain,
    ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_2733,c_1803])).

cnf(c_5862,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1797,c_1799])).

cnf(c_32795,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK5,X2)) = k1_relat_1(k7_relat_1(sK5,X2))
    | r1_tarski(k9_relat_1(sK5,X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK5,X2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3077,c_5862])).

cnf(c_35588,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK5,sK2)) = k1_relat_1(k7_relat_1(sK5,sK2))
    | r1_tarski(k9_relat_1(sK5,sK2),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5562,c_32795])).

cnf(c_35593,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK5,sK2)) = sK2
    | r1_tarski(k9_relat_1(sK5,sK2),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_35588,c_5562])).

cnf(c_35625,plain,
    ( k1_relset_1(X0,sK3,k7_relat_1(sK5,sK2)) = sK2
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4109,c_35593])).

cnf(c_35725,plain,
    ( k1_relset_1(X0,sK3,k7_relat_1(sK5,sK2)) = sK2
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5704,c_35625])).

cnf(c_35731,plain,
    ( k1_relset_1(sK2,sK3,k7_relat_1(sK5,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1807,c_35725])).

cnf(c_27,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_33,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)
    | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_637,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k2_partfun1(sK1,sK4,sK5,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_33])).

cnf(c_638,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_637])).

cnf(c_1782,plain,
    ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
    | k1_xboole_0 = sK3
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_639,plain,
    ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
    | k1_xboole_0 = sK3
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1896,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_1897,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1896])).

cnf(c_2222,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | k1_xboole_0 = sK3
    | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1782,c_41,c_43,c_639,c_1897])).

cnf(c_2223,plain,
    ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
    | k1_xboole_0 = sK3
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2222])).

cnf(c_4226,plain,
    ( k1_relset_1(sK2,sK3,k7_relat_1(sK5,sK2)) != sK2
    | sK3 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4220,c_2223])).

cnf(c_35927,plain,
    ( sK3 = k1_xboole_0
    | sK2 != sK2
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_35731,c_4226])).

cnf(c_36008,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_35927])).

cnf(c_36011,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK5,sK2)),sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1797,c_36008])).

cnf(c_36012,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_36011,c_5562])).

cnf(c_36013,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k9_relat_1(sK5,sK2),sK3) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_36012,c_3077])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5306,plain,
    ( ~ r2_hidden(sK0(sK2,X0),X0)
    | r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_12403,plain,
    ( ~ r2_hidden(sK0(sK2,sK2),sK2)
    | r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_5306])).

cnf(c_12405,plain,
    ( r2_hidden(sK0(sK2,sK2),sK2) != iProver_top
    | r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12403])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_5307,plain,
    ( r2_hidden(sK0(sK2,X0),sK2)
    | r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_12404,plain,
    ( r2_hidden(sK0(sK2,sK2),sK2)
    | r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_5307])).

cnf(c_12407,plain,
    ( r2_hidden(sK0(sK2,sK2),sK2) = iProver_top
    | r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12404])).

cnf(c_36084,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36013,c_4109,c_12405,c_12407])).

cnf(c_36088,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5704,c_36084])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_605,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k2_partfun1(sK1,sK4,sK5,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK3 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_33])).

cnf(c_606,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_1784,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1816,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1784,c_9])).

cnf(c_2481,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1816,c_41,c_43,c_1897])).

cnf(c_2482,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2481])).

cnf(c_4223,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k7_relat_1(sK5,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4220,c_2482])).

cnf(c_36588,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK5,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_36088,c_4223])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1811,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_284,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_285,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_284])).

cnf(c_353,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_285])).

cnf(c_1788,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_3127,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1811,c_1788])).

cnf(c_7761,plain,
    ( r1_tarski(k9_relat_1(sK5,sK2),X0) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4109,c_3127])).

cnf(c_35626,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK5,sK2)) = sK2
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7761,c_35593])).

cnf(c_121,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1921,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_1922,plain,
    ( sK3 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1921])).

cnf(c_1924,plain,
    ( sK3 != k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1922])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_15,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_480,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_15])).

cnf(c_484,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_480,c_18])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_484])).

cnf(c_1787,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_5705,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5695,c_1787])).

cnf(c_5853,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1797])).

cnf(c_6018,plain,
    ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK5,X0)),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5705,c_5853])).

cnf(c_6084,plain,
    ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK5,X0),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6018,c_3077])).

cnf(c_7222,plain,
    ( r1_tarski(k9_relat_1(sK5,X0),k1_xboole_0) != iProver_top
    | m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6084,c_5704])).

cnf(c_7223,plain,
    ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k9_relat_1(sK5,X0),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7222])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1804,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7228,plain,
    ( r1_tarski(k9_relat_1(sK5,X0),k1_xboole_0) != iProver_top
    | r1_tarski(k7_relat_1(sK5,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7223,c_1804])).

cnf(c_11817,plain,
    ( r1_tarski(k7_relat_1(sK5,sK2),k1_xboole_0) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7761,c_7228])).

cnf(c_1805,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2662,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1787])).

cnf(c_3153,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_2662])).

cnf(c_5655,plain,
    ( r1_tarski(k7_relat_1(sK5,sK2),k1_xboole_0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5562,c_3153])).

cnf(c_12777,plain,
    ( r1_tarski(sK2,X0) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11817,c_5655])).

cnf(c_36185,plain,
    ( v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top
    | k1_relset_1(X0,X1,k7_relat_1(sK5,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_35626,c_121,c_1924,c_12777,c_36088])).

cnf(c_36186,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK5,sK2)) = sK2
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_36185])).

cnf(c_36191,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK5,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_5704,c_36186])).

cnf(c_36595,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_36588,c_8,c_36191])).

cnf(c_1060,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3099,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1060])).

cnf(c_5545,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_3099])).

cnf(c_21060,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(X2))
    | k7_relat_1(sK5,sK2) != X0
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_5545])).

cnf(c_21061,plain,
    ( k7_relat_1(sK5,sK2) != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X2)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21060])).

cnf(c_21063,plain,
    ( k7_relat_1(sK5,sK2) != k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_21061])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1806,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3611,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3153,c_1806])).

cnf(c_12769,plain,
    ( k1_relat_1(k7_relat_1(sK5,sK2)) = k1_xboole_0
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11817,c_3611])).

cnf(c_12780,plain,
    ( sK2 = k1_xboole_0
    | v1_xboole_0(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12769,c_5562])).

cnf(c_12800,plain,
    ( ~ v1_xboole_0(sK3)
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12780])).

cnf(c_12771,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11817,c_1806])).

cnf(c_12785,plain,
    ( ~ v1_xboole_0(sK3)
    | k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12771])).

cnf(c_1923,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1921])).

cnf(c_1059,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1071,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1059])).

cnf(c_116,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_118,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_112,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_111,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_108,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_110,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_108])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36595,c_36088,c_21063,c_12800,c_12785,c_1923,c_1071,c_3,c_118,c_112,c_111,c_110])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.97/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/1.52  
% 7.97/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.97/1.52  
% 7.97/1.52  ------  iProver source info
% 7.97/1.52  
% 7.97/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.97/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.97/1.52  git: non_committed_changes: false
% 7.97/1.52  git: last_make_outside_of_git: false
% 7.97/1.52  
% 7.97/1.52  ------ 
% 7.97/1.52  
% 7.97/1.52  ------ Input Options
% 7.97/1.52  
% 7.97/1.52  --out_options                           all
% 7.97/1.52  --tptp_safe_out                         true
% 7.97/1.52  --problem_path                          ""
% 7.97/1.52  --include_path                          ""
% 7.97/1.52  --clausifier                            res/vclausify_rel
% 7.97/1.52  --clausifier_options                    ""
% 7.97/1.52  --stdin                                 false
% 7.97/1.52  --stats_out                             all
% 7.97/1.52  
% 7.97/1.52  ------ General Options
% 7.97/1.52  
% 7.97/1.52  --fof                                   false
% 7.97/1.52  --time_out_real                         305.
% 7.97/1.52  --time_out_virtual                      -1.
% 7.97/1.52  --symbol_type_check                     false
% 7.97/1.52  --clausify_out                          false
% 7.97/1.52  --sig_cnt_out                           false
% 7.97/1.52  --trig_cnt_out                          false
% 7.97/1.52  --trig_cnt_out_tolerance                1.
% 7.97/1.52  --trig_cnt_out_sk_spl                   false
% 7.97/1.52  --abstr_cl_out                          false
% 7.97/1.52  
% 7.97/1.52  ------ Global Options
% 7.97/1.52  
% 7.97/1.52  --schedule                              default
% 7.97/1.52  --add_important_lit                     false
% 7.97/1.52  --prop_solver_per_cl                    1000
% 7.97/1.52  --min_unsat_core                        false
% 7.97/1.52  --soft_assumptions                      false
% 7.97/1.52  --soft_lemma_size                       3
% 7.97/1.52  --prop_impl_unit_size                   0
% 7.97/1.52  --prop_impl_unit                        []
% 7.97/1.52  --share_sel_clauses                     true
% 7.97/1.52  --reset_solvers                         false
% 7.97/1.52  --bc_imp_inh                            [conj_cone]
% 7.97/1.52  --conj_cone_tolerance                   3.
% 7.97/1.52  --extra_neg_conj                        none
% 7.97/1.52  --large_theory_mode                     true
% 7.97/1.52  --prolific_symb_bound                   200
% 7.97/1.52  --lt_threshold                          2000
% 7.97/1.52  --clause_weak_htbl                      true
% 7.97/1.52  --gc_record_bc_elim                     false
% 7.97/1.52  
% 7.97/1.52  ------ Preprocessing Options
% 7.97/1.52  
% 7.97/1.52  --preprocessing_flag                    true
% 7.97/1.52  --time_out_prep_mult                    0.1
% 7.97/1.52  --splitting_mode                        input
% 7.97/1.52  --splitting_grd                         true
% 7.97/1.52  --splitting_cvd                         false
% 7.97/1.52  --splitting_cvd_svl                     false
% 7.97/1.52  --splitting_nvd                         32
% 7.97/1.52  --sub_typing                            true
% 7.97/1.52  --prep_gs_sim                           true
% 7.97/1.52  --prep_unflatten                        true
% 7.97/1.52  --prep_res_sim                          true
% 7.97/1.52  --prep_upred                            true
% 7.97/1.52  --prep_sem_filter                       exhaustive
% 7.97/1.52  --prep_sem_filter_out                   false
% 7.97/1.52  --pred_elim                             true
% 7.97/1.52  --res_sim_input                         true
% 7.97/1.52  --eq_ax_congr_red                       true
% 7.97/1.52  --pure_diseq_elim                       true
% 7.97/1.52  --brand_transform                       false
% 7.97/1.52  --non_eq_to_eq                          false
% 7.97/1.52  --prep_def_merge                        true
% 7.97/1.52  --prep_def_merge_prop_impl              false
% 7.97/1.52  --prep_def_merge_mbd                    true
% 7.97/1.52  --prep_def_merge_tr_red                 false
% 7.97/1.52  --prep_def_merge_tr_cl                  false
% 7.97/1.52  --smt_preprocessing                     true
% 7.97/1.52  --smt_ac_axioms                         fast
% 7.97/1.52  --preprocessed_out                      false
% 7.97/1.52  --preprocessed_stats                    false
% 7.97/1.52  
% 7.97/1.52  ------ Abstraction refinement Options
% 7.97/1.52  
% 7.97/1.52  --abstr_ref                             []
% 7.97/1.52  --abstr_ref_prep                        false
% 7.97/1.52  --abstr_ref_until_sat                   false
% 7.97/1.52  --abstr_ref_sig_restrict                funpre
% 7.97/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.97/1.52  --abstr_ref_under                       []
% 7.97/1.52  
% 7.97/1.52  ------ SAT Options
% 7.97/1.52  
% 7.97/1.52  --sat_mode                              false
% 7.97/1.52  --sat_fm_restart_options                ""
% 7.97/1.52  --sat_gr_def                            false
% 7.97/1.52  --sat_epr_types                         true
% 7.97/1.52  --sat_non_cyclic_types                  false
% 7.97/1.52  --sat_finite_models                     false
% 7.97/1.52  --sat_fm_lemmas                         false
% 7.97/1.52  --sat_fm_prep                           false
% 7.97/1.52  --sat_fm_uc_incr                        true
% 7.97/1.52  --sat_out_model                         small
% 7.97/1.52  --sat_out_clauses                       false
% 7.97/1.52  
% 7.97/1.52  ------ QBF Options
% 7.97/1.52  
% 7.97/1.52  --qbf_mode                              false
% 7.97/1.52  --qbf_elim_univ                         false
% 7.97/1.52  --qbf_dom_inst                          none
% 7.97/1.52  --qbf_dom_pre_inst                      false
% 7.97/1.52  --qbf_sk_in                             false
% 7.97/1.52  --qbf_pred_elim                         true
% 7.97/1.52  --qbf_split                             512
% 7.97/1.52  
% 7.97/1.52  ------ BMC1 Options
% 7.97/1.52  
% 7.97/1.52  --bmc1_incremental                      false
% 7.97/1.52  --bmc1_axioms                           reachable_all
% 7.97/1.52  --bmc1_min_bound                        0
% 7.97/1.52  --bmc1_max_bound                        -1
% 7.97/1.52  --bmc1_max_bound_default                -1
% 7.97/1.52  --bmc1_symbol_reachability              true
% 7.97/1.52  --bmc1_property_lemmas                  false
% 7.97/1.52  --bmc1_k_induction                      false
% 7.97/1.52  --bmc1_non_equiv_states                 false
% 7.97/1.52  --bmc1_deadlock                         false
% 7.97/1.52  --bmc1_ucm                              false
% 7.97/1.52  --bmc1_add_unsat_core                   none
% 7.97/1.52  --bmc1_unsat_core_children              false
% 7.97/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.97/1.52  --bmc1_out_stat                         full
% 7.97/1.52  --bmc1_ground_init                      false
% 7.97/1.52  --bmc1_pre_inst_next_state              false
% 7.97/1.52  --bmc1_pre_inst_state                   false
% 7.97/1.52  --bmc1_pre_inst_reach_state             false
% 7.97/1.52  --bmc1_out_unsat_core                   false
% 7.97/1.52  --bmc1_aig_witness_out                  false
% 7.97/1.52  --bmc1_verbose                          false
% 7.97/1.52  --bmc1_dump_clauses_tptp                false
% 7.97/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.97/1.52  --bmc1_dump_file                        -
% 7.97/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.97/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.97/1.52  --bmc1_ucm_extend_mode                  1
% 7.97/1.52  --bmc1_ucm_init_mode                    2
% 7.97/1.52  --bmc1_ucm_cone_mode                    none
% 7.97/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.97/1.52  --bmc1_ucm_relax_model                  4
% 7.97/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.97/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.97/1.52  --bmc1_ucm_layered_model                none
% 7.97/1.52  --bmc1_ucm_max_lemma_size               10
% 7.97/1.52  
% 7.97/1.52  ------ AIG Options
% 7.97/1.52  
% 7.97/1.52  --aig_mode                              false
% 7.97/1.52  
% 7.97/1.52  ------ Instantiation Options
% 7.97/1.52  
% 7.97/1.52  --instantiation_flag                    true
% 7.97/1.52  --inst_sos_flag                         true
% 7.97/1.52  --inst_sos_phase                        true
% 7.97/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.97/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.97/1.52  --inst_lit_sel_side                     num_symb
% 7.97/1.52  --inst_solver_per_active                1400
% 7.97/1.52  --inst_solver_calls_frac                1.
% 7.97/1.52  --inst_passive_queue_type               priority_queues
% 7.97/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.97/1.52  --inst_passive_queues_freq              [25;2]
% 7.97/1.52  --inst_dismatching                      true
% 7.97/1.52  --inst_eager_unprocessed_to_passive     true
% 7.97/1.52  --inst_prop_sim_given                   true
% 7.97/1.52  --inst_prop_sim_new                     false
% 7.97/1.52  --inst_subs_new                         false
% 7.97/1.52  --inst_eq_res_simp                      false
% 7.97/1.52  --inst_subs_given                       false
% 7.97/1.52  --inst_orphan_elimination               true
% 7.97/1.52  --inst_learning_loop_flag               true
% 7.97/1.52  --inst_learning_start                   3000
% 7.97/1.52  --inst_learning_factor                  2
% 7.97/1.52  --inst_start_prop_sim_after_learn       3
% 7.97/1.52  --inst_sel_renew                        solver
% 7.97/1.52  --inst_lit_activity_flag                true
% 7.97/1.52  --inst_restr_to_given                   false
% 7.97/1.52  --inst_activity_threshold               500
% 7.97/1.52  --inst_out_proof                        true
% 7.97/1.52  
% 7.97/1.52  ------ Resolution Options
% 7.97/1.52  
% 7.97/1.52  --resolution_flag                       true
% 7.97/1.52  --res_lit_sel                           adaptive
% 7.97/1.52  --res_lit_sel_side                      none
% 7.97/1.52  --res_ordering                          kbo
% 7.97/1.52  --res_to_prop_solver                    active
% 7.97/1.52  --res_prop_simpl_new                    false
% 7.97/1.52  --res_prop_simpl_given                  true
% 7.97/1.52  --res_passive_queue_type                priority_queues
% 7.97/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.97/1.52  --res_passive_queues_freq               [15;5]
% 7.97/1.52  --res_forward_subs                      full
% 7.97/1.52  --res_backward_subs                     full
% 7.97/1.52  --res_forward_subs_resolution           true
% 7.97/1.52  --res_backward_subs_resolution          true
% 7.97/1.52  --res_orphan_elimination                true
% 7.97/1.52  --res_time_limit                        2.
% 7.97/1.52  --res_out_proof                         true
% 7.97/1.52  
% 7.97/1.52  ------ Superposition Options
% 7.97/1.52  
% 7.97/1.52  --superposition_flag                    true
% 7.97/1.52  --sup_passive_queue_type                priority_queues
% 7.97/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.97/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.97/1.52  --demod_completeness_check              fast
% 7.97/1.52  --demod_use_ground                      true
% 7.97/1.52  --sup_to_prop_solver                    passive
% 7.97/1.52  --sup_prop_simpl_new                    true
% 7.97/1.52  --sup_prop_simpl_given                  true
% 7.97/1.52  --sup_fun_splitting                     true
% 7.97/1.52  --sup_smt_interval                      50000
% 7.97/1.52  
% 7.97/1.52  ------ Superposition Simplification Setup
% 7.97/1.52  
% 7.97/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.97/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.97/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.97/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.97/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.97/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.97/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.97/1.52  --sup_immed_triv                        [TrivRules]
% 7.97/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.52  --sup_immed_bw_main                     []
% 7.97/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.97/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.97/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.52  --sup_input_bw                          []
% 7.97/1.52  
% 7.97/1.52  ------ Combination Options
% 7.97/1.52  
% 7.97/1.52  --comb_res_mult                         3
% 7.97/1.52  --comb_sup_mult                         2
% 7.97/1.52  --comb_inst_mult                        10
% 7.97/1.52  
% 7.97/1.52  ------ Debug Options
% 7.97/1.52  
% 7.97/1.52  --dbg_backtrace                         false
% 7.97/1.52  --dbg_dump_prop_clauses                 false
% 7.97/1.52  --dbg_dump_prop_clauses_file            -
% 7.97/1.52  --dbg_out_stat                          false
% 7.97/1.52  ------ Parsing...
% 7.97/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.97/1.52  
% 7.97/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.97/1.52  
% 7.97/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.97/1.52  
% 7.97/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.97/1.52  ------ Proving...
% 7.97/1.52  ------ Problem Properties 
% 7.97/1.52  
% 7.97/1.52  
% 7.97/1.52  clauses                                 36
% 7.97/1.52  conjectures                             5
% 7.97/1.52  EPR                                     9
% 7.97/1.52  Horn                                    32
% 7.97/1.52  unary                                   9
% 7.97/1.52  binary                                  11
% 7.97/1.52  lits                                    89
% 7.97/1.52  lits eq                                 29
% 7.97/1.52  fd_pure                                 0
% 7.97/1.52  fd_pseudo                               0
% 7.97/1.52  fd_cond                                 2
% 7.97/1.52  fd_pseudo_cond                          1
% 7.97/1.52  AC symbols                              0
% 7.97/1.52  
% 7.97/1.52  ------ Schedule dynamic 5 is on 
% 7.97/1.52  
% 7.97/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.97/1.52  
% 7.97/1.52  
% 7.97/1.52  ------ 
% 7.97/1.52  Current options:
% 7.97/1.52  ------ 
% 7.97/1.52  
% 7.97/1.52  ------ Input Options
% 7.97/1.52  
% 7.97/1.52  --out_options                           all
% 7.97/1.52  --tptp_safe_out                         true
% 7.97/1.52  --problem_path                          ""
% 7.97/1.52  --include_path                          ""
% 7.97/1.52  --clausifier                            res/vclausify_rel
% 7.97/1.52  --clausifier_options                    ""
% 7.97/1.52  --stdin                                 false
% 7.97/1.52  --stats_out                             all
% 7.97/1.52  
% 7.97/1.52  ------ General Options
% 7.97/1.52  
% 7.97/1.52  --fof                                   false
% 7.97/1.52  --time_out_real                         305.
% 7.97/1.52  --time_out_virtual                      -1.
% 7.97/1.52  --symbol_type_check                     false
% 7.97/1.52  --clausify_out                          false
% 7.97/1.52  --sig_cnt_out                           false
% 7.97/1.52  --trig_cnt_out                          false
% 7.97/1.52  --trig_cnt_out_tolerance                1.
% 7.97/1.52  --trig_cnt_out_sk_spl                   false
% 7.97/1.52  --abstr_cl_out                          false
% 7.97/1.52  
% 7.97/1.52  ------ Global Options
% 7.97/1.52  
% 7.97/1.52  --schedule                              default
% 7.97/1.52  --add_important_lit                     false
% 7.97/1.52  --prop_solver_per_cl                    1000
% 7.97/1.52  --min_unsat_core                        false
% 7.97/1.52  --soft_assumptions                      false
% 7.97/1.52  --soft_lemma_size                       3
% 7.97/1.52  --prop_impl_unit_size                   0
% 7.97/1.52  --prop_impl_unit                        []
% 7.97/1.52  --share_sel_clauses                     true
% 7.97/1.52  --reset_solvers                         false
% 7.97/1.52  --bc_imp_inh                            [conj_cone]
% 7.97/1.52  --conj_cone_tolerance                   3.
% 7.97/1.52  --extra_neg_conj                        none
% 7.97/1.52  --large_theory_mode                     true
% 7.97/1.52  --prolific_symb_bound                   200
% 7.97/1.52  --lt_threshold                          2000
% 7.97/1.52  --clause_weak_htbl                      true
% 7.97/1.52  --gc_record_bc_elim                     false
% 7.97/1.52  
% 7.97/1.52  ------ Preprocessing Options
% 7.97/1.52  
% 7.97/1.52  --preprocessing_flag                    true
% 7.97/1.52  --time_out_prep_mult                    0.1
% 7.97/1.52  --splitting_mode                        input
% 7.97/1.52  --splitting_grd                         true
% 7.97/1.52  --splitting_cvd                         false
% 7.97/1.52  --splitting_cvd_svl                     false
% 7.97/1.52  --splitting_nvd                         32
% 7.97/1.52  --sub_typing                            true
% 7.97/1.52  --prep_gs_sim                           true
% 7.97/1.52  --prep_unflatten                        true
% 7.97/1.52  --prep_res_sim                          true
% 7.97/1.52  --prep_upred                            true
% 7.97/1.52  --prep_sem_filter                       exhaustive
% 7.97/1.52  --prep_sem_filter_out                   false
% 7.97/1.52  --pred_elim                             true
% 7.97/1.52  --res_sim_input                         true
% 7.97/1.52  --eq_ax_congr_red                       true
% 7.97/1.52  --pure_diseq_elim                       true
% 7.97/1.52  --brand_transform                       false
% 7.97/1.52  --non_eq_to_eq                          false
% 7.97/1.52  --prep_def_merge                        true
% 7.97/1.52  --prep_def_merge_prop_impl              false
% 7.97/1.52  --prep_def_merge_mbd                    true
% 7.97/1.52  --prep_def_merge_tr_red                 false
% 7.97/1.52  --prep_def_merge_tr_cl                  false
% 7.97/1.52  --smt_preprocessing                     true
% 7.97/1.52  --smt_ac_axioms                         fast
% 7.97/1.52  --preprocessed_out                      false
% 7.97/1.52  --preprocessed_stats                    false
% 7.97/1.52  
% 7.97/1.52  ------ Abstraction refinement Options
% 7.97/1.52  
% 7.97/1.52  --abstr_ref                             []
% 7.97/1.52  --abstr_ref_prep                        false
% 7.97/1.52  --abstr_ref_until_sat                   false
% 7.97/1.52  --abstr_ref_sig_restrict                funpre
% 7.97/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.97/1.52  --abstr_ref_under                       []
% 7.97/1.52  
% 7.97/1.52  ------ SAT Options
% 7.97/1.52  
% 7.97/1.52  --sat_mode                              false
% 7.97/1.52  --sat_fm_restart_options                ""
% 7.97/1.52  --sat_gr_def                            false
% 7.97/1.52  --sat_epr_types                         true
% 7.97/1.52  --sat_non_cyclic_types                  false
% 7.97/1.52  --sat_finite_models                     false
% 7.97/1.52  --sat_fm_lemmas                         false
% 7.97/1.52  --sat_fm_prep                           false
% 7.97/1.52  --sat_fm_uc_incr                        true
% 7.97/1.52  --sat_out_model                         small
% 7.97/1.52  --sat_out_clauses                       false
% 7.97/1.52  
% 7.97/1.52  ------ QBF Options
% 7.97/1.52  
% 7.97/1.52  --qbf_mode                              false
% 7.97/1.52  --qbf_elim_univ                         false
% 7.97/1.52  --qbf_dom_inst                          none
% 7.97/1.52  --qbf_dom_pre_inst                      false
% 7.97/1.52  --qbf_sk_in                             false
% 7.97/1.52  --qbf_pred_elim                         true
% 7.97/1.52  --qbf_split                             512
% 7.97/1.52  
% 7.97/1.52  ------ BMC1 Options
% 7.97/1.52  
% 7.97/1.52  --bmc1_incremental                      false
% 7.97/1.52  --bmc1_axioms                           reachable_all
% 7.97/1.52  --bmc1_min_bound                        0
% 7.97/1.52  --bmc1_max_bound                        -1
% 7.97/1.52  --bmc1_max_bound_default                -1
% 7.97/1.52  --bmc1_symbol_reachability              true
% 7.97/1.52  --bmc1_property_lemmas                  false
% 7.97/1.52  --bmc1_k_induction                      false
% 7.97/1.52  --bmc1_non_equiv_states                 false
% 7.97/1.52  --bmc1_deadlock                         false
% 7.97/1.52  --bmc1_ucm                              false
% 7.97/1.52  --bmc1_add_unsat_core                   none
% 7.97/1.52  --bmc1_unsat_core_children              false
% 7.97/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.97/1.52  --bmc1_out_stat                         full
% 7.97/1.52  --bmc1_ground_init                      false
% 7.97/1.52  --bmc1_pre_inst_next_state              false
% 7.97/1.52  --bmc1_pre_inst_state                   false
% 7.97/1.52  --bmc1_pre_inst_reach_state             false
% 7.97/1.52  --bmc1_out_unsat_core                   false
% 7.97/1.52  --bmc1_aig_witness_out                  false
% 7.97/1.52  --bmc1_verbose                          false
% 7.97/1.52  --bmc1_dump_clauses_tptp                false
% 7.97/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.97/1.52  --bmc1_dump_file                        -
% 7.97/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.97/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.97/1.52  --bmc1_ucm_extend_mode                  1
% 7.97/1.52  --bmc1_ucm_init_mode                    2
% 7.97/1.52  --bmc1_ucm_cone_mode                    none
% 7.97/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.97/1.52  --bmc1_ucm_relax_model                  4
% 7.97/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.97/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.97/1.52  --bmc1_ucm_layered_model                none
% 7.97/1.52  --bmc1_ucm_max_lemma_size               10
% 7.97/1.52  
% 7.97/1.52  ------ AIG Options
% 7.97/1.52  
% 7.97/1.52  --aig_mode                              false
% 7.97/1.52  
% 7.97/1.52  ------ Instantiation Options
% 7.97/1.52  
% 7.97/1.52  --instantiation_flag                    true
% 7.97/1.52  --inst_sos_flag                         true
% 7.97/1.52  --inst_sos_phase                        true
% 7.97/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.97/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.97/1.52  --inst_lit_sel_side                     none
% 7.97/1.52  --inst_solver_per_active                1400
% 7.97/1.52  --inst_solver_calls_frac                1.
% 7.97/1.52  --inst_passive_queue_type               priority_queues
% 7.97/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.97/1.52  --inst_passive_queues_freq              [25;2]
% 7.97/1.52  --inst_dismatching                      true
% 7.97/1.52  --inst_eager_unprocessed_to_passive     true
% 7.97/1.52  --inst_prop_sim_given                   true
% 7.97/1.52  --inst_prop_sim_new                     false
% 7.97/1.52  --inst_subs_new                         false
% 7.97/1.52  --inst_eq_res_simp                      false
% 7.97/1.52  --inst_subs_given                       false
% 7.97/1.52  --inst_orphan_elimination               true
% 7.97/1.52  --inst_learning_loop_flag               true
% 7.97/1.52  --inst_learning_start                   3000
% 7.97/1.52  --inst_learning_factor                  2
% 7.97/1.52  --inst_start_prop_sim_after_learn       3
% 7.97/1.52  --inst_sel_renew                        solver
% 7.97/1.52  --inst_lit_activity_flag                true
% 7.97/1.52  --inst_restr_to_given                   false
% 7.97/1.52  --inst_activity_threshold               500
% 7.97/1.52  --inst_out_proof                        true
% 7.97/1.52  
% 7.97/1.52  ------ Resolution Options
% 7.97/1.52  
% 7.97/1.52  --resolution_flag                       false
% 7.97/1.52  --res_lit_sel                           adaptive
% 7.97/1.52  --res_lit_sel_side                      none
% 7.97/1.52  --res_ordering                          kbo
% 7.97/1.52  --res_to_prop_solver                    active
% 7.97/1.52  --res_prop_simpl_new                    false
% 7.97/1.52  --res_prop_simpl_given                  true
% 7.97/1.52  --res_passive_queue_type                priority_queues
% 7.97/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.97/1.52  --res_passive_queues_freq               [15;5]
% 7.97/1.52  --res_forward_subs                      full
% 7.97/1.52  --res_backward_subs                     full
% 7.97/1.52  --res_forward_subs_resolution           true
% 7.97/1.52  --res_backward_subs_resolution          true
% 7.97/1.52  --res_orphan_elimination                true
% 7.97/1.52  --res_time_limit                        2.
% 7.97/1.52  --res_out_proof                         true
% 7.97/1.52  
% 7.97/1.52  ------ Superposition Options
% 7.97/1.52  
% 7.97/1.52  --superposition_flag                    true
% 7.97/1.52  --sup_passive_queue_type                priority_queues
% 7.97/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.97/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.97/1.52  --demod_completeness_check              fast
% 7.97/1.52  --demod_use_ground                      true
% 7.97/1.52  --sup_to_prop_solver                    passive
% 7.97/1.52  --sup_prop_simpl_new                    true
% 7.97/1.52  --sup_prop_simpl_given                  true
% 7.97/1.52  --sup_fun_splitting                     true
% 7.97/1.52  --sup_smt_interval                      50000
% 7.97/1.52  
% 7.97/1.52  ------ Superposition Simplification Setup
% 7.97/1.52  
% 7.97/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.97/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.97/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.97/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.97/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.97/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.97/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.97/1.52  --sup_immed_triv                        [TrivRules]
% 7.97/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.52  --sup_immed_bw_main                     []
% 7.97/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.97/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.97/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.97/1.52  --sup_input_bw                          []
% 7.97/1.52  
% 7.97/1.52  ------ Combination Options
% 7.97/1.52  
% 7.97/1.52  --comb_res_mult                         3
% 7.97/1.52  --comb_sup_mult                         2
% 7.97/1.52  --comb_inst_mult                        10
% 7.97/1.52  
% 7.97/1.52  ------ Debug Options
% 7.97/1.52  
% 7.97/1.52  --dbg_backtrace                         false
% 7.97/1.52  --dbg_dump_prop_clauses                 false
% 7.97/1.52  --dbg_dump_prop_clauses_file            -
% 7.97/1.52  --dbg_out_stat                          false
% 7.97/1.52  
% 7.97/1.52  
% 7.97/1.52  
% 7.97/1.52  
% 7.97/1.52  ------ Proving...
% 7.97/1.52  
% 7.97/1.52  
% 7.97/1.52  % SZS status Theorem for theBenchmark.p
% 7.97/1.52  
% 7.97/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.97/1.52  
% 7.97/1.52  fof(f20,conjecture,(
% 7.97/1.52    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f21,negated_conjecture,(
% 7.97/1.52    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 7.97/1.52    inference(negated_conjecture,[],[f20])).
% 7.97/1.52  
% 7.97/1.52  fof(f43,plain,(
% 7.97/1.52    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 7.97/1.52    inference(ennf_transformation,[],[f21])).
% 7.97/1.52  
% 7.97/1.52  fof(f44,plain,(
% 7.97/1.52    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 7.97/1.52    inference(flattening,[],[f43])).
% 7.97/1.52  
% 7.97/1.52  fof(f57,plain,(
% 7.97/1.52    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(X0,X3,sK5,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,sK5,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,sK5,X1))) & r1_tarski(k7_relset_1(X0,X3,sK5,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(sK5,X0,X3) & v1_funct_1(sK5))) )),
% 7.97/1.52    introduced(choice_axiom,[])).
% 7.97/1.52  
% 7.97/1.52  fof(f56,plain,(
% 7.97/1.52    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK1,sK4,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(k2_partfun1(sK1,sK4,X4,sK2),sK2,sK3) | ~v1_funct_1(k2_partfun1(sK1,sK4,X4,sK2))) & r1_tarski(k7_relset_1(sK1,sK4,X4,sK2),sK3) & r1_tarski(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) & v1_funct_2(X4,sK1,sK4) & v1_funct_1(X4)) & ~v1_xboole_0(sK4))),
% 7.97/1.52    introduced(choice_axiom,[])).
% 7.97/1.52  
% 7.97/1.52  fof(f58,plain,(
% 7.97/1.52    ((~m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3) | ~v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))) & r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) & r1_tarski(sK2,sK1) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) & v1_funct_2(sK5,sK1,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 7.97/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f44,f57,f56])).
% 7.97/1.52  
% 7.97/1.52  fof(f95,plain,(
% 7.97/1.52    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))),
% 7.97/1.52    inference(cnf_transformation,[],[f58])).
% 7.97/1.52  
% 7.97/1.52  fof(f19,axiom,(
% 7.97/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f41,plain,(
% 7.97/1.52    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.97/1.52    inference(ennf_transformation,[],[f19])).
% 7.97/1.52  
% 7.97/1.52  fof(f42,plain,(
% 7.97/1.52    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.97/1.52    inference(flattening,[],[f41])).
% 7.97/1.52  
% 7.97/1.52  fof(f91,plain,(
% 7.97/1.52    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f42])).
% 7.97/1.52  
% 7.97/1.52  fof(f93,plain,(
% 7.97/1.52    v1_funct_1(sK5)),
% 7.97/1.52    inference(cnf_transformation,[],[f58])).
% 7.97/1.52  
% 7.97/1.52  fof(f18,axiom,(
% 7.97/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f39,plain,(
% 7.97/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.97/1.52    inference(ennf_transformation,[],[f18])).
% 7.97/1.52  
% 7.97/1.52  fof(f40,plain,(
% 7.97/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.97/1.52    inference(flattening,[],[f39])).
% 7.97/1.52  
% 7.97/1.52  fof(f90,plain,(
% 7.97/1.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f40])).
% 7.97/1.52  
% 7.97/1.52  fof(f11,axiom,(
% 7.97/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f30,plain,(
% 7.97/1.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.97/1.52    inference(ennf_transformation,[],[f11])).
% 7.97/1.52  
% 7.97/1.52  fof(f77,plain,(
% 7.97/1.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.97/1.52    inference(cnf_transformation,[],[f30])).
% 7.97/1.52  
% 7.97/1.52  fof(f16,axiom,(
% 7.97/1.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f35,plain,(
% 7.97/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.97/1.52    inference(ennf_transformation,[],[f16])).
% 7.97/1.52  
% 7.97/1.52  fof(f36,plain,(
% 7.97/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.97/1.52    inference(flattening,[],[f35])).
% 7.97/1.52  
% 7.97/1.52  fof(f82,plain,(
% 7.97/1.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f36])).
% 7.97/1.52  
% 7.97/1.52  fof(f3,axiom,(
% 7.97/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f49,plain,(
% 7.97/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.97/1.52    inference(nnf_transformation,[],[f3])).
% 7.97/1.52  
% 7.97/1.52  fof(f50,plain,(
% 7.97/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.97/1.52    inference(flattening,[],[f49])).
% 7.97/1.52  
% 7.97/1.52  fof(f63,plain,(
% 7.97/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.97/1.52    inference(cnf_transformation,[],[f50])).
% 7.97/1.52  
% 7.97/1.52  fof(f100,plain,(
% 7.97/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.97/1.52    inference(equality_resolution,[],[f63])).
% 7.97/1.52  
% 7.97/1.52  fof(f15,axiom,(
% 7.97/1.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f34,plain,(
% 7.97/1.52    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.97/1.52    inference(ennf_transformation,[],[f15])).
% 7.97/1.52  
% 7.97/1.52  fof(f81,plain,(
% 7.97/1.52    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.97/1.52    inference(cnf_transformation,[],[f34])).
% 7.97/1.52  
% 7.97/1.52  fof(f97,plain,(
% 7.97/1.52    r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3)),
% 7.97/1.52    inference(cnf_transformation,[],[f58])).
% 7.97/1.52  
% 7.97/1.52  fof(f96,plain,(
% 7.97/1.52    r1_tarski(sK2,sK1)),
% 7.97/1.52    inference(cnf_transformation,[],[f58])).
% 7.97/1.52  
% 7.97/1.52  fof(f17,axiom,(
% 7.97/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f37,plain,(
% 7.97/1.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.97/1.52    inference(ennf_transformation,[],[f17])).
% 7.97/1.52  
% 7.97/1.52  fof(f38,plain,(
% 7.97/1.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.97/1.52    inference(flattening,[],[f37])).
% 7.97/1.52  
% 7.97/1.52  fof(f55,plain,(
% 7.97/1.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.97/1.52    inference(nnf_transformation,[],[f38])).
% 7.97/1.52  
% 7.97/1.52  fof(f83,plain,(
% 7.97/1.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.97/1.52    inference(cnf_transformation,[],[f55])).
% 7.97/1.52  
% 7.97/1.52  fof(f94,plain,(
% 7.97/1.52    v1_funct_2(sK5,sK1,sK4)),
% 7.97/1.52    inference(cnf_transformation,[],[f58])).
% 7.97/1.52  
% 7.97/1.52  fof(f14,axiom,(
% 7.97/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f33,plain,(
% 7.97/1.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.97/1.52    inference(ennf_transformation,[],[f14])).
% 7.97/1.52  
% 7.97/1.52  fof(f80,plain,(
% 7.97/1.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.97/1.52    inference(cnf_transformation,[],[f33])).
% 7.97/1.52  
% 7.97/1.52  fof(f92,plain,(
% 7.97/1.52    ~v1_xboole_0(sK4)),
% 7.97/1.52    inference(cnf_transformation,[],[f58])).
% 7.97/1.52  
% 7.97/1.52  fof(f2,axiom,(
% 7.97/1.52    v1_xboole_0(k1_xboole_0)),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f62,plain,(
% 7.97/1.52    v1_xboole_0(k1_xboole_0)),
% 7.97/1.52    inference(cnf_transformation,[],[f2])).
% 7.97/1.52  
% 7.97/1.52  fof(f10,axiom,(
% 7.97/1.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f28,plain,(
% 7.97/1.52    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.97/1.52    inference(ennf_transformation,[],[f10])).
% 7.97/1.52  
% 7.97/1.52  fof(f29,plain,(
% 7.97/1.52    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.97/1.52    inference(flattening,[],[f28])).
% 7.97/1.52  
% 7.97/1.52  fof(f76,plain,(
% 7.97/1.52    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f29])).
% 7.97/1.52  
% 7.97/1.52  fof(f9,axiom,(
% 7.97/1.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f27,plain,(
% 7.97/1.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.97/1.52    inference(ennf_transformation,[],[f9])).
% 7.97/1.52  
% 7.97/1.52  fof(f75,plain,(
% 7.97/1.52    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f27])).
% 7.97/1.52  
% 7.97/1.52  fof(f85,plain,(
% 7.97/1.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.97/1.52    inference(cnf_transformation,[],[f55])).
% 7.97/1.52  
% 7.97/1.52  fof(f98,plain,(
% 7.97/1.52    ~m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3) | ~v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))),
% 7.97/1.52    inference(cnf_transformation,[],[f58])).
% 7.97/1.52  
% 7.97/1.52  fof(f89,plain,(
% 7.97/1.52    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f40])).
% 7.97/1.52  
% 7.97/1.52  fof(f1,axiom,(
% 7.97/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f23,plain,(
% 7.97/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.97/1.52    inference(ennf_transformation,[],[f1])).
% 7.97/1.52  
% 7.97/1.52  fof(f45,plain,(
% 7.97/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.97/1.52    inference(nnf_transformation,[],[f23])).
% 7.97/1.52  
% 7.97/1.52  fof(f46,plain,(
% 7.97/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.97/1.52    inference(rectify,[],[f45])).
% 7.97/1.52  
% 7.97/1.52  fof(f47,plain,(
% 7.97/1.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.97/1.52    introduced(choice_axiom,[])).
% 7.97/1.52  
% 7.97/1.52  fof(f48,plain,(
% 7.97/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.97/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).
% 7.97/1.52  
% 7.97/1.52  fof(f61,plain,(
% 7.97/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f48])).
% 7.97/1.52  
% 7.97/1.52  fof(f60,plain,(
% 7.97/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f48])).
% 7.97/1.52  
% 7.97/1.52  fof(f86,plain,(
% 7.97/1.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.97/1.52    inference(cnf_transformation,[],[f55])).
% 7.97/1.52  
% 7.97/1.52  fof(f106,plain,(
% 7.97/1.52    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.97/1.52    inference(equality_resolution,[],[f86])).
% 7.97/1.52  
% 7.97/1.52  fof(f5,axiom,(
% 7.97/1.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f51,plain,(
% 7.97/1.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.97/1.52    inference(nnf_transformation,[],[f5])).
% 7.97/1.52  
% 7.97/1.52  fof(f52,plain,(
% 7.97/1.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.97/1.52    inference(flattening,[],[f51])).
% 7.97/1.52  
% 7.97/1.52  fof(f68,plain,(
% 7.97/1.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.97/1.52    inference(cnf_transformation,[],[f52])).
% 7.97/1.52  
% 7.97/1.52  fof(f102,plain,(
% 7.97/1.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.97/1.52    inference(equality_resolution,[],[f68])).
% 7.97/1.52  
% 7.97/1.52  fof(f69,plain,(
% 7.97/1.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.97/1.52    inference(cnf_transformation,[],[f52])).
% 7.97/1.52  
% 7.97/1.52  fof(f101,plain,(
% 7.97/1.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.97/1.52    inference(equality_resolution,[],[f69])).
% 7.97/1.52  
% 7.97/1.52  fof(f7,axiom,(
% 7.97/1.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f25,plain,(
% 7.97/1.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.97/1.52    inference(ennf_transformation,[],[f7])).
% 7.97/1.52  
% 7.97/1.52  fof(f72,plain,(
% 7.97/1.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f25])).
% 7.97/1.52  
% 7.97/1.52  fof(f6,axiom,(
% 7.97/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f53,plain,(
% 7.97/1.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.97/1.52    inference(nnf_transformation,[],[f6])).
% 7.97/1.52  
% 7.97/1.52  fof(f71,plain,(
% 7.97/1.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f53])).
% 7.97/1.52  
% 7.97/1.52  fof(f12,axiom,(
% 7.97/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f22,plain,(
% 7.97/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.97/1.52    inference(pure_predicate_removal,[],[f12])).
% 7.97/1.52  
% 7.97/1.52  fof(f31,plain,(
% 7.97/1.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.97/1.52    inference(ennf_transformation,[],[f22])).
% 7.97/1.52  
% 7.97/1.52  fof(f78,plain,(
% 7.97/1.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.97/1.52    inference(cnf_transformation,[],[f31])).
% 7.97/1.52  
% 7.97/1.52  fof(f8,axiom,(
% 7.97/1.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f26,plain,(
% 7.97/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.97/1.52    inference(ennf_transformation,[],[f8])).
% 7.97/1.52  
% 7.97/1.52  fof(f54,plain,(
% 7.97/1.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.97/1.52    inference(nnf_transformation,[],[f26])).
% 7.97/1.52  
% 7.97/1.52  fof(f73,plain,(
% 7.97/1.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f54])).
% 7.97/1.52  
% 7.97/1.52  fof(f70,plain,(
% 7.97/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.97/1.52    inference(cnf_transformation,[],[f53])).
% 7.97/1.52  
% 7.97/1.52  fof(f4,axiom,(
% 7.97/1.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 7.97/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.52  
% 7.97/1.52  fof(f24,plain,(
% 7.97/1.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 7.97/1.52    inference(ennf_transformation,[],[f4])).
% 7.97/1.52  
% 7.97/1.52  fof(f66,plain,(
% 7.97/1.52    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f24])).
% 7.97/1.52  
% 7.97/1.52  fof(f67,plain,(
% 7.97/1.52    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.97/1.52    inference(cnf_transformation,[],[f52])).
% 7.97/1.52  
% 7.97/1.52  cnf(c_36,negated_conjecture,
% 7.97/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) ),
% 7.97/1.52      inference(cnf_transformation,[],[f95]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1791,plain,
% 7.97/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_32,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | ~ v1_funct_1(X0)
% 7.97/1.52      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.97/1.52      inference(cnf_transformation,[],[f91]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1794,plain,
% 7.97/1.52      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.97/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.97/1.52      | v1_funct_1(X2) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3718,plain,
% 7.97/1.52      ( k2_partfun1(sK1,sK4,sK5,X0) = k7_relat_1(sK5,X0)
% 7.97/1.52      | v1_funct_1(sK5) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1791,c_1794]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_38,negated_conjecture,
% 7.97/1.52      ( v1_funct_1(sK5) ),
% 7.97/1.52      inference(cnf_transformation,[],[f93]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_41,plain,
% 7.97/1.52      ( v1_funct_1(sK5) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_4220,plain,
% 7.97/1.52      ( k2_partfun1(sK1,sK4,sK5,X0) = k7_relat_1(sK5,X0) ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_3718,c_41]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_30,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | ~ v1_funct_1(X0) ),
% 7.97/1.52      inference(cnf_transformation,[],[f90]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1796,plain,
% 7.97/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.97/1.52      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.97/1.52      | v1_funct_1(X0) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5194,plain,
% 7.97/1.52      ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top
% 7.97/1.52      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) != iProver_top
% 7.97/1.52      | v1_funct_1(sK5) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_4220,c_1796]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_43,plain,
% 7.97/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5695,plain,
% 7.97/1.52      ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_5194,c_41,c_43]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_18,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | v1_relat_1(X0) ),
% 7.97/1.52      inference(cnf_transformation,[],[f77]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1801,plain,
% 7.97/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.97/1.52      | v1_relat_1(X0) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5704,plain,
% 7.97/1.52      ( v1_relat_1(k7_relat_1(sK5,X0)) = iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_5695,c_1801]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_23,plain,
% 7.97/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.97/1.52      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.97/1.52      | ~ v1_relat_1(X0) ),
% 7.97/1.52      inference(cnf_transformation,[],[f82]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1797,plain,
% 7.97/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.97/1.52      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.97/1.52      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.97/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_6,plain,
% 7.97/1.52      ( r1_tarski(X0,X0) ),
% 7.97/1.52      inference(cnf_transformation,[],[f100]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1807,plain,
% 7.97/1.52      ( r1_tarski(X0,X0) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_22,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.97/1.52      inference(cnf_transformation,[],[f81]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1798,plain,
% 7.97/1.52      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.97/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3945,plain,
% 7.97/1.52      ( k7_relset_1(sK1,sK4,sK5,X0) = k9_relat_1(sK5,X0) ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1791,c_1798]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_34,negated_conjecture,
% 7.97/1.52      ( r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) ),
% 7.97/1.52      inference(cnf_transformation,[],[f97]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1793,plain,
% 7.97/1.52      ( r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_4109,plain,
% 7.97/1.52      ( r1_tarski(k9_relat_1(sK5,sK2),sK3) = iProver_top ),
% 7.97/1.52      inference(demodulation,[status(thm)],[c_3945,c_1793]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_35,negated_conjecture,
% 7.97/1.52      ( r1_tarski(sK2,sK1) ),
% 7.97/1.52      inference(cnf_transformation,[],[f96]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1792,plain,
% 7.97/1.52      ( r1_tarski(sK2,sK1) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_29,plain,
% 7.97/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.97/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | k1_relset_1(X1,X2,X0) = X1
% 7.97/1.52      | k1_xboole_0 = X2 ),
% 7.97/1.52      inference(cnf_transformation,[],[f83]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_37,negated_conjecture,
% 7.97/1.52      ( v1_funct_2(sK5,sK1,sK4) ),
% 7.97/1.52      inference(cnf_transformation,[],[f94]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_653,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | k1_relset_1(X1,X2,X0) = X1
% 7.97/1.52      | sK5 != X0
% 7.97/1.52      | sK4 != X2
% 7.97/1.52      | sK1 != X1
% 7.97/1.52      | k1_xboole_0 = X2 ),
% 7.97/1.52      inference(resolution_lifted,[status(thm)],[c_29,c_37]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_654,plain,
% 7.97/1.52      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
% 7.97/1.52      | k1_relset_1(sK1,sK4,sK5) = sK1
% 7.97/1.52      | k1_xboole_0 = sK4 ),
% 7.97/1.52      inference(unflattening,[status(thm)],[c_653]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_656,plain,
% 7.97/1.52      ( k1_relset_1(sK1,sK4,sK5) = sK1 | k1_xboole_0 = sK4 ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_654,c_36]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_21,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.97/1.52      inference(cnf_transformation,[],[f80]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1799,plain,
% 7.97/1.52      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.97/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3159,plain,
% 7.97/1.52      ( k1_relset_1(sK1,sK4,sK5) = k1_relat_1(sK5) ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1791,c_1799]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3269,plain,
% 7.97/1.52      ( k1_relat_1(sK5) = sK1 | sK4 = k1_xboole_0 ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_656,c_3159]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_39,negated_conjecture,
% 7.97/1.52      ( ~ v1_xboole_0(sK4) ),
% 7.97/1.52      inference(cnf_transformation,[],[f92]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3,plain,
% 7.97/1.52      ( v1_xboole_0(k1_xboole_0) ),
% 7.97/1.52      inference(cnf_transformation,[],[f62]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1057,plain,
% 7.97/1.52      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.97/1.52      theory(equality) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1870,plain,
% 7.97/1.52      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_1057]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1872,plain,
% 7.97/1.52      ( v1_xboole_0(sK4)
% 7.97/1.52      | ~ v1_xboole_0(k1_xboole_0)
% 7.97/1.52      | sK4 != k1_xboole_0 ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_1870]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3394,plain,
% 7.97/1.52      ( k1_relat_1(sK5) = sK1 ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_3269,c_39,c_3,c_1872]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_17,plain,
% 7.97/1.52      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.97/1.52      | ~ v1_relat_1(X1)
% 7.97/1.52      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 7.97/1.52      inference(cnf_transformation,[],[f76]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1802,plain,
% 7.97/1.52      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 7.97/1.52      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.97/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5242,plain,
% 7.97/1.52      ( k1_relat_1(k7_relat_1(sK5,X0)) = X0
% 7.97/1.52      | r1_tarski(X0,sK1) != iProver_top
% 7.97/1.52      | v1_relat_1(sK5) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_3394,c_1802]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_2733,plain,
% 7.97/1.52      ( v1_relat_1(sK5) = iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1791,c_1801]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5554,plain,
% 7.97/1.52      ( r1_tarski(X0,sK1) != iProver_top
% 7.97/1.52      | k1_relat_1(k7_relat_1(sK5,X0)) = X0 ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_5242,c_2733]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5555,plain,
% 7.97/1.52      ( k1_relat_1(k7_relat_1(sK5,X0)) = X0
% 7.97/1.52      | r1_tarski(X0,sK1) != iProver_top ),
% 7.97/1.52      inference(renaming,[status(thm)],[c_5554]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5562,plain,
% 7.97/1.52      ( k1_relat_1(k7_relat_1(sK5,sK2)) = sK2 ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1792,c_5555]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_16,plain,
% 7.97/1.52      ( ~ v1_relat_1(X0)
% 7.97/1.52      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.97/1.52      inference(cnf_transformation,[],[f75]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1803,plain,
% 7.97/1.52      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.97/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3077,plain,
% 7.97/1.52      ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_2733,c_1803]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5862,plain,
% 7.97/1.52      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.97/1.52      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 7.97/1.52      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 7.97/1.52      | v1_relat_1(X2) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1797,c_1799]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_32795,plain,
% 7.97/1.52      ( k1_relset_1(X0,X1,k7_relat_1(sK5,X2)) = k1_relat_1(k7_relat_1(sK5,X2))
% 7.97/1.52      | r1_tarski(k9_relat_1(sK5,X2),X1) != iProver_top
% 7.97/1.52      | r1_tarski(k1_relat_1(k7_relat_1(sK5,X2)),X0) != iProver_top
% 7.97/1.52      | v1_relat_1(k7_relat_1(sK5,X2)) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_3077,c_5862]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_35588,plain,
% 7.97/1.52      ( k1_relset_1(X0,X1,k7_relat_1(sK5,sK2)) = k1_relat_1(k7_relat_1(sK5,sK2))
% 7.97/1.52      | r1_tarski(k9_relat_1(sK5,sK2),X1) != iProver_top
% 7.97/1.52      | r1_tarski(sK2,X0) != iProver_top
% 7.97/1.52      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_5562,c_32795]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_35593,plain,
% 7.97/1.52      ( k1_relset_1(X0,X1,k7_relat_1(sK5,sK2)) = sK2
% 7.97/1.52      | r1_tarski(k9_relat_1(sK5,sK2),X1) != iProver_top
% 7.97/1.52      | r1_tarski(sK2,X0) != iProver_top
% 7.97/1.52      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 7.97/1.52      inference(light_normalisation,[status(thm)],[c_35588,c_5562]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_35625,plain,
% 7.97/1.52      ( k1_relset_1(X0,sK3,k7_relat_1(sK5,sK2)) = sK2
% 7.97/1.52      | r1_tarski(sK2,X0) != iProver_top
% 7.97/1.52      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_4109,c_35593]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_35725,plain,
% 7.97/1.52      ( k1_relset_1(X0,sK3,k7_relat_1(sK5,sK2)) = sK2
% 7.97/1.52      | r1_tarski(sK2,X0) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_5704,c_35625]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_35731,plain,
% 7.97/1.52      ( k1_relset_1(sK2,sK3,k7_relat_1(sK5,sK2)) = sK2 ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1807,c_35725]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_27,plain,
% 7.97/1.52      ( v1_funct_2(X0,X1,X2)
% 7.97/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | k1_relset_1(X1,X2,X0) != X1
% 7.97/1.52      | k1_xboole_0 = X2 ),
% 7.97/1.52      inference(cnf_transformation,[],[f85]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_33,negated_conjecture,
% 7.97/1.52      ( ~ v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)
% 7.97/1.52      | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 7.97/1.52      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
% 7.97/1.52      inference(cnf_transformation,[],[f98]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_637,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 7.97/1.52      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 7.97/1.52      | k2_partfun1(sK1,sK4,sK5,sK2) != X0
% 7.97/1.52      | k1_relset_1(X1,X2,X0) != X1
% 7.97/1.52      | sK3 != X2
% 7.97/1.52      | sK2 != X1
% 7.97/1.52      | k1_xboole_0 = X2 ),
% 7.97/1.52      inference(resolution_lifted,[status(thm)],[c_27,c_33]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_638,plain,
% 7.97/1.52      ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 7.97/1.52      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 7.97/1.52      | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
% 7.97/1.52      | k1_xboole_0 = sK3 ),
% 7.97/1.52      inference(unflattening,[status(thm)],[c_637]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1782,plain,
% 7.97/1.52      ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
% 7.97/1.52      | k1_xboole_0 = sK3
% 7.97/1.52      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 7.97/1.52      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_639,plain,
% 7.97/1.52      ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
% 7.97/1.52      | k1_xboole_0 = sK3
% 7.97/1.52      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 7.97/1.52      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_31,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | ~ v1_funct_1(X0)
% 7.97/1.52      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 7.97/1.52      inference(cnf_transformation,[],[f89]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1896,plain,
% 7.97/1.52      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
% 7.97/1.52      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 7.97/1.52      | ~ v1_funct_1(sK5) ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_31]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1897,plain,
% 7.97/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) != iProver_top
% 7.97/1.52      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) = iProver_top
% 7.97/1.52      | v1_funct_1(sK5) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_1896]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_2222,plain,
% 7.97/1.52      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 7.97/1.52      | k1_xboole_0 = sK3
% 7.97/1.52      | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2 ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_1782,c_41,c_43,c_639,c_1897]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_2223,plain,
% 7.97/1.52      ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
% 7.97/1.52      | k1_xboole_0 = sK3
% 7.97/1.52      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 7.97/1.52      inference(renaming,[status(thm)],[c_2222]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_4226,plain,
% 7.97/1.52      ( k1_relset_1(sK2,sK3,k7_relat_1(sK5,sK2)) != sK2
% 7.97/1.52      | sK3 = k1_xboole_0
% 7.97/1.52      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 7.97/1.52      inference(demodulation,[status(thm)],[c_4220,c_2223]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_35927,plain,
% 7.97/1.52      ( sK3 = k1_xboole_0
% 7.97/1.52      | sK2 != sK2
% 7.97/1.52      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 7.97/1.52      inference(demodulation,[status(thm)],[c_35731,c_4226]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_36008,plain,
% 7.97/1.52      ( sK3 = k1_xboole_0
% 7.97/1.52      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 7.97/1.52      inference(equality_resolution_simp,[status(thm)],[c_35927]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_36011,plain,
% 7.97/1.52      ( sK3 = k1_xboole_0
% 7.97/1.52      | r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3) != iProver_top
% 7.97/1.52      | r1_tarski(k1_relat_1(k7_relat_1(sK5,sK2)),sK2) != iProver_top
% 7.97/1.52      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1797,c_36008]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_36012,plain,
% 7.97/1.52      ( sK3 = k1_xboole_0
% 7.97/1.52      | r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3) != iProver_top
% 7.97/1.52      | r1_tarski(sK2,sK2) != iProver_top
% 7.97/1.52      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 7.97/1.52      inference(light_normalisation,[status(thm)],[c_36011,c_5562]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_36013,plain,
% 7.97/1.52      ( sK3 = k1_xboole_0
% 7.97/1.52      | r1_tarski(k9_relat_1(sK5,sK2),sK3) != iProver_top
% 7.97/1.52      | r1_tarski(sK2,sK2) != iProver_top
% 7.97/1.52      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 7.97/1.52      inference(demodulation,[status(thm)],[c_36012,c_3077]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_0,plain,
% 7.97/1.52      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.97/1.52      inference(cnf_transformation,[],[f61]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5306,plain,
% 7.97/1.52      ( ~ r2_hidden(sK0(sK2,X0),X0) | r1_tarski(sK2,X0) ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_0]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_12403,plain,
% 7.97/1.52      ( ~ r2_hidden(sK0(sK2,sK2),sK2) | r1_tarski(sK2,sK2) ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_5306]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_12405,plain,
% 7.97/1.52      ( r2_hidden(sK0(sK2,sK2),sK2) != iProver_top
% 7.97/1.52      | r1_tarski(sK2,sK2) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_12403]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1,plain,
% 7.97/1.52      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.97/1.52      inference(cnf_transformation,[],[f60]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5307,plain,
% 7.97/1.52      ( r2_hidden(sK0(sK2,X0),sK2) | r1_tarski(sK2,X0) ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_1]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_12404,plain,
% 7.97/1.52      ( r2_hidden(sK0(sK2,sK2),sK2) | r1_tarski(sK2,sK2) ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_5307]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_12407,plain,
% 7.97/1.52      ( r2_hidden(sK0(sK2,sK2),sK2) = iProver_top
% 7.97/1.52      | r1_tarski(sK2,sK2) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_12404]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_36084,plain,
% 7.97/1.52      ( sK3 = k1_xboole_0
% 7.97/1.52      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_36013,c_4109,c_12405,c_12407]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_36088,plain,
% 7.97/1.52      ( sK3 = k1_xboole_0 ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_5704,c_36084]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_26,plain,
% 7.97/1.52      ( v1_funct_2(X0,k1_xboole_0,X1)
% 7.97/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.97/1.52      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 7.97/1.52      inference(cnf_transformation,[],[f106]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_605,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.97/1.52      | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 7.97/1.52      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 7.97/1.52      | k2_partfun1(sK1,sK4,sK5,sK2) != X0
% 7.97/1.52      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 7.97/1.52      | sK3 != X1
% 7.97/1.52      | sK2 != k1_xboole_0 ),
% 7.97/1.52      inference(resolution_lifted,[status(thm)],[c_26,c_33]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_606,plain,
% 7.97/1.52      ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 7.97/1.52      | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 7.97/1.52      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 7.97/1.52      | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
% 7.97/1.52      | sK2 != k1_xboole_0 ),
% 7.97/1.52      inference(unflattening,[status(thm)],[c_605]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1784,plain,
% 7.97/1.52      ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
% 7.97/1.52      | sK2 != k1_xboole_0
% 7.97/1.52      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 7.97/1.52      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 7.97/1.52      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_9,plain,
% 7.97/1.52      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.97/1.52      inference(cnf_transformation,[],[f102]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1816,plain,
% 7.97/1.52      ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
% 7.97/1.52      | sK2 != k1_xboole_0
% 7.97/1.52      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 7.97/1.52      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.97/1.52      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
% 7.97/1.52      inference(demodulation,[status(thm)],[c_1784,c_9]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_2481,plain,
% 7.97/1.52      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.97/1.52      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 7.97/1.52      | sK2 != k1_xboole_0
% 7.97/1.52      | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0 ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_1816,c_41,c_43,c_1897]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_2482,plain,
% 7.97/1.52      ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
% 7.97/1.52      | sK2 != k1_xboole_0
% 7.97/1.52      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 7.97/1.52      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.97/1.52      inference(renaming,[status(thm)],[c_2481]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_4223,plain,
% 7.97/1.52      ( k1_relset_1(k1_xboole_0,sK3,k7_relat_1(sK5,sK2)) != k1_xboole_0
% 7.97/1.52      | sK2 != k1_xboole_0
% 7.97/1.52      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 7.97/1.52      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.97/1.52      inference(demodulation,[status(thm)],[c_4220,c_2482]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_36588,plain,
% 7.97/1.52      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK5,sK2)) != k1_xboole_0
% 7.97/1.52      | sK2 != k1_xboole_0
% 7.97/1.52      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 7.97/1.52      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.97/1.52      inference(demodulation,[status(thm)],[c_36088,c_4223]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_8,plain,
% 7.97/1.52      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.97/1.52      inference(cnf_transformation,[],[f101]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1811,plain,
% 7.97/1.52      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.97/1.52      | r1_tarski(X0,X1) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_13,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.97/1.52      | ~ r2_hidden(X2,X0)
% 7.97/1.52      | ~ v1_xboole_0(X1) ),
% 7.97/1.52      inference(cnf_transformation,[],[f72]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_11,plain,
% 7.97/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.97/1.52      inference(cnf_transformation,[],[f71]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_284,plain,
% 7.97/1.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.97/1.52      inference(prop_impl,[status(thm)],[c_11]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_285,plain,
% 7.97/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.97/1.52      inference(renaming,[status(thm)],[c_284]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_353,plain,
% 7.97/1.52      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 7.97/1.52      inference(bin_hyper_res,[status(thm)],[c_13,c_285]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1788,plain,
% 7.97/1.52      ( r2_hidden(X0,X1) != iProver_top
% 7.97/1.52      | r1_tarski(X1,X2) != iProver_top
% 7.97/1.52      | v1_xboole_0(X2) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_353]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3127,plain,
% 7.97/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.97/1.52      | r1_tarski(X0,X2) = iProver_top
% 7.97/1.52      | v1_xboole_0(X1) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1811,c_1788]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_7761,plain,
% 7.97/1.52      ( r1_tarski(k9_relat_1(sK5,sK2),X0) = iProver_top
% 7.97/1.52      | v1_xboole_0(sK3) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_4109,c_3127]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_35626,plain,
% 7.97/1.52      ( k1_relset_1(X0,X1,k7_relat_1(sK5,sK2)) = sK2
% 7.97/1.52      | r1_tarski(sK2,X0) != iProver_top
% 7.97/1.52      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top
% 7.97/1.52      | v1_xboole_0(sK3) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_7761,c_35593]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_121,plain,
% 7.97/1.52      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1921,plain,
% 7.97/1.52      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_1057]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1922,plain,
% 7.97/1.52      ( sK3 != X0
% 7.97/1.52      | v1_xboole_0(X0) != iProver_top
% 7.97/1.52      | v1_xboole_0(sK3) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_1921]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1924,plain,
% 7.97/1.52      ( sK3 != k1_xboole_0
% 7.97/1.52      | v1_xboole_0(sK3) = iProver_top
% 7.97/1.52      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_1922]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_19,plain,
% 7.97/1.52      ( v4_relat_1(X0,X1)
% 7.97/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.97/1.52      inference(cnf_transformation,[],[f78]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_15,plain,
% 7.97/1.52      ( ~ v4_relat_1(X0,X1)
% 7.97/1.52      | r1_tarski(k1_relat_1(X0),X1)
% 7.97/1.52      | ~ v1_relat_1(X0) ),
% 7.97/1.52      inference(cnf_transformation,[],[f73]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_480,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | r1_tarski(k1_relat_1(X0),X1)
% 7.97/1.52      | ~ v1_relat_1(X0) ),
% 7.97/1.52      inference(resolution,[status(thm)],[c_19,c_15]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_484,plain,
% 7.97/1.52      ( r1_tarski(k1_relat_1(X0),X1)
% 7.97/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_480,c_18]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_485,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.97/1.52      | r1_tarski(k1_relat_1(X0),X1) ),
% 7.97/1.52      inference(renaming,[status(thm)],[c_484]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1787,plain,
% 7.97/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.97/1.52      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5705,plain,
% 7.97/1.52      ( r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),sK1) = iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_5695,c_1787]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5853,plain,
% 7.97/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.97/1.52      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 7.97/1.52      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.97/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_8,c_1797]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_6018,plain,
% 7.97/1.52      ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.97/1.52      | r1_tarski(k2_relat_1(k7_relat_1(sK5,X0)),k1_xboole_0) != iProver_top
% 7.97/1.52      | v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_5705,c_5853]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_6084,plain,
% 7.97/1.52      ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.97/1.52      | r1_tarski(k9_relat_1(sK5,X0),k1_xboole_0) != iProver_top
% 7.97/1.52      | v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top ),
% 7.97/1.52      inference(light_normalisation,[status(thm)],[c_6018,c_3077]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_7222,plain,
% 7.97/1.52      ( r1_tarski(k9_relat_1(sK5,X0),k1_xboole_0) != iProver_top
% 7.97/1.52      | m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_6084,c_5704]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_7223,plain,
% 7.97/1.52      ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.97/1.52      | r1_tarski(k9_relat_1(sK5,X0),k1_xboole_0) != iProver_top ),
% 7.97/1.52      inference(renaming,[status(thm)],[c_7222]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_12,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.97/1.52      inference(cnf_transformation,[],[f70]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1804,plain,
% 7.97/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.97/1.52      | r1_tarski(X0,X1) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_7228,plain,
% 7.97/1.52      ( r1_tarski(k9_relat_1(sK5,X0),k1_xboole_0) != iProver_top
% 7.97/1.52      | r1_tarski(k7_relat_1(sK5,X0),k1_xboole_0) = iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_7223,c_1804]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_11817,plain,
% 7.97/1.52      ( r1_tarski(k7_relat_1(sK5,sK2),k1_xboole_0) = iProver_top
% 7.97/1.52      | v1_xboole_0(sK3) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_7761,c_7228]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1805,plain,
% 7.97/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.97/1.52      | r1_tarski(X0,X1) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_2662,plain,
% 7.97/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.97/1.52      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_8,c_1787]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3153,plain,
% 7.97/1.52      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.97/1.52      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_1805,c_2662]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5655,plain,
% 7.97/1.52      ( r1_tarski(k7_relat_1(sK5,sK2),k1_xboole_0) != iProver_top
% 7.97/1.52      | r1_tarski(sK2,X0) = iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_5562,c_3153]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_12777,plain,
% 7.97/1.52      ( r1_tarski(sK2,X0) = iProver_top
% 7.97/1.52      | v1_xboole_0(sK3) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_11817,c_5655]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_36185,plain,
% 7.97/1.52      ( v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top
% 7.97/1.52      | k1_relset_1(X0,X1,k7_relat_1(sK5,sK2)) = sK2 ),
% 7.97/1.52      inference(global_propositional_subsumption,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_35626,c_121,c_1924,c_12777,c_36088]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_36186,plain,
% 7.97/1.52      ( k1_relset_1(X0,X1,k7_relat_1(sK5,sK2)) = sK2
% 7.97/1.52      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 7.97/1.52      inference(renaming,[status(thm)],[c_36185]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_36191,plain,
% 7.97/1.52      ( k1_relset_1(X0,X1,k7_relat_1(sK5,sK2)) = sK2 ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_5704,c_36186]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_36595,plain,
% 7.97/1.52      ( sK2 != k1_xboole_0
% 7.97/1.52      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.97/1.52      inference(demodulation,[status(thm)],[c_36588,c_8,c_36191]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1060,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.97/1.52      theory(equality) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3099,plain,
% 7.97/1.52      ( m1_subset_1(X0,X1)
% 7.97/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 7.97/1.52      | X0 != X2
% 7.97/1.52      | X1 != k1_zfmisc_1(X3) ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_1060]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_5545,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.97/1.52      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 7.97/1.52      | X2 != X0
% 7.97/1.52      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_3099]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_21060,plain,
% 7.97/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.97/1.52      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(X2))
% 7.97/1.52      | k7_relat_1(sK5,sK2) != X0
% 7.97/1.52      | k1_zfmisc_1(X2) != k1_zfmisc_1(X1) ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_5545]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_21061,plain,
% 7.97/1.52      ( k7_relat_1(sK5,sK2) != X0
% 7.97/1.52      | k1_zfmisc_1(X1) != k1_zfmisc_1(X2)
% 7.97/1.52      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.97/1.52      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(X1)) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_21060]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_21063,plain,
% 7.97/1.52      ( k7_relat_1(sK5,sK2) != k1_xboole_0
% 7.97/1.52      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 7.97/1.52      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.97/1.52      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_21061]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_7,plain,
% 7.97/1.52      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 7.97/1.52      inference(cnf_transformation,[],[f66]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1806,plain,
% 7.97/1.52      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_3611,plain,
% 7.97/1.52      ( k1_relat_1(X0) = k1_xboole_0
% 7.97/1.52      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_3153,c_1806]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_12769,plain,
% 7.97/1.52      ( k1_relat_1(k7_relat_1(sK5,sK2)) = k1_xboole_0
% 7.97/1.52      | v1_xboole_0(sK3) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_11817,c_3611]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_12780,plain,
% 7.97/1.52      ( sK2 = k1_xboole_0 | v1_xboole_0(sK3) != iProver_top ),
% 7.97/1.52      inference(demodulation,[status(thm)],[c_12769,c_5562]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_12800,plain,
% 7.97/1.52      ( ~ v1_xboole_0(sK3) | sK2 = k1_xboole_0 ),
% 7.97/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_12780]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_12771,plain,
% 7.97/1.52      ( k7_relat_1(sK5,sK2) = k1_xboole_0
% 7.97/1.52      | v1_xboole_0(sK3) != iProver_top ),
% 7.97/1.52      inference(superposition,[status(thm)],[c_11817,c_1806]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_12785,plain,
% 7.97/1.52      ( ~ v1_xboole_0(sK3) | k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 7.97/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_12771]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1923,plain,
% 7.97/1.52      ( v1_xboole_0(sK3)
% 7.97/1.52      | ~ v1_xboole_0(k1_xboole_0)
% 7.97/1.52      | sK3 != k1_xboole_0 ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_1921]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1059,plain,
% 7.97/1.52      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 7.97/1.52      theory(equality) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_1071,plain,
% 7.97/1.52      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 7.97/1.52      | k1_xboole_0 != k1_xboole_0 ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_1059]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_116,plain,
% 7.97/1.52      ( r1_tarski(X0,X0) = iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_118,plain,
% 7.97/1.52      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_116]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_112,plain,
% 7.97/1.52      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_9]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_10,plain,
% 7.97/1.52      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.97/1.52      | k1_xboole_0 = X0
% 7.97/1.52      | k1_xboole_0 = X1 ),
% 7.97/1.52      inference(cnf_transformation,[],[f67]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_111,plain,
% 7.97/1.52      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.97/1.52      | k1_xboole_0 = k1_xboole_0 ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_10]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_108,plain,
% 7.97/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.97/1.52      | r1_tarski(X0,X1) != iProver_top ),
% 7.97/1.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(c_110,plain,
% 7.97/1.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.97/1.52      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.97/1.52      inference(instantiation,[status(thm)],[c_108]) ).
% 7.97/1.52  
% 7.97/1.52  cnf(contradiction,plain,
% 7.97/1.52      ( $false ),
% 7.97/1.52      inference(minisat,
% 7.97/1.52                [status(thm)],
% 7.97/1.52                [c_36595,c_36088,c_21063,c_12800,c_12785,c_1923,c_1071,
% 7.97/1.52                 c_3,c_118,c_112,c_111,c_110]) ).
% 7.97/1.52  
% 7.97/1.52  
% 7.97/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.97/1.52  
% 7.97/1.52  ------                               Statistics
% 7.97/1.52  
% 7.97/1.52  ------ General
% 7.97/1.52  
% 7.97/1.52  abstr_ref_over_cycles:                  0
% 7.97/1.52  abstr_ref_under_cycles:                 0
% 7.97/1.52  gc_basic_clause_elim:                   0
% 7.97/1.52  forced_gc_time:                         0
% 7.97/1.52  parsing_time:                           0.009
% 7.97/1.52  unif_index_cands_time:                  0.
% 7.97/1.52  unif_index_add_time:                    0.
% 7.97/1.52  orderings_time:                         0.
% 7.97/1.52  out_proof_time:                         0.018
% 7.97/1.52  total_time:                             0.889
% 7.97/1.52  num_of_symbols:                         55
% 7.97/1.52  num_of_terms:                           25531
% 7.97/1.52  
% 7.97/1.52  ------ Preprocessing
% 7.97/1.52  
% 7.97/1.52  num_of_splits:                          0
% 7.97/1.52  num_of_split_atoms:                     0
% 7.97/1.52  num_of_reused_defs:                     0
% 7.97/1.52  num_eq_ax_congr_red:                    28
% 7.97/1.52  num_of_sem_filtered_clauses:            1
% 7.97/1.52  num_of_subtypes:                        0
% 7.97/1.52  monotx_restored_types:                  0
% 7.97/1.52  sat_num_of_epr_types:                   0
% 7.97/1.52  sat_num_of_non_cyclic_types:            0
% 7.97/1.52  sat_guarded_non_collapsed_types:        0
% 7.97/1.52  num_pure_diseq_elim:                    0
% 7.97/1.52  simp_replaced_by:                       0
% 7.97/1.52  res_preprocessed:                       176
% 7.97/1.52  prep_upred:                             0
% 7.97/1.52  prep_unflattend:                        35
% 7.97/1.52  smt_new_axioms:                         0
% 7.97/1.52  pred_elim_cands:                        6
% 7.97/1.52  pred_elim:                              2
% 7.97/1.52  pred_elim_cl:                           3
% 7.97/1.52  pred_elim_cycles:                       5
% 7.97/1.52  merged_defs:                            8
% 7.97/1.52  merged_defs_ncl:                        0
% 7.97/1.52  bin_hyper_res:                          9
% 7.97/1.52  prep_cycles:                            4
% 7.97/1.52  pred_elim_time:                         0.006
% 7.97/1.52  splitting_time:                         0.
% 7.97/1.52  sem_filter_time:                        0.
% 7.97/1.52  monotx_time:                            0.
% 7.97/1.52  subtype_inf_time:                       0.
% 7.97/1.52  
% 7.97/1.52  ------ Problem properties
% 7.97/1.52  
% 7.97/1.52  clauses:                                36
% 7.97/1.52  conjectures:                            5
% 7.97/1.52  epr:                                    9
% 7.97/1.52  horn:                                   32
% 7.97/1.52  ground:                                 13
% 7.97/1.52  unary:                                  9
% 7.97/1.52  binary:                                 11
% 7.97/1.52  lits:                                   89
% 7.97/1.52  lits_eq:                                29
% 7.97/1.52  fd_pure:                                0
% 7.97/1.52  fd_pseudo:                              0
% 7.97/1.52  fd_cond:                                2
% 7.97/1.52  fd_pseudo_cond:                         1
% 7.97/1.52  ac_symbols:                             0
% 7.97/1.52  
% 7.97/1.52  ------ Propositional Solver
% 7.97/1.52  
% 7.97/1.52  prop_solver_calls:                      31
% 7.97/1.52  prop_fast_solver_calls:                 2373
% 7.97/1.52  smt_solver_calls:                       0
% 7.97/1.52  smt_fast_solver_calls:                  0
% 7.97/1.52  prop_num_of_clauses:                    15340
% 7.97/1.52  prop_preprocess_simplified:             29082
% 7.97/1.52  prop_fo_subsumed:                       97
% 7.97/1.52  prop_solver_time:                       0.
% 7.97/1.52  smt_solver_time:                        0.
% 7.97/1.52  smt_fast_solver_time:                   0.
% 7.97/1.52  prop_fast_solver_time:                  0.
% 7.97/1.52  prop_unsat_core_time:                   0.001
% 7.97/1.52  
% 7.97/1.52  ------ QBF
% 7.97/1.52  
% 7.97/1.52  qbf_q_res:                              0
% 7.97/1.52  qbf_num_tautologies:                    0
% 7.97/1.52  qbf_prep_cycles:                        0
% 7.97/1.52  
% 7.97/1.52  ------ BMC1
% 7.97/1.52  
% 7.97/1.52  bmc1_current_bound:                     -1
% 7.97/1.52  bmc1_last_solved_bound:                 -1
% 7.97/1.52  bmc1_unsat_core_size:                   -1
% 7.97/1.52  bmc1_unsat_core_parents_size:           -1
% 7.97/1.52  bmc1_merge_next_fun:                    0
% 7.97/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.97/1.52  
% 7.97/1.52  ------ Instantiation
% 7.97/1.52  
% 7.97/1.52  inst_num_of_clauses:                    4104
% 7.97/1.52  inst_num_in_passive:                    2116
% 7.97/1.52  inst_num_in_active:                     1826
% 7.97/1.52  inst_num_in_unprocessed:                162
% 7.97/1.52  inst_num_of_loops:                      2400
% 7.97/1.52  inst_num_of_learning_restarts:          0
% 7.97/1.52  inst_num_moves_active_passive:          572
% 7.97/1.52  inst_lit_activity:                      0
% 7.97/1.52  inst_lit_activity_moves:                0
% 7.97/1.52  inst_num_tautologies:                   0
% 7.97/1.52  inst_num_prop_implied:                  0
% 7.97/1.52  inst_num_existing_simplified:           0
% 7.97/1.52  inst_num_eq_res_simplified:             0
% 7.97/1.52  inst_num_child_elim:                    0
% 7.97/1.52  inst_num_of_dismatching_blockings:      2321
% 7.97/1.52  inst_num_of_non_proper_insts:           5485
% 7.97/1.52  inst_num_of_duplicates:                 0
% 7.97/1.52  inst_inst_num_from_inst_to_res:         0
% 7.97/1.52  inst_dismatching_checking_time:         0.
% 7.97/1.52  
% 7.97/1.52  ------ Resolution
% 7.97/1.52  
% 7.97/1.52  res_num_of_clauses:                     0
% 7.97/1.52  res_num_in_passive:                     0
% 7.97/1.52  res_num_in_active:                      0
% 7.97/1.52  res_num_of_loops:                       180
% 7.97/1.52  res_forward_subset_subsumed:            417
% 7.97/1.52  res_backward_subset_subsumed:           0
% 7.97/1.52  res_forward_subsumed:                   0
% 7.97/1.52  res_backward_subsumed:                  0
% 7.97/1.52  res_forward_subsumption_resolution:     0
% 7.97/1.52  res_backward_subsumption_resolution:    0
% 7.97/1.52  res_clause_to_clause_subsumption:       4176
% 7.97/1.52  res_orphan_elimination:                 0
% 7.97/1.52  res_tautology_del:                      302
% 7.97/1.52  res_num_eq_res_simplified:              0
% 7.97/1.52  res_num_sel_changes:                    0
% 7.97/1.52  res_moves_from_active_to_pass:          0
% 7.97/1.52  
% 7.97/1.52  ------ Superposition
% 7.97/1.52  
% 7.97/1.52  sup_time_total:                         0.
% 7.97/1.52  sup_time_generating:                    0.
% 7.97/1.52  sup_time_sim_full:                      0.
% 7.97/1.52  sup_time_sim_immed:                     0.
% 7.97/1.52  
% 7.97/1.52  sup_num_of_clauses:                     1237
% 7.97/1.52  sup_num_in_active:                      374
% 7.97/1.52  sup_num_in_passive:                     863
% 7.97/1.52  sup_num_of_loops:                       478
% 7.97/1.52  sup_fw_superposition:                   1227
% 7.97/1.52  sup_bw_superposition:                   579
% 7.97/1.52  sup_immediate_simplified:               308
% 7.97/1.52  sup_given_eliminated:                   6
% 7.97/1.52  comparisons_done:                       0
% 7.97/1.52  comparisons_avoided:                    0
% 7.97/1.52  
% 7.97/1.52  ------ Simplifications
% 7.97/1.52  
% 7.97/1.52  
% 7.97/1.52  sim_fw_subset_subsumed:                 52
% 7.97/1.52  sim_bw_subset_subsumed:                 39
% 7.97/1.52  sim_fw_subsumed:                        86
% 7.97/1.52  sim_bw_subsumed:                        61
% 7.97/1.52  sim_fw_subsumption_res:                 0
% 7.97/1.52  sim_bw_subsumption_res:                 0
% 7.97/1.52  sim_tautology_del:                      13
% 7.97/1.52  sim_eq_tautology_del:                   54
% 7.97/1.52  sim_eq_res_simp:                        2
% 7.97/1.52  sim_fw_demodulated:                     62
% 7.97/1.52  sim_bw_demodulated:                     69
% 7.97/1.52  sim_light_normalised:                   114
% 7.97/1.52  sim_joinable_taut:                      0
% 7.97/1.52  sim_joinable_simp:                      0
% 7.97/1.52  sim_ac_normalised:                      0
% 7.97/1.52  sim_smt_subsumption:                    0
% 7.97/1.52  
%------------------------------------------------------------------------------
