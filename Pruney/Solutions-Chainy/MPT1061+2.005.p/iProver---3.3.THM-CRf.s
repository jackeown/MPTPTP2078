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
% DateTime   : Thu Dec  3 12:09:30 EST 2020

% Result     : Theorem 19.61s
% Output     : CNFRefutation 19.61s
% Verified   : 
% Statistics : Number of formulae       :  303 (1207 expanded)
%              Number of clauses        :  214 ( 472 expanded)
%              Number of leaves         :   29 ( 264 expanded)
%              Depth                    :   24
%              Number of atoms          :  886 (6029 expanded)
%              Number of equality atoms :  438 ( 889 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

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
    inference(ennf_transformation,[],[f23])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f58,plain,(
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

fof(f57,plain,
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

fof(f59,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)
      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) )
    & r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3)
    & r1_tarski(sK2,sK1)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    & v1_funct_2(sK5,sK1,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f48,f58,f57])).

fof(f95,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) ),
    inference(cnf_transformation,[],[f59])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f97,plain,(
    r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f96,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f19,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,(
    v1_funct_2(sK5,sK1,sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f92,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f98,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

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

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f104,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f86])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f88])).

fof(f102,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f101])).

cnf(c_999,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k1_relset_1(X0,X2,X4) = k1_relset_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_66671,plain,
    ( k2_partfun1(sK1,sK4,sK5,sK2) != X0
    | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_relset_1(X1,X2,X0)
    | sK3 != X2
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_66673,plain,
    ( k2_partfun1(sK1,sK4,sK5,sK2) != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | sK3 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_66671])).

cnf(c_992,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_48523,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_partfun1(sK1,sK4,sK5,sK2))
    | k2_partfun1(sK1,sK4,sK5,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_51965,plain,
    ( v1_xboole_0(k2_partfun1(sK1,sK4,sK5,sK2))
    | ~ v1_xboole_0(k7_relat_1(sK5,sK2))
    | k2_partfun1(sK1,sK4,sK5,sK2) != k7_relat_1(sK5,sK2) ),
    inference(instantiation,[status(thm)],[c_48523])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_293,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_294,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_293])).

cnf(c_361,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_294])).

cnf(c_46498,plain,
    ( ~ r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0),k2_partfun1(sK1,sK4,sK5,sK2))
    | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_47270,plain,
    ( ~ r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0),k2_partfun1(sK1,sK4,sK5,sK2))
    | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_partfun1(sK1,sK4,sK5,sK2))
    | ~ v1_xboole_0(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(instantiation,[status(thm)],[c_46498])).

cnf(c_989,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_42263,plain,
    ( k1_relset_1(X0,X1,X2) != X3
    | k1_xboole_0 != X3
    | k1_xboole_0 = k1_relset_1(X0,X1,X2) ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_42264,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_42263])).

cnf(c_996,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_39942,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(X0,X1)
    | sK3 != X1
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_996])).

cnf(c_39943,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | sK3 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_39942])).

cnf(c_994,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3209,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_36943,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X0 != sK3
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3209])).

cnf(c_36944,plain,
    ( X0 != sK3
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36943])).

cnf(c_36946,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_36944])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1776,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1779,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3662,plain,
    ( k2_partfun1(sK1,sK4,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_1779])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_40,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3814,plain,
    ( k2_partfun1(sK1,sK4,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3662,c_40])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1781,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4247,plain,
    ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3814,c_1781])).

cnf(c_42,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4688,plain,
    ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4247,c_40,c_42])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1786,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4699,plain,
    ( v1_relat_1(k7_relat_1(sK5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4688,c_1786])).

cnf(c_22,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1782,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1783,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3236,plain,
    ( k7_relset_1(sK1,sK4,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1776,c_1783])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1778,plain,
    ( r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3272,plain,
    ( r1_tarski(k9_relat_1(sK5,sK2),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3236,c_1778])).

cnf(c_2572,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_1786])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1789,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2798,plain,
    ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_2572,c_1789])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1794,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1784,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4404,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1782,c_1784])).

cnf(c_21096,plain,
    ( k1_relset_1(k1_relat_1(X0),X1,X0) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_4404])).

cnf(c_21318,plain,
    ( k1_relset_1(k1_relat_1(k7_relat_1(sK5,X0)),X1,k7_relat_1(sK5,X0)) = k1_relat_1(k7_relat_1(sK5,X0))
    | r1_tarski(k9_relat_1(sK5,X0),X1) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2798,c_21096])).

cnf(c_28702,plain,
    ( r1_tarski(k9_relat_1(sK5,X0),X1) != iProver_top
    | k1_relset_1(k1_relat_1(k7_relat_1(sK5,X0)),X1,k7_relat_1(sK5,X0)) = k1_relat_1(k7_relat_1(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21318,c_4699])).

cnf(c_28703,plain,
    ( k1_relset_1(k1_relat_1(k7_relat_1(sK5,X0)),X1,k7_relat_1(sK5,X0)) = k1_relat_1(k7_relat_1(sK5,X0))
    | r1_tarski(k9_relat_1(sK5,X0),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_28702])).

cnf(c_28711,plain,
    ( k1_relset_1(k1_relat_1(k7_relat_1(sK5,sK2)),sK3,k7_relat_1(sK5,sK2)) = k1_relat_1(k7_relat_1(sK5,sK2)) ),
    inference(superposition,[status(thm)],[c_3272,c_28703])).

cnf(c_34,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1777,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK5,sK1,sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_36])).

cnf(c_619,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | k1_relset_1(sK1,sK4,sK5) = sK1
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_621,plain,
    ( k1_relset_1(sK1,sK4,sK5) = sK1
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_619,c_35])).

cnf(c_3139,plain,
    ( k1_relset_1(sK1,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1776,c_1784])).

cnf(c_3270,plain,
    ( k1_relat_1(sK5) = sK1
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_621,c_3139])).

cnf(c_38,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1856,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_1858,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1856])).

cnf(c_3443,plain,
    ( k1_relat_1(sK5) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3270,c_38,c_3,c_1858])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1787,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3562,plain,
    ( k1_relat_1(k7_relat_1(sK5,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3443,c_1787])).

cnf(c_4232,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | k1_relat_1(k7_relat_1(sK5,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3562,c_2572])).

cnf(c_4233,plain,
    ( k1_relat_1(k7_relat_1(sK5,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4232])).

cnf(c_4241,plain,
    ( k1_relat_1(k7_relat_1(sK5,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1777,c_4233])).

cnf(c_28717,plain,
    ( k1_relset_1(sK2,sK3,k7_relat_1(sK5,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_28711,c_4241])).

cnf(c_26,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)
    | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k2_partfun1(sK1,sK4,sK5,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_32])).

cnf(c_603,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_1766,plain,
    ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
    | k1_xboole_0 = sK3
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_604,plain,
    ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
    | k1_xboole_0 = sK3
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1882,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_1883,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1882])).

cnf(c_2230,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | k1_xboole_0 = sK3
    | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1766,c_40,c_42,c_604,c_1883])).

cnf(c_2231,plain,
    ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
    | k1_xboole_0 = sK3
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2230])).

cnf(c_3820,plain,
    ( k1_relset_1(sK2,sK3,k7_relat_1(sK5,sK2)) != sK2
    | sK3 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3814,c_2231])).

cnf(c_28883,plain,
    ( sK3 = k1_xboole_0
    | sK2 != sK2
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28717,c_3820])).

cnf(c_29127,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_28883])).

cnf(c_29130,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK5,sK2)),sK2) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1782,c_29127])).

cnf(c_29131,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29130,c_4241])).

cnf(c_29132,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k9_relat_1(sK5,sK2),sK3) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29131,c_2798])).

cnf(c_8442,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8443,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8442])).

cnf(c_29213,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29132,c_3272,c_8443])).

cnf(c_29217,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4699,c_29213])).

cnf(c_988,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_28153,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_988])).

cnf(c_28154,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_28153])).

cnf(c_990,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_8962,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),X2)
    | X2 != X1
    | k2_partfun1(sK1,sK4,sK5,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_27216,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),sK3)
    | k2_partfun1(sK1,sK4,sK5,sK2) != X0
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_8962])).

cnf(c_27217,plain,
    ( k2_partfun1(sK1,sK4,sK5,sK2) != X0
    | sK3 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27216])).

cnf(c_27219,plain,
    ( k2_partfun1(sK1,sK4,sK5,sK2) != k1_xboole_0
    | sK3 != k1_xboole_0
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),sK3) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_27217])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1798,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1773,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_3512,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1798,c_1773])).

cnf(c_7502,plain,
    ( r1_tarski(k9_relat_1(sK5,sK2),X0) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3272,c_3512])).

cnf(c_1792,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1785,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3515,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1792,c_1785])).

cnf(c_8185,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k9_relat_1(sK5,sK2)) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7502,c_3515])).

cnf(c_122,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8199,plain,
    ( v1_xboole_0(k9_relat_1(sK5,sK2)) = iProver_top
    | v1_xboole_0(sK3) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8185])).

cnf(c_10858,plain,
    ( v1_xboole_0(k9_relat_1(sK5,sK2)) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8185,c_122,c_8199])).

cnf(c_4399,plain,
    ( r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1782,c_1785])).

cnf(c_19050,plain,
    ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_4399])).

cnf(c_19221,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_19050])).

cnf(c_19256,plain,
    ( v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top
    | v1_xboole_0(k9_relat_1(sK5,X0)) != iProver_top
    | v1_xboole_0(k7_relat_1(sK5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2798,c_19221])).

cnf(c_19361,plain,
    ( v1_xboole_0(k9_relat_1(sK5,X0)) != iProver_top
    | v1_xboole_0(k7_relat_1(sK5,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19256,c_4699])).

cnf(c_19367,plain,
    ( v1_xboole_0(k7_relat_1(sK5,sK2)) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10858,c_19361])).

cnf(c_19370,plain,
    ( v1_xboole_0(k7_relat_1(sK5,sK2))
    | ~ v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19367])).

cnf(c_12069,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK1,sK4,sK5,sK2) = k7_relat_1(sK5,sK2) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_11149,plain,
    ( r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2922,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3))
    | k2_partfun1(sK1,sK4,sK5,sK2) != X0
    | k2_zfmisc_1(k1_xboole_0,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_10502,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3))
    | k2_partfun1(sK1,sK4,sK5,sK2) != X0
    | k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_2922])).

cnf(c_10503,plain,
    ( k2_partfun1(sK1,sK4,sK5,sK2) != X0
    | k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(X1,X2)
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10502])).

cnf(c_10505,plain,
    ( k2_partfun1(sK1,sK4,sK5,sK2) != k1_xboole_0
    | k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3)) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10503])).

cnf(c_9296,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_9297,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9296])).

cnf(c_7996,plain,
    ( ~ r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2))
    | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_7998,plain,
    ( ~ r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2))
    | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7996])).

cnf(c_2370,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_7979,plain,
    ( ~ r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2))
    | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2370])).

cnf(c_7980,plain,
    ( r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),sK3) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7979])).

cnf(c_2241,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ r1_tarski(sK3,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_6653,plain,
    ( ~ r2_hidden(sK0(sK3,k2_zfmisc_1(X0,X1)),sK3)
    | ~ r1_tarski(sK3,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2241])).

cnf(c_6654,plain,
    ( r2_hidden(sK0(sK3,k2_zfmisc_1(X0,X1)),sK3) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6653])).

cnf(c_6656,plain,
    ( r2_hidden(sK0(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK3) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6654])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1793,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3138,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1792,c_1784])).

cnf(c_6109,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1793,c_3138])).

cnf(c_2571,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1792,c_1786])).

cnf(c_3031,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1793,c_2571])).

cnf(c_3560,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1793,c_1787])).

cnf(c_5582,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3031,c_3560])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_18,c_14])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_496,c_18,c_17,c_14])).

cnf(c_1771,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_2662,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1792,c_1771])).

cnf(c_4867,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1793,c_2662])).

cnf(c_5587,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5582,c_4867])).

cnf(c_6113,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6109,c_5587])).

cnf(c_6118,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6113])).

cnf(c_4961,plain,
    ( r1_tarski(k1_xboole_0,k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4751,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_988])).

cnf(c_3041,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != X0
    | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_4497,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relset_1(X0,X1,X2)
    | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_xboole_0
    | k1_xboole_0 != k1_relset_1(X0,X1,X2) ),
    inference(instantiation,[status(thm)],[c_3041])).

cnf(c_4498,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_xboole_0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4497])).

cnf(c_4302,plain,
    ( r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0),k2_partfun1(sK1,sK4,sK5,sK2))
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4116,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4117,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4116])).

cnf(c_4119,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4117])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2990,plain,
    ( ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_partfun1(sK1,sK4,sK5,sK2))
    | k2_partfun1(sK1,sK4,sK5,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2895,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2749,plain,
    ( r2_hidden(sK0(sK3,k2_zfmisc_1(X0,X1)),sK3)
    | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2755,plain,
    ( r2_hidden(sK0(sK3,k2_zfmisc_1(X0,X1)),sK3) = iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2749])).

cnf(c_2757,plain,
    ( r2_hidden(sK0(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK3) = iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2755])).

cnf(c_2492,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2493,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) = iProver_top
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2492])).

cnf(c_2356,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2164,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2165,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2164])).

cnf(c_2167,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2165])).

cnf(c_1877,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_2147,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1877])).

cnf(c_2059,plain,
    ( r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2))
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2063,plain,
    ( r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2)) = iProver_top
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2059])).

cnf(c_2005,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2006,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
    | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2005])).

cnf(c_1956,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_1957,plain,
    ( sK3 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1956])).

cnf(c_1959,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1957])).

cnf(c_1907,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_1908,plain,
    ( sK3 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1907])).

cnf(c_1910,plain,
    ( sK3 != k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_1909,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1907])).

cnf(c_25,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k2_partfun1(sK1,sK4,sK5,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK3 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_571,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_572,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_23,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_524,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k2_partfun1(sK1,sK4,sK5,sK2) != k1_xboole_0
    | sK3 != k1_xboole_0
    | sK2 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_525,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | k2_partfun1(sK1,sK4,sK5,sK2) != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_120,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_114,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_116,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_115,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_66673,c_51965,c_47270,c_42264,c_39943,c_36946,c_29217,c_28154,c_27219,c_19370,c_12069,c_11149,c_10505,c_9297,c_7998,c_7980,c_6656,c_6118,c_4961,c_4751,c_4498,c_4302,c_4119,c_2990,c_2895,c_2757,c_2493,c_2356,c_2167,c_2147,c_2063,c_2059,c_2006,c_2005,c_1959,c_1910,c_1909,c_1883,c_1882,c_572,c_525,c_122,c_3,c_120,c_116,c_115,c_42,c_35,c_40,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 19.61/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.61/2.99  
% 19.61/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.61/2.99  
% 19.61/2.99  ------  iProver source info
% 19.61/2.99  
% 19.61/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.61/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.61/2.99  git: non_committed_changes: false
% 19.61/2.99  git: last_make_outside_of_git: false
% 19.61/2.99  
% 19.61/2.99  ------ 
% 19.61/2.99  
% 19.61/2.99  ------ Input Options
% 19.61/2.99  
% 19.61/2.99  --out_options                           all
% 19.61/2.99  --tptp_safe_out                         true
% 19.61/2.99  --problem_path                          ""
% 19.61/2.99  --include_path                          ""
% 19.61/2.99  --clausifier                            res/vclausify_rel
% 19.61/2.99  --clausifier_options                    ""
% 19.61/2.99  --stdin                                 false
% 19.61/2.99  --stats_out                             all
% 19.61/2.99  
% 19.61/2.99  ------ General Options
% 19.61/2.99  
% 19.61/2.99  --fof                                   false
% 19.61/2.99  --time_out_real                         305.
% 19.61/2.99  --time_out_virtual                      -1.
% 19.61/2.99  --symbol_type_check                     false
% 19.61/2.99  --clausify_out                          false
% 19.61/2.99  --sig_cnt_out                           false
% 19.61/2.99  --trig_cnt_out                          false
% 19.61/2.99  --trig_cnt_out_tolerance                1.
% 19.61/2.99  --trig_cnt_out_sk_spl                   false
% 19.61/2.99  --abstr_cl_out                          false
% 19.61/2.99  
% 19.61/2.99  ------ Global Options
% 19.61/2.99  
% 19.61/2.99  --schedule                              default
% 19.61/2.99  --add_important_lit                     false
% 19.61/2.99  --prop_solver_per_cl                    1000
% 19.61/2.99  --min_unsat_core                        false
% 19.61/2.99  --soft_assumptions                      false
% 19.61/2.99  --soft_lemma_size                       3
% 19.61/2.99  --prop_impl_unit_size                   0
% 19.61/2.99  --prop_impl_unit                        []
% 19.61/2.99  --share_sel_clauses                     true
% 19.61/2.99  --reset_solvers                         false
% 19.61/2.99  --bc_imp_inh                            [conj_cone]
% 19.61/2.99  --conj_cone_tolerance                   3.
% 19.61/2.99  --extra_neg_conj                        none
% 19.61/2.99  --large_theory_mode                     true
% 19.61/2.99  --prolific_symb_bound                   200
% 19.61/2.99  --lt_threshold                          2000
% 19.61/2.99  --clause_weak_htbl                      true
% 19.61/2.99  --gc_record_bc_elim                     false
% 19.61/2.99  
% 19.61/2.99  ------ Preprocessing Options
% 19.61/2.99  
% 19.61/2.99  --preprocessing_flag                    true
% 19.61/2.99  --time_out_prep_mult                    0.1
% 19.61/2.99  --splitting_mode                        input
% 19.61/2.99  --splitting_grd                         true
% 19.61/2.99  --splitting_cvd                         false
% 19.61/2.99  --splitting_cvd_svl                     false
% 19.61/2.99  --splitting_nvd                         32
% 19.61/2.99  --sub_typing                            true
% 19.61/2.99  --prep_gs_sim                           true
% 19.61/2.99  --prep_unflatten                        true
% 19.61/2.99  --prep_res_sim                          true
% 19.61/2.99  --prep_upred                            true
% 19.61/2.99  --prep_sem_filter                       exhaustive
% 19.61/2.99  --prep_sem_filter_out                   false
% 19.61/2.99  --pred_elim                             true
% 19.61/2.99  --res_sim_input                         true
% 19.61/2.99  --eq_ax_congr_red                       true
% 19.61/2.99  --pure_diseq_elim                       true
% 19.61/2.99  --brand_transform                       false
% 19.61/2.99  --non_eq_to_eq                          false
% 19.61/2.99  --prep_def_merge                        true
% 19.61/2.99  --prep_def_merge_prop_impl              false
% 19.61/2.99  --prep_def_merge_mbd                    true
% 19.61/2.99  --prep_def_merge_tr_red                 false
% 19.61/2.99  --prep_def_merge_tr_cl                  false
% 19.61/2.99  --smt_preprocessing                     true
% 19.61/2.99  --smt_ac_axioms                         fast
% 19.61/2.99  --preprocessed_out                      false
% 19.61/2.99  --preprocessed_stats                    false
% 19.61/2.99  
% 19.61/2.99  ------ Abstraction refinement Options
% 19.61/2.99  
% 19.61/2.99  --abstr_ref                             []
% 19.61/2.99  --abstr_ref_prep                        false
% 19.61/2.99  --abstr_ref_until_sat                   false
% 19.61/2.99  --abstr_ref_sig_restrict                funpre
% 19.61/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.61/2.99  --abstr_ref_under                       []
% 19.61/2.99  
% 19.61/2.99  ------ SAT Options
% 19.61/2.99  
% 19.61/2.99  --sat_mode                              false
% 19.61/2.99  --sat_fm_restart_options                ""
% 19.61/2.99  --sat_gr_def                            false
% 19.61/2.99  --sat_epr_types                         true
% 19.61/2.99  --sat_non_cyclic_types                  false
% 19.61/2.99  --sat_finite_models                     false
% 19.61/2.99  --sat_fm_lemmas                         false
% 19.61/2.99  --sat_fm_prep                           false
% 19.61/2.99  --sat_fm_uc_incr                        true
% 19.61/2.99  --sat_out_model                         small
% 19.61/2.99  --sat_out_clauses                       false
% 19.61/2.99  
% 19.61/2.99  ------ QBF Options
% 19.61/2.99  
% 19.61/2.99  --qbf_mode                              false
% 19.61/2.99  --qbf_elim_univ                         false
% 19.61/2.99  --qbf_dom_inst                          none
% 19.61/2.99  --qbf_dom_pre_inst                      false
% 19.61/2.99  --qbf_sk_in                             false
% 19.61/2.99  --qbf_pred_elim                         true
% 19.61/2.99  --qbf_split                             512
% 19.61/2.99  
% 19.61/2.99  ------ BMC1 Options
% 19.61/2.99  
% 19.61/2.99  --bmc1_incremental                      false
% 19.61/2.99  --bmc1_axioms                           reachable_all
% 19.61/2.99  --bmc1_min_bound                        0
% 19.61/2.99  --bmc1_max_bound                        -1
% 19.61/2.99  --bmc1_max_bound_default                -1
% 19.61/2.99  --bmc1_symbol_reachability              true
% 19.61/2.99  --bmc1_property_lemmas                  false
% 19.61/2.99  --bmc1_k_induction                      false
% 19.61/2.99  --bmc1_non_equiv_states                 false
% 19.61/2.99  --bmc1_deadlock                         false
% 19.61/2.99  --bmc1_ucm                              false
% 19.61/2.99  --bmc1_add_unsat_core                   none
% 19.61/2.99  --bmc1_unsat_core_children              false
% 19.61/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.61/2.99  --bmc1_out_stat                         full
% 19.61/2.99  --bmc1_ground_init                      false
% 19.61/2.99  --bmc1_pre_inst_next_state              false
% 19.61/2.99  --bmc1_pre_inst_state                   false
% 19.61/2.99  --bmc1_pre_inst_reach_state             false
% 19.61/2.99  --bmc1_out_unsat_core                   false
% 19.61/2.99  --bmc1_aig_witness_out                  false
% 19.61/2.99  --bmc1_verbose                          false
% 19.61/2.99  --bmc1_dump_clauses_tptp                false
% 19.61/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.61/2.99  --bmc1_dump_file                        -
% 19.61/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.61/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.61/2.99  --bmc1_ucm_extend_mode                  1
% 19.61/2.99  --bmc1_ucm_init_mode                    2
% 19.61/2.99  --bmc1_ucm_cone_mode                    none
% 19.61/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.61/2.99  --bmc1_ucm_relax_model                  4
% 19.61/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.61/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.61/2.99  --bmc1_ucm_layered_model                none
% 19.61/2.99  --bmc1_ucm_max_lemma_size               10
% 19.61/2.99  
% 19.61/2.99  ------ AIG Options
% 19.61/2.99  
% 19.61/2.99  --aig_mode                              false
% 19.61/2.99  
% 19.61/2.99  ------ Instantiation Options
% 19.61/2.99  
% 19.61/2.99  --instantiation_flag                    true
% 19.61/2.99  --inst_sos_flag                         true
% 19.61/2.99  --inst_sos_phase                        true
% 19.61/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.61/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.61/2.99  --inst_lit_sel_side                     num_symb
% 19.61/2.99  --inst_solver_per_active                1400
% 19.61/2.99  --inst_solver_calls_frac                1.
% 19.61/2.99  --inst_passive_queue_type               priority_queues
% 19.61/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.61/2.99  --inst_passive_queues_freq              [25;2]
% 19.61/2.99  --inst_dismatching                      true
% 19.61/2.99  --inst_eager_unprocessed_to_passive     true
% 19.61/2.99  --inst_prop_sim_given                   true
% 19.61/2.99  --inst_prop_sim_new                     false
% 19.61/2.99  --inst_subs_new                         false
% 19.61/2.99  --inst_eq_res_simp                      false
% 19.61/2.99  --inst_subs_given                       false
% 19.61/2.99  --inst_orphan_elimination               true
% 19.61/2.99  --inst_learning_loop_flag               true
% 19.61/2.99  --inst_learning_start                   3000
% 19.61/2.99  --inst_learning_factor                  2
% 19.61/2.99  --inst_start_prop_sim_after_learn       3
% 19.61/2.99  --inst_sel_renew                        solver
% 19.61/2.99  --inst_lit_activity_flag                true
% 19.61/2.99  --inst_restr_to_given                   false
% 19.61/2.99  --inst_activity_threshold               500
% 19.61/2.99  --inst_out_proof                        true
% 19.61/2.99  
% 19.61/2.99  ------ Resolution Options
% 19.61/2.99  
% 19.61/2.99  --resolution_flag                       true
% 19.61/2.99  --res_lit_sel                           adaptive
% 19.61/2.99  --res_lit_sel_side                      none
% 19.61/2.99  --res_ordering                          kbo
% 19.61/2.99  --res_to_prop_solver                    active
% 19.61/2.99  --res_prop_simpl_new                    false
% 19.61/2.99  --res_prop_simpl_given                  true
% 19.61/2.99  --res_passive_queue_type                priority_queues
% 19.61/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.61/2.99  --res_passive_queues_freq               [15;5]
% 19.61/2.99  --res_forward_subs                      full
% 19.61/2.99  --res_backward_subs                     full
% 19.61/2.99  --res_forward_subs_resolution           true
% 19.61/2.99  --res_backward_subs_resolution          true
% 19.61/2.99  --res_orphan_elimination                true
% 19.61/2.99  --res_time_limit                        2.
% 19.61/2.99  --res_out_proof                         true
% 19.61/2.99  
% 19.61/2.99  ------ Superposition Options
% 19.61/2.99  
% 19.61/2.99  --superposition_flag                    true
% 19.61/2.99  --sup_passive_queue_type                priority_queues
% 19.61/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.61/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.61/2.99  --demod_completeness_check              fast
% 19.61/2.99  --demod_use_ground                      true
% 19.61/2.99  --sup_to_prop_solver                    passive
% 19.61/2.99  --sup_prop_simpl_new                    true
% 19.61/2.99  --sup_prop_simpl_given                  true
% 19.61/2.99  --sup_fun_splitting                     true
% 19.61/2.99  --sup_smt_interval                      50000
% 19.61/2.99  
% 19.61/2.99  ------ Superposition Simplification Setup
% 19.61/2.99  
% 19.61/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.61/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.61/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.61/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.61/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.61/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.61/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.61/2.99  --sup_immed_triv                        [TrivRules]
% 19.61/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.61/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.61/2.99  --sup_immed_bw_main                     []
% 19.61/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.61/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.61/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.61/2.99  --sup_input_bw                          []
% 19.61/2.99  
% 19.61/2.99  ------ Combination Options
% 19.61/2.99  
% 19.61/2.99  --comb_res_mult                         3
% 19.61/2.99  --comb_sup_mult                         2
% 19.61/2.99  --comb_inst_mult                        10
% 19.61/2.99  
% 19.61/2.99  ------ Debug Options
% 19.61/2.99  
% 19.61/2.99  --dbg_backtrace                         false
% 19.61/2.99  --dbg_dump_prop_clauses                 false
% 19.61/2.99  --dbg_dump_prop_clauses_file            -
% 19.61/2.99  --dbg_out_stat                          false
% 19.61/2.99  ------ Parsing...
% 19.61/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.61/2.99  
% 19.61/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.61/2.99  
% 19.61/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.61/2.99  
% 19.61/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.61/2.99  ------ Proving...
% 19.61/2.99  ------ Problem Properties 
% 19.61/2.99  
% 19.61/2.99  
% 19.61/2.99  clauses                                 36
% 19.61/2.99  conjectures                             5
% 19.61/2.99  EPR                                     10
% 19.61/2.99  Horn                                    33
% 19.61/2.99  unary                                   9
% 19.61/2.99  binary                                  11
% 19.61/2.99  lits                                    89
% 19.61/2.99  lits eq                                 24
% 19.61/2.99  fd_pure                                 0
% 19.61/2.99  fd_pseudo                               0
% 19.61/2.99  fd_cond                                 0
% 19.61/2.99  fd_pseudo_cond                          1
% 19.61/2.99  AC symbols                              0
% 19.61/2.99  
% 19.61/2.99  ------ Schedule dynamic 5 is on 
% 19.61/2.99  
% 19.61/2.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.61/2.99  
% 19.61/2.99  
% 19.61/2.99  ------ 
% 19.61/2.99  Current options:
% 19.61/2.99  ------ 
% 19.61/2.99  
% 19.61/2.99  ------ Input Options
% 19.61/2.99  
% 19.61/2.99  --out_options                           all
% 19.61/2.99  --tptp_safe_out                         true
% 19.61/2.99  --problem_path                          ""
% 19.61/2.99  --include_path                          ""
% 19.61/2.99  --clausifier                            res/vclausify_rel
% 19.61/2.99  --clausifier_options                    ""
% 19.61/2.99  --stdin                                 false
% 19.61/2.99  --stats_out                             all
% 19.61/2.99  
% 19.61/2.99  ------ General Options
% 19.61/2.99  
% 19.61/2.99  --fof                                   false
% 19.61/2.99  --time_out_real                         305.
% 19.61/2.99  --time_out_virtual                      -1.
% 19.61/2.99  --symbol_type_check                     false
% 19.61/2.99  --clausify_out                          false
% 19.61/2.99  --sig_cnt_out                           false
% 19.61/2.99  --trig_cnt_out                          false
% 19.61/2.99  --trig_cnt_out_tolerance                1.
% 19.61/2.99  --trig_cnt_out_sk_spl                   false
% 19.61/2.99  --abstr_cl_out                          false
% 19.61/2.99  
% 19.61/2.99  ------ Global Options
% 19.61/2.99  
% 19.61/2.99  --schedule                              default
% 19.61/2.99  --add_important_lit                     false
% 19.61/2.99  --prop_solver_per_cl                    1000
% 19.61/2.99  --min_unsat_core                        false
% 19.61/2.99  --soft_assumptions                      false
% 19.61/2.99  --soft_lemma_size                       3
% 19.61/2.99  --prop_impl_unit_size                   0
% 19.61/2.99  --prop_impl_unit                        []
% 19.61/2.99  --share_sel_clauses                     true
% 19.61/2.99  --reset_solvers                         false
% 19.61/2.99  --bc_imp_inh                            [conj_cone]
% 19.61/2.99  --conj_cone_tolerance                   3.
% 19.61/2.99  --extra_neg_conj                        none
% 19.61/2.99  --large_theory_mode                     true
% 19.61/2.99  --prolific_symb_bound                   200
% 19.61/2.99  --lt_threshold                          2000
% 19.61/2.99  --clause_weak_htbl                      true
% 19.61/2.99  --gc_record_bc_elim                     false
% 19.61/2.99  
% 19.61/2.99  ------ Preprocessing Options
% 19.61/2.99  
% 19.61/2.99  --preprocessing_flag                    true
% 19.61/2.99  --time_out_prep_mult                    0.1
% 19.61/2.99  --splitting_mode                        input
% 19.61/2.99  --splitting_grd                         true
% 19.61/2.99  --splitting_cvd                         false
% 19.61/2.99  --splitting_cvd_svl                     false
% 19.61/2.99  --splitting_nvd                         32
% 19.61/2.99  --sub_typing                            true
% 19.61/2.99  --prep_gs_sim                           true
% 19.61/2.99  --prep_unflatten                        true
% 19.61/2.99  --prep_res_sim                          true
% 19.61/2.99  --prep_upred                            true
% 19.61/2.99  --prep_sem_filter                       exhaustive
% 19.61/2.99  --prep_sem_filter_out                   false
% 19.61/2.99  --pred_elim                             true
% 19.61/2.99  --res_sim_input                         true
% 19.61/2.99  --eq_ax_congr_red                       true
% 19.61/2.99  --pure_diseq_elim                       true
% 19.61/2.99  --brand_transform                       false
% 19.61/2.99  --non_eq_to_eq                          false
% 19.61/2.99  --prep_def_merge                        true
% 19.61/2.99  --prep_def_merge_prop_impl              false
% 19.61/2.99  --prep_def_merge_mbd                    true
% 19.61/2.99  --prep_def_merge_tr_red                 false
% 19.61/2.99  --prep_def_merge_tr_cl                  false
% 19.61/2.99  --smt_preprocessing                     true
% 19.61/2.99  --smt_ac_axioms                         fast
% 19.61/2.99  --preprocessed_out                      false
% 19.61/2.99  --preprocessed_stats                    false
% 19.61/2.99  
% 19.61/2.99  ------ Abstraction refinement Options
% 19.61/2.99  
% 19.61/2.99  --abstr_ref                             []
% 19.61/2.99  --abstr_ref_prep                        false
% 19.61/2.99  --abstr_ref_until_sat                   false
% 19.61/2.99  --abstr_ref_sig_restrict                funpre
% 19.61/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.61/2.99  --abstr_ref_under                       []
% 19.61/2.99  
% 19.61/2.99  ------ SAT Options
% 19.61/2.99  
% 19.61/2.99  --sat_mode                              false
% 19.61/2.99  --sat_fm_restart_options                ""
% 19.61/2.99  --sat_gr_def                            false
% 19.61/2.99  --sat_epr_types                         true
% 19.61/2.99  --sat_non_cyclic_types                  false
% 19.61/2.99  --sat_finite_models                     false
% 19.61/2.99  --sat_fm_lemmas                         false
% 19.61/2.99  --sat_fm_prep                           false
% 19.61/2.99  --sat_fm_uc_incr                        true
% 19.61/2.99  --sat_out_model                         small
% 19.61/2.99  --sat_out_clauses                       false
% 19.61/2.99  
% 19.61/2.99  ------ QBF Options
% 19.61/2.99  
% 19.61/2.99  --qbf_mode                              false
% 19.61/2.99  --qbf_elim_univ                         false
% 19.61/2.99  --qbf_dom_inst                          none
% 19.61/2.99  --qbf_dom_pre_inst                      false
% 19.61/2.99  --qbf_sk_in                             false
% 19.61/2.99  --qbf_pred_elim                         true
% 19.61/2.99  --qbf_split                             512
% 19.61/2.99  
% 19.61/2.99  ------ BMC1 Options
% 19.61/2.99  
% 19.61/2.99  --bmc1_incremental                      false
% 19.61/2.99  --bmc1_axioms                           reachable_all
% 19.61/2.99  --bmc1_min_bound                        0
% 19.61/2.99  --bmc1_max_bound                        -1
% 19.61/2.99  --bmc1_max_bound_default                -1
% 19.61/2.99  --bmc1_symbol_reachability              true
% 19.61/2.99  --bmc1_property_lemmas                  false
% 19.61/2.99  --bmc1_k_induction                      false
% 19.61/2.99  --bmc1_non_equiv_states                 false
% 19.61/2.99  --bmc1_deadlock                         false
% 19.61/2.99  --bmc1_ucm                              false
% 19.61/2.99  --bmc1_add_unsat_core                   none
% 19.61/2.99  --bmc1_unsat_core_children              false
% 19.61/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.61/2.99  --bmc1_out_stat                         full
% 19.61/2.99  --bmc1_ground_init                      false
% 19.61/2.99  --bmc1_pre_inst_next_state              false
% 19.61/2.99  --bmc1_pre_inst_state                   false
% 19.61/2.99  --bmc1_pre_inst_reach_state             false
% 19.61/2.99  --bmc1_out_unsat_core                   false
% 19.61/2.99  --bmc1_aig_witness_out                  false
% 19.61/2.99  --bmc1_verbose                          false
% 19.61/2.99  --bmc1_dump_clauses_tptp                false
% 19.61/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.61/2.99  --bmc1_dump_file                        -
% 19.61/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.61/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.61/2.99  --bmc1_ucm_extend_mode                  1
% 19.61/2.99  --bmc1_ucm_init_mode                    2
% 19.61/2.99  --bmc1_ucm_cone_mode                    none
% 19.61/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.61/2.99  --bmc1_ucm_relax_model                  4
% 19.61/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.61/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.61/2.99  --bmc1_ucm_layered_model                none
% 19.61/2.99  --bmc1_ucm_max_lemma_size               10
% 19.61/2.99  
% 19.61/2.99  ------ AIG Options
% 19.61/2.99  
% 19.61/2.99  --aig_mode                              false
% 19.61/2.99  
% 19.61/2.99  ------ Instantiation Options
% 19.61/2.99  
% 19.61/2.99  --instantiation_flag                    true
% 19.61/2.99  --inst_sos_flag                         true
% 19.61/2.99  --inst_sos_phase                        true
% 19.61/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.61/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.61/2.99  --inst_lit_sel_side                     none
% 19.61/2.99  --inst_solver_per_active                1400
% 19.61/2.99  --inst_solver_calls_frac                1.
% 19.61/2.99  --inst_passive_queue_type               priority_queues
% 19.61/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.61/2.99  --inst_passive_queues_freq              [25;2]
% 19.61/2.99  --inst_dismatching                      true
% 19.61/2.99  --inst_eager_unprocessed_to_passive     true
% 19.61/2.99  --inst_prop_sim_given                   true
% 19.61/2.99  --inst_prop_sim_new                     false
% 19.61/2.99  --inst_subs_new                         false
% 19.61/2.99  --inst_eq_res_simp                      false
% 19.61/2.99  --inst_subs_given                       false
% 19.61/2.99  --inst_orphan_elimination               true
% 19.61/2.99  --inst_learning_loop_flag               true
% 19.61/2.99  --inst_learning_start                   3000
% 19.61/2.99  --inst_learning_factor                  2
% 19.61/2.99  --inst_start_prop_sim_after_learn       3
% 19.61/2.99  --inst_sel_renew                        solver
% 19.61/2.99  --inst_lit_activity_flag                true
% 19.61/2.99  --inst_restr_to_given                   false
% 19.61/2.99  --inst_activity_threshold               500
% 19.61/2.99  --inst_out_proof                        true
% 19.61/2.99  
% 19.61/2.99  ------ Resolution Options
% 19.61/2.99  
% 19.61/2.99  --resolution_flag                       false
% 19.61/2.99  --res_lit_sel                           adaptive
% 19.61/2.99  --res_lit_sel_side                      none
% 19.61/2.99  --res_ordering                          kbo
% 19.61/2.99  --res_to_prop_solver                    active
% 19.61/2.99  --res_prop_simpl_new                    false
% 19.61/2.99  --res_prop_simpl_given                  true
% 19.61/2.99  --res_passive_queue_type                priority_queues
% 19.61/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.61/2.99  --res_passive_queues_freq               [15;5]
% 19.61/2.99  --res_forward_subs                      full
% 19.61/2.99  --res_backward_subs                     full
% 19.61/2.99  --res_forward_subs_resolution           true
% 19.61/2.99  --res_backward_subs_resolution          true
% 19.61/2.99  --res_orphan_elimination                true
% 19.61/2.99  --res_time_limit                        2.
% 19.61/2.99  --res_out_proof                         true
% 19.61/2.99  
% 19.61/2.99  ------ Superposition Options
% 19.61/2.99  
% 19.61/2.99  --superposition_flag                    true
% 19.61/2.99  --sup_passive_queue_type                priority_queues
% 19.61/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.61/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.61/2.99  --demod_completeness_check              fast
% 19.61/2.99  --demod_use_ground                      true
% 19.61/2.99  --sup_to_prop_solver                    passive
% 19.61/2.99  --sup_prop_simpl_new                    true
% 19.61/2.99  --sup_prop_simpl_given                  true
% 19.61/2.99  --sup_fun_splitting                     true
% 19.61/2.99  --sup_smt_interval                      50000
% 19.61/2.99  
% 19.61/2.99  ------ Superposition Simplification Setup
% 19.61/2.99  
% 19.61/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.61/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.61/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.61/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.61/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.61/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.61/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.61/2.99  --sup_immed_triv                        [TrivRules]
% 19.61/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.61/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.61/2.99  --sup_immed_bw_main                     []
% 19.61/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.61/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.61/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.61/2.99  --sup_input_bw                          []
% 19.61/2.99  
% 19.61/2.99  ------ Combination Options
% 19.61/2.99  
% 19.61/2.99  --comb_res_mult                         3
% 19.61/2.99  --comb_sup_mult                         2
% 19.61/2.99  --comb_inst_mult                        10
% 19.61/2.99  
% 19.61/2.99  ------ Debug Options
% 19.61/2.99  
% 19.61/2.99  --dbg_backtrace                         false
% 19.61/2.99  --dbg_dump_prop_clauses                 false
% 19.61/2.99  --dbg_dump_prop_clauses_file            -
% 19.61/2.99  --dbg_out_stat                          false
% 19.61/2.99  
% 19.61/2.99  
% 19.61/2.99  
% 19.61/2.99  
% 19.61/2.99  ------ Proving...
% 19.61/2.99  
% 19.61/2.99  
% 19.61/2.99  % SZS status Theorem for theBenchmark.p
% 19.61/2.99  
% 19.61/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.61/2.99  
% 19.61/2.99  fof(f6,axiom,(
% 19.61/2.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f26,plain,(
% 19.61/2.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 19.61/2.99    inference(ennf_transformation,[],[f6])).
% 19.61/2.99  
% 19.61/2.99  fof(f70,plain,(
% 19.61/2.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 19.61/2.99    inference(cnf_transformation,[],[f26])).
% 19.61/2.99  
% 19.61/2.99  fof(f5,axiom,(
% 19.61/2.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f55,plain,(
% 19.61/2.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.61/2.99    inference(nnf_transformation,[],[f5])).
% 19.61/2.99  
% 19.61/2.99  fof(f69,plain,(
% 19.61/2.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.61/2.99    inference(cnf_transformation,[],[f55])).
% 19.61/2.99  
% 19.61/2.99  fof(f22,conjecture,(
% 19.61/2.99    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f23,negated_conjecture,(
% 19.61/2.99    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 19.61/2.99    inference(negated_conjecture,[],[f22])).
% 19.61/2.99  
% 19.61/2.99  fof(f47,plain,(
% 19.61/2.99    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 19.61/2.99    inference(ennf_transformation,[],[f23])).
% 19.61/2.99  
% 19.61/2.99  fof(f48,plain,(
% 19.61/2.99    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 19.61/2.99    inference(flattening,[],[f47])).
% 19.61/2.99  
% 19.61/2.99  fof(f58,plain,(
% 19.61/2.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(X0,X3,sK5,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,sK5,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,sK5,X1))) & r1_tarski(k7_relset_1(X0,X3,sK5,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(sK5,X0,X3) & v1_funct_1(sK5))) )),
% 19.61/2.99    introduced(choice_axiom,[])).
% 19.61/2.99  
% 19.61/2.99  fof(f57,plain,(
% 19.61/2.99    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK1,sK4,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(k2_partfun1(sK1,sK4,X4,sK2),sK2,sK3) | ~v1_funct_1(k2_partfun1(sK1,sK4,X4,sK2))) & r1_tarski(k7_relset_1(sK1,sK4,X4,sK2),sK3) & r1_tarski(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) & v1_funct_2(X4,sK1,sK4) & v1_funct_1(X4)) & ~v1_xboole_0(sK4))),
% 19.61/2.99    introduced(choice_axiom,[])).
% 19.61/2.99  
% 19.61/2.99  fof(f59,plain,(
% 19.61/2.99    ((~m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3) | ~v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))) & r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) & r1_tarski(sK2,sK1) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) & v1_funct_2(sK5,sK1,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 19.61/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f48,f58,f57])).
% 19.61/2.99  
% 19.61/2.99  fof(f95,plain,(
% 19.61/2.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))),
% 19.61/2.99    inference(cnf_transformation,[],[f59])).
% 19.61/2.99  
% 19.61/2.99  fof(f21,axiom,(
% 19.61/2.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f45,plain,(
% 19.61/2.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 19.61/2.99    inference(ennf_transformation,[],[f21])).
% 19.61/2.99  
% 19.61/2.99  fof(f46,plain,(
% 19.61/2.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 19.61/2.99    inference(flattening,[],[f45])).
% 19.61/2.99  
% 19.61/2.99  fof(f91,plain,(
% 19.61/2.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.61/2.99    inference(cnf_transformation,[],[f46])).
% 19.61/2.99  
% 19.61/2.99  fof(f93,plain,(
% 19.61/2.99    v1_funct_1(sK5)),
% 19.61/2.99    inference(cnf_transformation,[],[f59])).
% 19.61/2.99  
% 19.61/2.99  fof(f20,axiom,(
% 19.61/2.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f43,plain,(
% 19.61/2.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 19.61/2.99    inference(ennf_transformation,[],[f20])).
% 19.61/2.99  
% 19.61/2.99  fof(f44,plain,(
% 19.61/2.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 19.61/2.99    inference(flattening,[],[f43])).
% 19.61/2.99  
% 19.61/2.99  fof(f90,plain,(
% 19.61/2.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.61/2.99    inference(cnf_transformation,[],[f44])).
% 19.61/2.99  
% 19.61/2.99  fof(f13,axiom,(
% 19.61/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f34,plain,(
% 19.61/2.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.61/2.99    inference(ennf_transformation,[],[f13])).
% 19.61/2.99  
% 19.61/2.99  fof(f77,plain,(
% 19.61/2.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.61/2.99    inference(cnf_transformation,[],[f34])).
% 19.61/2.99  
% 19.61/2.99  fof(f18,axiom,(
% 19.61/2.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f39,plain,(
% 19.61/2.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 19.61/2.99    inference(ennf_transformation,[],[f18])).
% 19.61/2.99  
% 19.61/2.99  fof(f40,plain,(
% 19.61/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 19.61/2.99    inference(flattening,[],[f39])).
% 19.61/2.99  
% 19.61/2.99  fof(f82,plain,(
% 19.61/2.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 19.61/2.99    inference(cnf_transformation,[],[f40])).
% 19.61/2.99  
% 19.61/2.99  fof(f17,axiom,(
% 19.61/2.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f38,plain,(
% 19.61/2.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.61/2.99    inference(ennf_transformation,[],[f17])).
% 19.61/2.99  
% 19.61/2.99  fof(f81,plain,(
% 19.61/2.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.61/2.99    inference(cnf_transformation,[],[f38])).
% 19.61/2.99  
% 19.61/2.99  fof(f97,plain,(
% 19.61/2.99    r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3)),
% 19.61/2.99    inference(cnf_transformation,[],[f59])).
% 19.61/2.99  
% 19.61/2.99  fof(f9,axiom,(
% 19.61/2.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f28,plain,(
% 19.61/2.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 19.61/2.99    inference(ennf_transformation,[],[f9])).
% 19.61/2.99  
% 19.61/2.99  fof(f73,plain,(
% 19.61/2.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.61/2.99    inference(cnf_transformation,[],[f28])).
% 19.61/2.99  
% 19.61/2.99  fof(f3,axiom,(
% 19.61/2.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f53,plain,(
% 19.61/2.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.61/2.99    inference(nnf_transformation,[],[f3])).
% 19.61/2.99  
% 19.61/2.99  fof(f54,plain,(
% 19.61/2.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.61/2.99    inference(flattening,[],[f53])).
% 19.61/2.99  
% 19.61/2.99  fof(f64,plain,(
% 19.61/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.61/2.99    inference(cnf_transformation,[],[f54])).
% 19.61/2.99  
% 19.61/2.99  fof(f100,plain,(
% 19.61/2.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.61/2.99    inference(equality_resolution,[],[f64])).
% 19.61/2.99  
% 19.61/2.99  fof(f16,axiom,(
% 19.61/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f37,plain,(
% 19.61/2.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.61/2.99    inference(ennf_transformation,[],[f16])).
% 19.61/2.99  
% 19.61/2.99  fof(f80,plain,(
% 19.61/2.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.61/2.99    inference(cnf_transformation,[],[f37])).
% 19.61/2.99  
% 19.61/2.99  fof(f96,plain,(
% 19.61/2.99    r1_tarski(sK2,sK1)),
% 19.61/2.99    inference(cnf_transformation,[],[f59])).
% 19.61/2.99  
% 19.61/2.99  fof(f19,axiom,(
% 19.61/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f41,plain,(
% 19.61/2.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.61/2.99    inference(ennf_transformation,[],[f19])).
% 19.61/2.99  
% 19.61/2.99  fof(f42,plain,(
% 19.61/2.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.61/2.99    inference(flattening,[],[f41])).
% 19.61/2.99  
% 19.61/2.99  fof(f56,plain,(
% 19.61/2.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.61/2.99    inference(nnf_transformation,[],[f42])).
% 19.61/2.99  
% 19.61/2.99  fof(f83,plain,(
% 19.61/2.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.61/2.99    inference(cnf_transformation,[],[f56])).
% 19.61/2.99  
% 19.61/2.99  fof(f94,plain,(
% 19.61/2.99    v1_funct_2(sK5,sK1,sK4)),
% 19.61/2.99    inference(cnf_transformation,[],[f59])).
% 19.61/2.99  
% 19.61/2.99  fof(f92,plain,(
% 19.61/2.99    ~v1_xboole_0(sK4)),
% 19.61/2.99    inference(cnf_transformation,[],[f59])).
% 19.61/2.99  
% 19.61/2.99  fof(f2,axiom,(
% 19.61/2.99    v1_xboole_0(k1_xboole_0)),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f63,plain,(
% 19.61/2.99    v1_xboole_0(k1_xboole_0)),
% 19.61/2.99    inference(cnf_transformation,[],[f2])).
% 19.61/2.99  
% 19.61/2.99  fof(f12,axiom,(
% 19.61/2.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f32,plain,(
% 19.61/2.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 19.61/2.99    inference(ennf_transformation,[],[f12])).
% 19.61/2.99  
% 19.61/2.99  fof(f33,plain,(
% 19.61/2.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 19.61/2.99    inference(flattening,[],[f32])).
% 19.61/2.99  
% 19.61/2.99  fof(f76,plain,(
% 19.61/2.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 19.61/2.99    inference(cnf_transformation,[],[f33])).
% 19.61/2.99  
% 19.61/2.99  fof(f85,plain,(
% 19.61/2.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.61/2.99    inference(cnf_transformation,[],[f56])).
% 19.61/2.99  
% 19.61/2.99  fof(f98,plain,(
% 19.61/2.99    ~m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3) | ~v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))),
% 19.61/2.99    inference(cnf_transformation,[],[f59])).
% 19.61/2.99  
% 19.61/2.99  fof(f89,plain,(
% 19.61/2.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.61/2.99    inference(cnf_transformation,[],[f44])).
% 19.61/2.99  
% 19.61/2.99  fof(f1,axiom,(
% 19.61/2.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f25,plain,(
% 19.61/2.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 19.61/2.99    inference(ennf_transformation,[],[f1])).
% 19.61/2.99  
% 19.61/2.99  fof(f49,plain,(
% 19.61/2.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 19.61/2.99    inference(nnf_transformation,[],[f25])).
% 19.61/2.99  
% 19.61/2.99  fof(f50,plain,(
% 19.61/2.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.61/2.99    inference(rectify,[],[f49])).
% 19.61/2.99  
% 19.61/2.99  fof(f51,plain,(
% 19.61/2.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.61/2.99    introduced(choice_axiom,[])).
% 19.61/2.99  
% 19.61/2.99  fof(f52,plain,(
% 19.61/2.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.61/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).
% 19.61/2.99  
% 19.61/2.99  fof(f61,plain,(
% 19.61/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 19.61/2.99    inference(cnf_transformation,[],[f52])).
% 19.61/2.99  
% 19.61/2.99  fof(f15,axiom,(
% 19.61/2.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f36,plain,(
% 19.61/2.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 19.61/2.99    inference(ennf_transformation,[],[f15])).
% 19.61/2.99  
% 19.61/2.99  fof(f79,plain,(
% 19.61/2.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 19.61/2.99    inference(cnf_transformation,[],[f36])).
% 19.61/2.99  
% 19.61/2.99  fof(f4,axiom,(
% 19.61/2.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f67,plain,(
% 19.61/2.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 19.61/2.99    inference(cnf_transformation,[],[f4])).
% 19.61/2.99  
% 19.61/2.99  fof(f14,axiom,(
% 19.61/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f24,plain,(
% 19.61/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 19.61/2.99    inference(pure_predicate_removal,[],[f14])).
% 19.61/2.99  
% 19.61/2.99  fof(f35,plain,(
% 19.61/2.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.61/2.99    inference(ennf_transformation,[],[f24])).
% 19.61/2.99  
% 19.61/2.99  fof(f78,plain,(
% 19.61/2.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.61/2.99    inference(cnf_transformation,[],[f35])).
% 19.61/2.99  
% 19.61/2.99  fof(f10,axiom,(
% 19.61/2.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 19.61/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/2.99  
% 19.61/2.99  fof(f29,plain,(
% 19.61/2.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 19.61/2.99    inference(ennf_transformation,[],[f10])).
% 19.61/2.99  
% 19.61/2.99  fof(f30,plain,(
% 19.61/2.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 19.61/2.99    inference(flattening,[],[f29])).
% 19.61/2.99  
% 19.61/2.99  fof(f74,plain,(
% 19.61/2.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.61/2.99    inference(cnf_transformation,[],[f30])).
% 19.61/2.99  
% 19.61/2.99  fof(f68,plain,(
% 19.61/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.61/2.99    inference(cnf_transformation,[],[f55])).
% 19.61/2.99  
% 19.61/2.99  fof(f66,plain,(
% 19.61/2.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.61/2.99    inference(cnf_transformation,[],[f54])).
% 19.61/2.99  
% 19.61/2.99  fof(f86,plain,(
% 19.61/2.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.61/2.99    inference(cnf_transformation,[],[f56])).
% 19.61/2.99  
% 19.61/2.99  fof(f104,plain,(
% 19.61/2.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 19.61/2.99    inference(equality_resolution,[],[f86])).
% 19.61/2.99  
% 19.61/2.99  fof(f88,plain,(
% 19.61/2.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.61/2.99    inference(cnf_transformation,[],[f56])).
% 19.61/2.99  
% 19.61/2.99  fof(f101,plain,(
% 19.61/2.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.61/2.99    inference(equality_resolution,[],[f88])).
% 19.61/2.99  
% 19.61/2.99  fof(f102,plain,(
% 19.61/2.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 19.61/2.99    inference(equality_resolution,[],[f101])).
% 19.61/2.99  
% 19.61/2.99  cnf(c_999,plain,
% 19.61/2.99      ( X0 != X1
% 19.61/2.99      | X2 != X3
% 19.61/2.99      | X4 != X5
% 19.61/2.99      | k1_relset_1(X0,X2,X4) = k1_relset_1(X1,X3,X5) ),
% 19.61/2.99      theory(equality) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_66671,plain,
% 19.61/2.99      ( k2_partfun1(sK1,sK4,sK5,sK2) != X0
% 19.61/2.99      | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_relset_1(X1,X2,X0)
% 19.61/2.99      | sK3 != X2
% 19.61/2.99      | k1_xboole_0 != X1 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_999]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_66673,plain,
% 19.61/2.99      ( k2_partfun1(sK1,sK4,sK5,sK2) != k1_xboole_0
% 19.61/2.99      | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 19.61/2.99      | sK3 != k1_xboole_0
% 19.61/2.99      | k1_xboole_0 != k1_xboole_0 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_66671]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_992,plain,
% 19.61/2.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 19.61/2.99      theory(equality) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_48523,plain,
% 19.61/2.99      ( ~ v1_xboole_0(X0)
% 19.61/2.99      | v1_xboole_0(k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | k2_partfun1(sK1,sK4,sK5,sK2) != X0 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_992]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_51965,plain,
% 19.61/2.99      ( v1_xboole_0(k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | ~ v1_xboole_0(k7_relat_1(sK5,sK2))
% 19.61/2.99      | k2_partfun1(sK1,sK4,sK5,sK2) != k7_relat_1(sK5,sK2) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_48523]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_10,plain,
% 19.61/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.61/2.99      | ~ r2_hidden(X2,X0)
% 19.61/2.99      | ~ v1_xboole_0(X1) ),
% 19.61/2.99      inference(cnf_transformation,[],[f70]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_8,plain,
% 19.61/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.61/2.99      inference(cnf_transformation,[],[f69]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_293,plain,
% 19.61/2.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.61/2.99      inference(prop_impl,[status(thm)],[c_8]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_294,plain,
% 19.61/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.61/2.99      inference(renaming,[status(thm)],[c_293]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_361,plain,
% 19.61/2.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 19.61/2.99      inference(bin_hyper_res,[status(thm)],[c_10,c_294]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_46498,plain,
% 19.61/2.99      ( ~ r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0),k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),X0)
% 19.61/2.99      | ~ v1_xboole_0(X0) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_361]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_47270,plain,
% 19.61/2.99      ( ~ r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0),k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | ~ v1_xboole_0(k2_partfun1(sK1,sK4,sK5,sK2)) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_46498]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_989,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_42263,plain,
% 19.61/2.99      ( k1_relset_1(X0,X1,X2) != X3
% 19.61/2.99      | k1_xboole_0 != X3
% 19.61/2.99      | k1_xboole_0 = k1_relset_1(X0,X1,X2) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_989]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_42264,plain,
% 19.61/2.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 19.61/2.99      | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 19.61/2.99      | k1_xboole_0 != k1_xboole_0 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_42263]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_996,plain,
% 19.61/2.99      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 19.61/2.99      theory(equality) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_39942,plain,
% 19.61/2.99      ( k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(X0,X1)
% 19.61/2.99      | sK3 != X1
% 19.61/2.99      | k1_xboole_0 != X0 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_996]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_39943,plain,
% 19.61/2.99      ( k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 19.61/2.99      | sK3 != k1_xboole_0
% 19.61/2.99      | k1_xboole_0 != k1_xboole_0 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_39942]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_994,plain,
% 19.61/2.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.61/2.99      theory(equality) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3209,plain,
% 19.61/2.99      ( m1_subset_1(X0,X1)
% 19.61/2.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 19.61/2.99      | X1 != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 19.61/2.99      | X0 != sK3 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_994]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_36943,plain,
% 19.61/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | X0 != sK3
% 19.61/2.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_3209]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_36944,plain,
% 19.61/2.99      ( X0 != sK3
% 19.61/2.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 19.61/2.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 19.61/2.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_36943]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_36946,plain,
% 19.61/2.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 19.61/2.99      | k1_xboole_0 != sK3
% 19.61/2.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 19.61/2.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_36944]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_35,negated_conjecture,
% 19.61/2.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) ),
% 19.61/2.99      inference(cnf_transformation,[],[f95]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1776,plain,
% 19.61/2.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_31,plain,
% 19.61/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | ~ v1_funct_1(X0)
% 19.61/2.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 19.61/2.99      inference(cnf_transformation,[],[f91]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1779,plain,
% 19.61/2.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 19.61/2.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.61/2.99      | v1_funct_1(X2) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3662,plain,
% 19.61/2.99      ( k2_partfun1(sK1,sK4,sK5,X0) = k7_relat_1(sK5,X0)
% 19.61/2.99      | v1_funct_1(sK5) != iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1776,c_1779]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_37,negated_conjecture,
% 19.61/2.99      ( v1_funct_1(sK5) ),
% 19.61/2.99      inference(cnf_transformation,[],[f93]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_40,plain,
% 19.61/2.99      ( v1_funct_1(sK5) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3814,plain,
% 19.61/2.99      ( k2_partfun1(sK1,sK4,sK5,X0) = k7_relat_1(sK5,X0) ),
% 19.61/2.99      inference(global_propositional_subsumption,
% 19.61/2.99                [status(thm)],
% 19.61/2.99                [c_3662,c_40]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_29,plain,
% 19.61/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | ~ v1_funct_1(X0) ),
% 19.61/2.99      inference(cnf_transformation,[],[f90]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1781,plain,
% 19.61/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.61/2.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 19.61/2.99      | v1_funct_1(X0) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4247,plain,
% 19.61/2.99      ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top
% 19.61/2.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) != iProver_top
% 19.61/2.99      | v1_funct_1(sK5) != iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_3814,c_1781]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_42,plain,
% 19.61/2.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4688,plain,
% 19.61/2.99      ( m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) = iProver_top ),
% 19.61/2.99      inference(global_propositional_subsumption,
% 19.61/2.99                [status(thm)],
% 19.61/2.99                [c_4247,c_40,c_42]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_17,plain,
% 19.61/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | v1_relat_1(X0) ),
% 19.61/2.99      inference(cnf_transformation,[],[f77]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1786,plain,
% 19.61/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.61/2.99      | v1_relat_1(X0) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4699,plain,
% 19.61/2.99      ( v1_relat_1(k7_relat_1(sK5,X0)) = iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_4688,c_1786]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_22,plain,
% 19.61/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 19.61/2.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 19.61/2.99      | ~ v1_relat_1(X0) ),
% 19.61/2.99      inference(cnf_transformation,[],[f82]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1782,plain,
% 19.61/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 19.61/2.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 19.61/2.99      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 19.61/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_21,plain,
% 19.61/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 19.61/2.99      inference(cnf_transformation,[],[f81]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1783,plain,
% 19.61/2.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 19.61/2.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3236,plain,
% 19.61/2.99      ( k7_relset_1(sK1,sK4,sK5,X0) = k9_relat_1(sK5,X0) ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1776,c_1783]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_33,negated_conjecture,
% 19.61/2.99      ( r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) ),
% 19.61/2.99      inference(cnf_transformation,[],[f97]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1778,plain,
% 19.61/2.99      ( r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3272,plain,
% 19.61/2.99      ( r1_tarski(k9_relat_1(sK5,sK2),sK3) = iProver_top ),
% 19.61/2.99      inference(demodulation,[status(thm)],[c_3236,c_1778]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2572,plain,
% 19.61/2.99      ( v1_relat_1(sK5) = iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1776,c_1786]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_13,plain,
% 19.61/2.99      ( ~ v1_relat_1(X0)
% 19.61/2.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 19.61/2.99      inference(cnf_transformation,[],[f73]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1789,plain,
% 19.61/2.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 19.61/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2798,plain,
% 19.61/2.99      ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_2572,c_1789]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_6,plain,
% 19.61/2.99      ( r1_tarski(X0,X0) ),
% 19.61/2.99      inference(cnf_transformation,[],[f100]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1794,plain,
% 19.61/2.99      ( r1_tarski(X0,X0) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_20,plain,
% 19.61/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 19.61/2.99      inference(cnf_transformation,[],[f80]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1784,plain,
% 19.61/2.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 19.61/2.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4404,plain,
% 19.61/2.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 19.61/2.99      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 19.61/2.99      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 19.61/2.99      | v1_relat_1(X2) != iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1782,c_1784]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_21096,plain,
% 19.61/2.99      ( k1_relset_1(k1_relat_1(X0),X1,X0) = k1_relat_1(X0)
% 19.61/2.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 19.61/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1794,c_4404]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_21318,plain,
% 19.61/2.99      ( k1_relset_1(k1_relat_1(k7_relat_1(sK5,X0)),X1,k7_relat_1(sK5,X0)) = k1_relat_1(k7_relat_1(sK5,X0))
% 19.61/2.99      | r1_tarski(k9_relat_1(sK5,X0),X1) != iProver_top
% 19.61/2.99      | v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_2798,c_21096]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_28702,plain,
% 19.61/2.99      ( r1_tarski(k9_relat_1(sK5,X0),X1) != iProver_top
% 19.61/2.99      | k1_relset_1(k1_relat_1(k7_relat_1(sK5,X0)),X1,k7_relat_1(sK5,X0)) = k1_relat_1(k7_relat_1(sK5,X0)) ),
% 19.61/2.99      inference(global_propositional_subsumption,
% 19.61/2.99                [status(thm)],
% 19.61/2.99                [c_21318,c_4699]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_28703,plain,
% 19.61/2.99      ( k1_relset_1(k1_relat_1(k7_relat_1(sK5,X0)),X1,k7_relat_1(sK5,X0)) = k1_relat_1(k7_relat_1(sK5,X0))
% 19.61/2.99      | r1_tarski(k9_relat_1(sK5,X0),X1) != iProver_top ),
% 19.61/2.99      inference(renaming,[status(thm)],[c_28702]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_28711,plain,
% 19.61/2.99      ( k1_relset_1(k1_relat_1(k7_relat_1(sK5,sK2)),sK3,k7_relat_1(sK5,sK2)) = k1_relat_1(k7_relat_1(sK5,sK2)) ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_3272,c_28703]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_34,negated_conjecture,
% 19.61/2.99      ( r1_tarski(sK2,sK1) ),
% 19.61/2.99      inference(cnf_transformation,[],[f96]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1777,plain,
% 19.61/2.99      ( r1_tarski(sK2,sK1) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_28,plain,
% 19.61/2.99      ( ~ v1_funct_2(X0,X1,X2)
% 19.61/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | k1_relset_1(X1,X2,X0) = X1
% 19.61/2.99      | k1_xboole_0 = X2 ),
% 19.61/2.99      inference(cnf_transformation,[],[f83]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_36,negated_conjecture,
% 19.61/2.99      ( v1_funct_2(sK5,sK1,sK4) ),
% 19.61/2.99      inference(cnf_transformation,[],[f94]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_618,plain,
% 19.61/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | k1_relset_1(X1,X2,X0) = X1
% 19.61/2.99      | sK5 != X0
% 19.61/2.99      | sK4 != X2
% 19.61/2.99      | sK1 != X1
% 19.61/2.99      | k1_xboole_0 = X2 ),
% 19.61/2.99      inference(resolution_lifted,[status(thm)],[c_28,c_36]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_619,plain,
% 19.61/2.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
% 19.61/2.99      | k1_relset_1(sK1,sK4,sK5) = sK1
% 19.61/2.99      | k1_xboole_0 = sK4 ),
% 19.61/2.99      inference(unflattening,[status(thm)],[c_618]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_621,plain,
% 19.61/2.99      ( k1_relset_1(sK1,sK4,sK5) = sK1 | k1_xboole_0 = sK4 ),
% 19.61/2.99      inference(global_propositional_subsumption,
% 19.61/2.99                [status(thm)],
% 19.61/2.99                [c_619,c_35]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3139,plain,
% 19.61/2.99      ( k1_relset_1(sK1,sK4,sK5) = k1_relat_1(sK5) ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1776,c_1784]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3270,plain,
% 19.61/2.99      ( k1_relat_1(sK5) = sK1 | sK4 = k1_xboole_0 ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_621,c_3139]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_38,negated_conjecture,
% 19.61/2.99      ( ~ v1_xboole_0(sK4) ),
% 19.61/2.99      inference(cnf_transformation,[],[f92]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3,plain,
% 19.61/2.99      ( v1_xboole_0(k1_xboole_0) ),
% 19.61/2.99      inference(cnf_transformation,[],[f63]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1856,plain,
% 19.61/2.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_992]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1858,plain,
% 19.61/2.99      ( v1_xboole_0(sK4)
% 19.61/2.99      | ~ v1_xboole_0(k1_xboole_0)
% 19.61/2.99      | sK4 != k1_xboole_0 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_1856]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3443,plain,
% 19.61/2.99      ( k1_relat_1(sK5) = sK1 ),
% 19.61/2.99      inference(global_propositional_subsumption,
% 19.61/2.99                [status(thm)],
% 19.61/2.99                [c_3270,c_38,c_3,c_1858]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_16,plain,
% 19.61/2.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 19.61/2.99      | ~ v1_relat_1(X1)
% 19.61/2.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 19.61/2.99      inference(cnf_transformation,[],[f76]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1787,plain,
% 19.61/2.99      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 19.61/2.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 19.61/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3562,plain,
% 19.61/2.99      ( k1_relat_1(k7_relat_1(sK5,X0)) = X0
% 19.61/2.99      | r1_tarski(X0,sK1) != iProver_top
% 19.61/2.99      | v1_relat_1(sK5) != iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_3443,c_1787]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4232,plain,
% 19.61/2.99      ( r1_tarski(X0,sK1) != iProver_top
% 19.61/2.99      | k1_relat_1(k7_relat_1(sK5,X0)) = X0 ),
% 19.61/2.99      inference(global_propositional_subsumption,
% 19.61/2.99                [status(thm)],
% 19.61/2.99                [c_3562,c_2572]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4233,plain,
% 19.61/2.99      ( k1_relat_1(k7_relat_1(sK5,X0)) = X0
% 19.61/2.99      | r1_tarski(X0,sK1) != iProver_top ),
% 19.61/2.99      inference(renaming,[status(thm)],[c_4232]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4241,plain,
% 19.61/2.99      ( k1_relat_1(k7_relat_1(sK5,sK2)) = sK2 ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1777,c_4233]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_28717,plain,
% 19.61/2.99      ( k1_relset_1(sK2,sK3,k7_relat_1(sK5,sK2)) = sK2 ),
% 19.61/2.99      inference(light_normalisation,[status(thm)],[c_28711,c_4241]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_26,plain,
% 19.61/2.99      ( v1_funct_2(X0,X1,X2)
% 19.61/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | k1_relset_1(X1,X2,X0) != X1
% 19.61/2.99      | k1_xboole_0 = X2 ),
% 19.61/2.99      inference(cnf_transformation,[],[f85]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_32,negated_conjecture,
% 19.61/2.99      ( ~ v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)
% 19.61/2.99      | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 19.61/2.99      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
% 19.61/2.99      inference(cnf_transformation,[],[f98]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_602,plain,
% 19.61/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 19.61/2.99      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | k2_partfun1(sK1,sK4,sK5,sK2) != X0
% 19.61/2.99      | k1_relset_1(X1,X2,X0) != X1
% 19.61/2.99      | sK3 != X2
% 19.61/2.99      | sK2 != X1
% 19.61/2.99      | k1_xboole_0 = X2 ),
% 19.61/2.99      inference(resolution_lifted,[status(thm)],[c_26,c_32]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_603,plain,
% 19.61/2.99      ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 19.61/2.99      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
% 19.61/2.99      | k1_xboole_0 = sK3 ),
% 19.61/2.99      inference(unflattening,[status(thm)],[c_602]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1766,plain,
% 19.61/2.99      ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
% 19.61/2.99      | k1_xboole_0 = sK3
% 19.61/2.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 19.61/2.99      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_604,plain,
% 19.61/2.99      ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
% 19.61/2.99      | k1_xboole_0 = sK3
% 19.61/2.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 19.61/2.99      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_30,plain,
% 19.61/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | ~ v1_funct_1(X0)
% 19.61/2.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 19.61/2.99      inference(cnf_transformation,[],[f89]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1882,plain,
% 19.61/2.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
% 19.61/2.99      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | ~ v1_funct_1(sK5) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_30]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1883,plain,
% 19.61/2.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) != iProver_top
% 19.61/2.99      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) = iProver_top
% 19.61/2.99      | v1_funct_1(sK5) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_1882]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2230,plain,
% 19.61/2.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 19.61/2.99      | k1_xboole_0 = sK3
% 19.61/2.99      | k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2 ),
% 19.61/2.99      inference(global_propositional_subsumption,
% 19.61/2.99                [status(thm)],
% 19.61/2.99                [c_1766,c_40,c_42,c_604,c_1883]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2231,plain,
% 19.61/2.99      ( k1_relset_1(sK2,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != sK2
% 19.61/2.99      | k1_xboole_0 = sK3
% 19.61/2.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 19.61/2.99      inference(renaming,[status(thm)],[c_2230]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3820,plain,
% 19.61/2.99      ( k1_relset_1(sK2,sK3,k7_relat_1(sK5,sK2)) != sK2
% 19.61/2.99      | sK3 = k1_xboole_0
% 19.61/2.99      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 19.61/2.99      inference(demodulation,[status(thm)],[c_3814,c_2231]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_28883,plain,
% 19.61/2.99      ( sK3 = k1_xboole_0
% 19.61/2.99      | sK2 != sK2
% 19.61/2.99      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 19.61/2.99      inference(demodulation,[status(thm)],[c_28717,c_3820]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_29127,plain,
% 19.61/2.99      ( sK3 = k1_xboole_0
% 19.61/2.99      | m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 19.61/2.99      inference(equality_resolution_simp,[status(thm)],[c_28883]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_29130,plain,
% 19.61/2.99      ( sK3 = k1_xboole_0
% 19.61/2.99      | r1_tarski(k1_relat_1(k7_relat_1(sK5,sK2)),sK2) != iProver_top
% 19.61/2.99      | r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3) != iProver_top
% 19.61/2.99      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1782,c_29127]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_29131,plain,
% 19.61/2.99      ( sK3 = k1_xboole_0
% 19.61/2.99      | r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3) != iProver_top
% 19.61/2.99      | r1_tarski(sK2,sK2) != iProver_top
% 19.61/2.99      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 19.61/2.99      inference(light_normalisation,[status(thm)],[c_29130,c_4241]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_29132,plain,
% 19.61/2.99      ( sK3 = k1_xboole_0
% 19.61/2.99      | r1_tarski(k9_relat_1(sK5,sK2),sK3) != iProver_top
% 19.61/2.99      | r1_tarski(sK2,sK2) != iProver_top
% 19.61/2.99      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 19.61/2.99      inference(demodulation,[status(thm)],[c_29131,c_2798]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_8442,plain,
% 19.61/2.99      ( r1_tarski(sK2,sK2) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_6]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_8443,plain,
% 19.61/2.99      ( r1_tarski(sK2,sK2) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_8442]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_29213,plain,
% 19.61/2.99      ( sK3 = k1_xboole_0
% 19.61/2.99      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 19.61/2.99      inference(global_propositional_subsumption,
% 19.61/2.99                [status(thm)],
% 19.61/2.99                [c_29132,c_3272,c_8443]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_29217,plain,
% 19.61/2.99      ( sK3 = k1_xboole_0 ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_4699,c_29213]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_988,plain,( X0 = X0 ),theory(equality) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_28153,plain,
% 19.61/2.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_988]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_28154,plain,
% 19.61/2.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_28153]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_990,plain,
% 19.61/2.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.61/2.99      theory(equality) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_8962,plain,
% 19.61/2.99      ( ~ r1_tarski(X0,X1)
% 19.61/2.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),X2)
% 19.61/2.99      | X2 != X1
% 19.61/2.99      | k2_partfun1(sK1,sK4,sK5,sK2) != X0 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_990]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_27216,plain,
% 19.61/2.99      ( ~ r1_tarski(X0,X1)
% 19.61/2.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),sK3)
% 19.61/2.99      | k2_partfun1(sK1,sK4,sK5,sK2) != X0
% 19.61/2.99      | sK3 != X1 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_8962]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_27217,plain,
% 19.61/2.99      ( k2_partfun1(sK1,sK4,sK5,sK2) != X0
% 19.61/2.99      | sK3 != X1
% 19.61/2.99      | r1_tarski(X0,X1) != iProver_top
% 19.61/2.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),sK3) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_27216]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_27219,plain,
% 19.61/2.99      ( k2_partfun1(sK1,sK4,sK5,sK2) != k1_xboole_0
% 19.61/2.99      | sK3 != k1_xboole_0
% 19.61/2.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),sK3) = iProver_top
% 19.61/2.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_27217]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1,plain,
% 19.61/2.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 19.61/2.99      inference(cnf_transformation,[],[f61]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1798,plain,
% 19.61/2.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 19.61/2.99      | r1_tarski(X0,X1) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1773,plain,
% 19.61/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.61/2.99      | r1_tarski(X1,X2) != iProver_top
% 19.61/2.99      | v1_xboole_0(X2) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_361]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3512,plain,
% 19.61/2.99      ( r1_tarski(X0,X1) != iProver_top
% 19.61/2.99      | r1_tarski(X0,X2) = iProver_top
% 19.61/2.99      | v1_xboole_0(X1) != iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1798,c_1773]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_7502,plain,
% 19.61/2.99      ( r1_tarski(k9_relat_1(sK5,sK2),X0) = iProver_top
% 19.61/2.99      | v1_xboole_0(sK3) != iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_3272,c_3512]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1792,plain,
% 19.61/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 19.61/2.99      | r1_tarski(X0,X1) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_19,plain,
% 19.61/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | ~ v1_xboole_0(X2)
% 19.61/2.99      | v1_xboole_0(X0) ),
% 19.61/2.99      inference(cnf_transformation,[],[f79]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1785,plain,
% 19.61/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.61/2.99      | v1_xboole_0(X2) != iProver_top
% 19.61/2.99      | v1_xboole_0(X0) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3515,plain,
% 19.61/2.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 19.61/2.99      | v1_xboole_0(X2) != iProver_top
% 19.61/2.99      | v1_xboole_0(X0) = iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1792,c_1785]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_8185,plain,
% 19.61/2.99      ( v1_xboole_0(X0) != iProver_top
% 19.61/2.99      | v1_xboole_0(k9_relat_1(sK5,sK2)) = iProver_top
% 19.61/2.99      | v1_xboole_0(sK3) != iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_7502,c_3515]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_122,plain,
% 19.61/2.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_8199,plain,
% 19.61/2.99      ( v1_xboole_0(k9_relat_1(sK5,sK2)) = iProver_top
% 19.61/2.99      | v1_xboole_0(sK3) != iProver_top
% 19.61/2.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_8185]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_10858,plain,
% 19.61/2.99      ( v1_xboole_0(k9_relat_1(sK5,sK2)) = iProver_top
% 19.61/2.99      | v1_xboole_0(sK3) != iProver_top ),
% 19.61/2.99      inference(global_propositional_subsumption,
% 19.61/2.99                [status(thm)],
% 19.61/2.99                [c_8185,c_122,c_8199]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4399,plain,
% 19.61/2.99      ( r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 19.61/2.99      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 19.61/2.99      | v1_relat_1(X0) != iProver_top
% 19.61/2.99      | v1_xboole_0(X2) != iProver_top
% 19.61/2.99      | v1_xboole_0(X0) = iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1782,c_1785]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_19050,plain,
% 19.61/2.99      ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 19.61/2.99      | v1_relat_1(X0) != iProver_top
% 19.61/2.99      | v1_xboole_0(X1) != iProver_top
% 19.61/2.99      | v1_xboole_0(X0) = iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1794,c_4399]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_19221,plain,
% 19.61/2.99      ( v1_relat_1(X0) != iProver_top
% 19.61/2.99      | v1_xboole_0(X0) = iProver_top
% 19.61/2.99      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1794,c_19050]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_19256,plain,
% 19.61/2.99      ( v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top
% 19.61/2.99      | v1_xboole_0(k9_relat_1(sK5,X0)) != iProver_top
% 19.61/2.99      | v1_xboole_0(k7_relat_1(sK5,X0)) = iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_2798,c_19221]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_19361,plain,
% 19.61/2.99      ( v1_xboole_0(k9_relat_1(sK5,X0)) != iProver_top
% 19.61/2.99      | v1_xboole_0(k7_relat_1(sK5,X0)) = iProver_top ),
% 19.61/2.99      inference(global_propositional_subsumption,
% 19.61/2.99                [status(thm)],
% 19.61/2.99                [c_19256,c_4699]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_19367,plain,
% 19.61/2.99      ( v1_xboole_0(k7_relat_1(sK5,sK2)) = iProver_top
% 19.61/2.99      | v1_xboole_0(sK3) != iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_10858,c_19361]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_19370,plain,
% 19.61/2.99      ( v1_xboole_0(k7_relat_1(sK5,sK2)) | ~ v1_xboole_0(sK3) ),
% 19.61/2.99      inference(predicate_to_equality_rev,[status(thm)],[c_19367]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_12069,plain,
% 19.61/2.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
% 19.61/2.99      | ~ v1_funct_1(sK5)
% 19.61/2.99      | k2_partfun1(sK1,sK4,sK5,sK2) = k7_relat_1(sK5,sK2) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_31]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_11149,plain,
% 19.61/2.99      ( r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_partfun1(sK1,sK4,sK5,sK2)) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_6]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2922,plain,
% 19.61/2.99      ( ~ r1_tarski(X0,X1)
% 19.61/2.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3))
% 19.61/2.99      | k2_partfun1(sK1,sK4,sK5,sK2) != X0
% 19.61/2.99      | k2_zfmisc_1(k1_xboole_0,sK3) != X1 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_990]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_10502,plain,
% 19.61/2.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 19.61/2.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3))
% 19.61/2.99      | k2_partfun1(sK1,sK4,sK5,sK2) != X0
% 19.61/2.99      | k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(X1,X2) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_2922]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_10503,plain,
% 19.61/2.99      ( k2_partfun1(sK1,sK4,sK5,sK2) != X0
% 19.61/2.99      | k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(X1,X2)
% 19.61/2.99      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 19.61/2.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3)) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_10502]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_10505,plain,
% 19.61/2.99      ( k2_partfun1(sK1,sK4,sK5,sK2) != k1_xboole_0
% 19.61/2.99      | k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 19.61/2.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3)) = iProver_top
% 19.61/2.99      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_10503]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_9296,plain,
% 19.61/2.99      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_989]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_9297,plain,
% 19.61/2.99      ( sK3 != k1_xboole_0
% 19.61/2.99      | k1_xboole_0 = sK3
% 19.61/2.99      | k1_xboole_0 != k1_xboole_0 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_9296]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_7996,plain,
% 19.61/2.99      ( ~ r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),X0)
% 19.61/2.99      | ~ v1_xboole_0(X0) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_361]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_7998,plain,
% 19.61/2.99      ( ~ r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0)
% 19.61/2.99      | ~ v1_xboole_0(k1_xboole_0) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_7996]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2370,plain,
% 19.61/2.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,sK3) | ~ v1_xboole_0(sK3) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_361]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_7979,plain,
% 19.61/2.99      ( ~ r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),sK3)
% 19.61/2.99      | ~ v1_xboole_0(sK3) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_2370]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_7980,plain,
% 19.61/2.99      ( r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top
% 19.61/2.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),sK3) != iProver_top
% 19.61/2.99      | v1_xboole_0(sK3) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_7979]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2241,plain,
% 19.61/2.99      ( ~ r2_hidden(X0,sK3)
% 19.61/2.99      | ~ r1_tarski(sK3,k1_xboole_0)
% 19.61/2.99      | ~ v1_xboole_0(k1_xboole_0) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_361]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_6653,plain,
% 19.61/2.99      ( ~ r2_hidden(sK0(sK3,k2_zfmisc_1(X0,X1)),sK3)
% 19.61/2.99      | ~ r1_tarski(sK3,k1_xboole_0)
% 19.61/2.99      | ~ v1_xboole_0(k1_xboole_0) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_2241]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_6654,plain,
% 19.61/2.99      ( r2_hidden(sK0(sK3,k2_zfmisc_1(X0,X1)),sK3) != iProver_top
% 19.61/2.99      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 19.61/2.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_6653]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_6656,plain,
% 19.61/2.99      ( r2_hidden(sK0(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK3) != iProver_top
% 19.61/2.99      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 19.61/2.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_6654]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_7,plain,
% 19.61/2.99      ( r1_tarski(k1_xboole_0,X0) ),
% 19.61/2.99      inference(cnf_transformation,[],[f67]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1793,plain,
% 19.61/2.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3138,plain,
% 19.61/2.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 19.61/2.99      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1792,c_1784]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_6109,plain,
% 19.61/2.99      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1793,c_3138]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2571,plain,
% 19.61/2.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 19.61/2.99      | v1_relat_1(X0) = iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1792,c_1786]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3031,plain,
% 19.61/2.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1793,c_2571]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3560,plain,
% 19.61/2.99      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 19.61/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1793,c_1787]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_5582,plain,
% 19.61/2.99      ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_3031,c_3560]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_18,plain,
% 19.61/2.99      ( v4_relat_1(X0,X1)
% 19.61/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 19.61/2.99      inference(cnf_transformation,[],[f78]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_14,plain,
% 19.61/2.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 19.61/2.99      inference(cnf_transformation,[],[f74]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_496,plain,
% 19.61/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | ~ v1_relat_1(X0)
% 19.61/2.99      | k7_relat_1(X0,X1) = X0 ),
% 19.61/2.99      inference(resolution,[status(thm)],[c_18,c_14]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_500,plain,
% 19.61/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | k7_relat_1(X0,X1) = X0 ),
% 19.61/2.99      inference(global_propositional_subsumption,
% 19.61/2.99                [status(thm)],
% 19.61/2.99                [c_496,c_18,c_17,c_14]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1771,plain,
% 19.61/2.99      ( k7_relat_1(X0,X1) = X0
% 19.61/2.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2662,plain,
% 19.61/2.99      ( k7_relat_1(X0,X1) = X0
% 19.61/2.99      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1792,c_1771]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4867,plain,
% 19.61/2.99      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.61/2.99      inference(superposition,[status(thm)],[c_1793,c_2662]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_5587,plain,
% 19.61/2.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.61/2.99      inference(demodulation,[status(thm)],[c_5582,c_4867]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_6113,plain,
% 19.61/2.99      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 19.61/2.99      inference(light_normalisation,[status(thm)],[c_6109,c_5587]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_6118,plain,
% 19.61/2.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_6113]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4961,plain,
% 19.61/2.99      ( r1_tarski(k1_xboole_0,k2_partfun1(sK1,sK4,sK5,sK2)) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_7]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4751,plain,
% 19.61/2.99      ( sK2 = sK2 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_988]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_3041,plain,
% 19.61/2.99      ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != X0
% 19.61/2.99      | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_xboole_0
% 19.61/2.99      | k1_xboole_0 != X0 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_989]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4497,plain,
% 19.61/2.99      ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relset_1(X0,X1,X2)
% 19.61/2.99      | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_xboole_0
% 19.61/2.99      | k1_xboole_0 != k1_relset_1(X0,X1,X2) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_3041]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4498,plain,
% 19.61/2.99      ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 19.61/2.99      | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) = k1_xboole_0
% 19.61/2.99      | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_4497]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4302,plain,
% 19.61/2.99      ( r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0),k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_1]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_9,plain,
% 19.61/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.61/2.99      inference(cnf_transformation,[],[f68]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4116,plain,
% 19.61/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.61/2.99      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_9]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4117,plain,
% 19.61/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.61/2.99      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_4116]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4119,plain,
% 19.61/2.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 19.61/2.99      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_4117]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_4,plain,
% 19.61/2.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 19.61/2.99      inference(cnf_transformation,[],[f66]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2990,plain,
% 19.61/2.99      ( ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k1_xboole_0)
% 19.61/2.99      | ~ r1_tarski(k1_xboole_0,k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | k2_partfun1(sK1,sK4,sK5,sK2) = k1_xboole_0 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_4]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2895,plain,
% 19.61/2.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,k1_xboole_0)) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_7]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2749,plain,
% 19.61/2.99      ( r2_hidden(sK0(sK3,k2_zfmisc_1(X0,X1)),sK3)
% 19.61/2.99      | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_1]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2755,plain,
% 19.61/2.99      ( r2_hidden(sK0(sK3,k2_zfmisc_1(X0,X1)),sK3) = iProver_top
% 19.61/2.99      | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_2749]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2757,plain,
% 19.61/2.99      ( r2_hidden(sK0(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK3) = iProver_top
% 19.61/2.99      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_2755]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2492,plain,
% 19.61/2.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 19.61/2.99      | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3)) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_8]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2493,plain,
% 19.61/2.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) = iProver_top
% 19.61/2.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(k1_xboole_0,sK3)) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_2492]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2356,plain,
% 19.61/2.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 19.61/2.99      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,k1_xboole_0)) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_8]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2164,plain,
% 19.61/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.61/2.99      | ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_8]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2165,plain,
% 19.61/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 19.61/2.99      | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_2164]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2167,plain,
% 19.61/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 19.61/2.99      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_2165]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1877,plain,
% 19.61/2.99      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_989]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2147,plain,
% 19.61/2.99      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_1877]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2059,plain,
% 19.61/2.99      ( r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_1]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2063,plain,
% 19.61/2.99      ( r2_hidden(sK0(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)),k2_partfun1(sK1,sK4,sK5,sK2)) = iProver_top
% 19.61/2.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_2059]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2005,plain,
% 19.61/2.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 19.61/2.99      | ~ r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_8]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_2006,plain,
% 19.61/2.99      ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
% 19.61/2.99      | r1_tarski(k2_partfun1(sK1,sK4,sK5,sK2),k2_zfmisc_1(sK2,sK3)) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_2005]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1956,plain,
% 19.61/2.99      ( ~ r1_tarski(X0,X1)
% 19.61/2.99      | r1_tarski(sK3,k1_xboole_0)
% 19.61/2.99      | sK3 != X0
% 19.61/2.99      | k1_xboole_0 != X1 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_990]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1957,plain,
% 19.61/2.99      ( sK3 != X0
% 19.61/2.99      | k1_xboole_0 != X1
% 19.61/2.99      | r1_tarski(X0,X1) != iProver_top
% 19.61/2.99      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_1956]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1959,plain,
% 19.61/2.99      ( sK3 != k1_xboole_0
% 19.61/2.99      | k1_xboole_0 != k1_xboole_0
% 19.61/2.99      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 19.61/2.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_1957]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1907,plain,
% 19.61/2.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_992]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1908,plain,
% 19.61/2.99      ( sK3 != X0
% 19.61/2.99      | v1_xboole_0(X0) != iProver_top
% 19.61/2.99      | v1_xboole_0(sK3) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_1907]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1910,plain,
% 19.61/2.99      ( sK3 != k1_xboole_0
% 19.61/2.99      | v1_xboole_0(sK3) = iProver_top
% 19.61/2.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_1908]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_1909,plain,
% 19.61/2.99      ( v1_xboole_0(sK3)
% 19.61/2.99      | ~ v1_xboole_0(k1_xboole_0)
% 19.61/2.99      | sK3 != k1_xboole_0 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_1907]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_25,plain,
% 19.61/2.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 19.61/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 19.61/2.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 19.61/2.99      inference(cnf_transformation,[],[f104]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_570,plain,
% 19.61/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 19.61/2.99      | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 19.61/2.99      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | k2_partfun1(sK1,sK4,sK5,sK2) != X0
% 19.61/2.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 19.61/2.99      | sK3 != X1
% 19.61/2.99      | sK2 != k1_xboole_0 ),
% 19.61/2.99      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_571,plain,
% 19.61/2.99      ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 19.61/2.99      | ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 19.61/2.99      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
% 19.61/2.99      | sK2 != k1_xboole_0 ),
% 19.61/2.99      inference(unflattening,[status(thm)],[c_570]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_572,plain,
% 19.61/2.99      ( k1_relset_1(k1_xboole_0,sK3,k2_partfun1(sK1,sK4,sK5,sK2)) != k1_xboole_0
% 19.61/2.99      | sK2 != k1_xboole_0
% 19.61/2.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 19.61/2.99      | m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 19.61/2.99      | v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) != iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_23,plain,
% 19.61/2.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 19.61/2.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 19.61/2.99      | k1_xboole_0 = X0 ),
% 19.61/2.99      inference(cnf_transformation,[],[f102]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_524,plain,
% 19.61/2.99      ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 19.61/2.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 19.61/2.99      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | k2_partfun1(sK1,sK4,sK5,sK2) != k1_xboole_0
% 19.61/2.99      | sK3 != k1_xboole_0
% 19.61/2.99      | sK2 != X0
% 19.61/2.99      | k1_xboole_0 = X0 ),
% 19.61/2.99      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_525,plain,
% 19.61/2.99      ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 19.61/2.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 19.61/2.99      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
% 19.61/2.99      | k2_partfun1(sK1,sK4,sK5,sK2) != k1_xboole_0
% 19.61/2.99      | sK3 != k1_xboole_0
% 19.61/2.99      | k1_xboole_0 = sK2 ),
% 19.61/2.99      inference(unflattening,[status(thm)],[c_524]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_120,plain,
% 19.61/2.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 19.61/2.99      | k1_xboole_0 = k1_xboole_0 ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_4]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_114,plain,
% 19.61/2.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 19.61/2.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_116,plain,
% 19.61/2.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_114]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(c_115,plain,
% 19.61/2.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 19.61/2.99      inference(instantiation,[status(thm)],[c_7]) ).
% 19.61/2.99  
% 19.61/2.99  cnf(contradiction,plain,
% 19.61/2.99      ( $false ),
% 19.61/2.99      inference(minisat,
% 19.61/2.99                [status(thm)],
% 19.61/2.99                [c_66673,c_51965,c_47270,c_42264,c_39943,c_36946,c_29217,
% 19.61/2.99                 c_28154,c_27219,c_19370,c_12069,c_11149,c_10505,c_9297,
% 19.61/2.99                 c_7998,c_7980,c_6656,c_6118,c_4961,c_4751,c_4498,c_4302,
% 19.61/2.99                 c_4119,c_2990,c_2895,c_2757,c_2493,c_2356,c_2167,c_2147,
% 19.61/2.99                 c_2063,c_2059,c_2006,c_2005,c_1959,c_1910,c_1909,c_1883,
% 19.61/2.99                 c_1882,c_572,c_525,c_122,c_3,c_120,c_116,c_115,c_42,
% 19.61/2.99                 c_35,c_40,c_37]) ).
% 19.61/2.99  
% 19.61/2.99  
% 19.61/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.61/2.99  
% 19.61/2.99  ------                               Statistics
% 19.61/2.99  
% 19.61/2.99  ------ General
% 19.61/2.99  
% 19.61/2.99  abstr_ref_over_cycles:                  0
% 19.61/2.99  abstr_ref_under_cycles:                 0
% 19.61/2.99  gc_basic_clause_elim:                   0
% 19.61/2.99  forced_gc_time:                         0
% 19.61/2.99  parsing_time:                           0.009
% 19.61/2.99  unif_index_cands_time:                  0.
% 19.61/2.99  unif_index_add_time:                    0.
% 19.61/2.99  orderings_time:                         0.
% 19.61/2.99  out_proof_time:                         0.025
% 19.61/2.99  total_time:                             2.033
% 19.61/2.99  num_of_symbols:                         55
% 19.61/2.99  num_of_terms:                           61186
% 19.61/2.99  
% 19.61/2.99  ------ Preprocessing
% 19.61/2.99  
% 19.61/2.99  num_of_splits:                          0
% 19.61/2.99  num_of_split_atoms:                     0
% 19.61/2.99  num_of_reused_defs:                     0
% 19.61/2.99  num_eq_ax_congr_red:                    25
% 19.61/2.99  num_of_sem_filtered_clauses:            1
% 19.61/2.99  num_of_subtypes:                        0
% 19.61/2.99  monotx_restored_types:                  0
% 19.61/2.99  sat_num_of_epr_types:                   0
% 19.61/2.99  sat_num_of_non_cyclic_types:            0
% 19.61/2.99  sat_guarded_non_collapsed_types:        0
% 19.61/2.99  num_pure_diseq_elim:                    0
% 19.61/2.99  simp_replaced_by:                       0
% 19.61/2.99  res_preprocessed:                       177
% 19.61/2.99  prep_upred:                             0
% 19.61/2.99  prep_unflattend:                        33
% 19.61/2.99  smt_new_axioms:                         0
% 19.61/2.99  pred_elim_cands:                        6
% 19.61/2.99  pred_elim:                              2
% 19.61/2.99  pred_elim_cl:                           2
% 19.61/2.99  pred_elim_cycles:                       4
% 19.61/2.99  merged_defs:                            8
% 19.61/2.99  merged_defs_ncl:                        0
% 19.61/2.99  bin_hyper_res:                          10
% 19.61/2.99  prep_cycles:                            4
% 19.61/2.99  pred_elim_time:                         0.003
% 19.61/2.99  splitting_time:                         0.
% 19.61/2.99  sem_filter_time:                        0.
% 19.61/2.99  monotx_time:                            0.
% 19.61/2.99  subtype_inf_time:                       0.
% 19.61/2.99  
% 19.61/2.99  ------ Problem properties
% 19.61/2.99  
% 19.61/2.99  clauses:                                36
% 19.61/2.99  conjectures:                            5
% 19.61/2.99  epr:                                    10
% 19.61/2.99  horn:                                   33
% 19.61/2.99  ground:                                 13
% 19.61/2.99  unary:                                  9
% 19.61/2.99  binary:                                 11
% 19.61/2.99  lits:                                   89
% 19.61/2.99  lits_eq:                                24
% 19.61/2.99  fd_pure:                                0
% 19.61/2.99  fd_pseudo:                              0
% 19.61/2.99  fd_cond:                                0
% 19.61/2.99  fd_pseudo_cond:                         1
% 19.61/2.99  ac_symbols:                             0
% 19.61/2.99  
% 19.61/2.99  ------ Propositional Solver
% 19.61/2.99  
% 19.61/2.99  prop_solver_calls:                      42
% 19.61/2.99  prop_fast_solver_calls:                 3414
% 19.61/2.99  smt_solver_calls:                       0
% 19.61/2.99  smt_fast_solver_calls:                  0
% 19.61/2.99  prop_num_of_clauses:                    30364
% 19.61/2.99  prop_preprocess_simplified:             43080
% 19.61/2.99  prop_fo_subsumed:                       120
% 19.61/2.99  prop_solver_time:                       0.
% 19.61/2.99  smt_solver_time:                        0.
% 19.61/2.99  smt_fast_solver_time:                   0.
% 19.61/2.99  prop_fast_solver_time:                  0.
% 19.61/2.99  prop_unsat_core_time:                   0.003
% 19.61/2.99  
% 19.61/2.99  ------ QBF
% 19.61/2.99  
% 19.61/2.99  qbf_q_res:                              0
% 19.61/2.99  qbf_num_tautologies:                    0
% 19.61/2.99  qbf_prep_cycles:                        0
% 19.61/2.99  
% 19.61/2.99  ------ BMC1
% 19.61/2.99  
% 19.61/2.99  bmc1_current_bound:                     -1
% 19.61/2.99  bmc1_last_solved_bound:                 -1
% 19.61/2.99  bmc1_unsat_core_size:                   -1
% 19.61/2.99  bmc1_unsat_core_parents_size:           -1
% 19.61/2.99  bmc1_merge_next_fun:                    0
% 19.61/2.99  bmc1_unsat_core_clauses_time:           0.
% 19.61/2.99  
% 19.61/2.99  ------ Instantiation
% 19.61/2.99  
% 19.61/2.99  inst_num_of_clauses:                    2022
% 19.61/2.99  inst_num_in_passive:                    903
% 19.61/2.99  inst_num_in_active:                     2688
% 19.61/2.99  inst_num_in_unprocessed:                201
% 19.61/2.99  inst_num_of_loops:                      4115
% 19.61/2.99  inst_num_of_learning_restarts:          1
% 19.61/2.99  inst_num_moves_active_passive:          1419
% 19.61/2.99  inst_lit_activity:                      0
% 19.61/2.99  inst_lit_activity_moves:                0
% 19.61/2.99  inst_num_tautologies:                   0
% 19.61/2.99  inst_num_prop_implied:                  0
% 19.61/2.99  inst_num_existing_simplified:           0
% 19.61/2.99  inst_num_eq_res_simplified:             0
% 19.61/2.99  inst_num_child_elim:                    0
% 19.61/2.99  inst_num_of_dismatching_blockings:      4378
% 19.61/2.99  inst_num_of_non_proper_insts:           8855
% 19.61/2.99  inst_num_of_duplicates:                 0
% 19.61/2.99  inst_inst_num_from_inst_to_res:         0
% 19.61/2.99  inst_dismatching_checking_time:         0.
% 19.61/2.99  
% 19.61/2.99  ------ Resolution
% 19.61/2.99  
% 19.61/2.99  res_num_of_clauses:                     51
% 19.61/2.99  res_num_in_passive:                     51
% 19.61/2.99  res_num_in_active:                      0
% 19.61/2.99  res_num_of_loops:                       181
% 19.61/2.99  res_forward_subset_subsumed:            459
% 19.61/2.99  res_backward_subset_subsumed:           0
% 19.61/2.99  res_forward_subsumed:                   0
% 19.61/2.99  res_backward_subsumed:                  0
% 19.61/2.99  res_forward_subsumption_resolution:     0
% 19.61/2.99  res_backward_subsumption_resolution:    0
% 19.61/2.99  res_clause_to_clause_subsumption:       16004
% 19.61/2.99  res_orphan_elimination:                 0
% 19.61/2.99  res_tautology_del:                      625
% 19.61/2.99  res_num_eq_res_simplified:              0
% 19.61/2.99  res_num_sel_changes:                    0
% 19.61/2.99  res_moves_from_active_to_pass:          0
% 19.61/2.99  
% 19.61/2.99  ------ Superposition
% 19.61/2.99  
% 19.61/2.99  sup_time_total:                         0.
% 19.61/2.99  sup_time_generating:                    0.
% 19.61/2.99  sup_time_sim_full:                      0.
% 19.61/2.99  sup_time_sim_immed:                     0.
% 19.61/2.99  
% 19.61/2.99  sup_num_of_clauses:                     3445
% 19.61/2.99  sup_num_in_active:                      686
% 19.61/2.99  sup_num_in_passive:                     2759
% 19.61/2.99  sup_num_of_loops:                       822
% 19.61/2.99  sup_fw_superposition:                   3644
% 19.61/2.99  sup_bw_superposition:                   1845
% 19.61/2.99  sup_immediate_simplified:               1867
% 19.61/2.99  sup_given_eliminated:                   11
% 19.61/2.99  comparisons_done:                       0
% 19.61/2.99  comparisons_avoided:                    0
% 19.61/2.99  
% 19.61/2.99  ------ Simplifications
% 19.61/2.99  
% 19.61/2.99  
% 19.61/2.99  sim_fw_subset_subsumed:                 259
% 19.61/2.99  sim_bw_subset_subsumed:                 83
% 19.61/2.99  sim_fw_subsumed:                        654
% 19.61/2.99  sim_bw_subsumed:                        179
% 19.61/2.99  sim_fw_subsumption_res:                 0
% 19.61/2.99  sim_bw_subsumption_res:                 0
% 19.61/2.99  sim_tautology_del:                      91
% 19.61/2.99  sim_eq_tautology_del:                   185
% 19.61/2.99  sim_eq_res_simp:                        1
% 19.61/2.99  sim_fw_demodulated:                     778
% 19.61/2.99  sim_bw_demodulated:                     25
% 19.61/2.99  sim_light_normalised:                   624
% 19.61/2.99  sim_joinable_taut:                      0
% 19.61/2.99  sim_joinable_simp:                      0
% 19.61/2.99  sim_ac_normalised:                      0
% 19.61/2.99  sim_smt_subsumption:                    0
% 19.61/2.99  
%------------------------------------------------------------------------------
