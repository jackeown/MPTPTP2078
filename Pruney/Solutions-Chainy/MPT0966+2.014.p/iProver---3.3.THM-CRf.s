%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:33 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  209 (20548 expanded)
%              Number of clauses        :  128 (7750 expanded)
%              Number of leaves         :   21 (3719 expanded)
%              Depth                    :   29
%              Number of atoms          :  644 (104273 expanded)
%              Number of equality atoms :  339 (30843 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

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
    inference(nnf_transformation,[],[f40])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f41,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f41])).

fof(f56,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
        | ~ v1_funct_2(sK5,sK2,sK4)
        | ~ v1_funct_1(sK5) )
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 != sK3 )
      & r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK5,sK2,sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
      | ~ v1_funct_2(sK5,sK2,sK4)
      | ~ v1_funct_1(sK5) )
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f42,f56])).

fof(f94,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f98,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_funct_2(sK5,sK2,sK4)
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f97,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f101,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f68])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f47])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f102,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f72])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f103,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f107,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f90])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f108,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f88])).

fof(f81,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_600,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_39])).

cnf(c_601,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_600])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_603,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_601,c_38])).

cnf(c_1435,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1439,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2961,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1435,c_1439])).

cnf(c_2971,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_603,c_2961])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1438,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2760,plain,
    ( k2_relset_1(sK2,sK3,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1435,c_1438])).

cnf(c_37,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1436,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2830,plain,
    ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2760,c_1436])).

cnf(c_25,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_18,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_25,c_18])).

cnf(c_1433,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_1715,plain,
    ( r1_tarski(k1_relat_1(sK5),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1435,c_1433])).

cnf(c_43,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1530,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1599,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1530])).

cnf(c_1765,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1599])).

cnf(c_1766,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1765])).

cnf(c_19,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1852,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1853,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1852])).

cnf(c_1876,plain,
    ( r1_tarski(k1_relat_1(sK5),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1715,c_43,c_1766,c_1853])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1437,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2960,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1437,c_1439])).

cnf(c_6045,plain,
    ( k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5)
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1876,c_2960])).

cnf(c_6422,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6045,c_43,c_1766,c_1853])).

cnf(c_6423,plain,
    ( k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5)
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6422])).

cnf(c_6429,plain,
    ( k1_relset_1(sK2,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2830,c_6423])).

cnf(c_32,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_35,negated_conjecture,
    ( ~ v1_funct_2(sK5,sK2,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_205,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_funct_2(sK5,sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_35,c_40])).

cnf(c_206,negated_conjecture,
    ( ~ v1_funct_2(sK5,sK2,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
    inference(renaming,[status(thm)],[c_205])).

cnf(c_587,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK4 != X2
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_206])).

cnf(c_588,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | k1_relset_1(sK2,sK4,sK5) != sK2
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_1428,plain,
    ( k1_relset_1(sK2,sK4,sK5) != sK2
    | k1_xboole_0 = sK4
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_6500,plain,
    ( k1_relat_1(sK5) != sK2
    | sK4 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6429,c_1428])).

cnf(c_1505,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ r1_tarski(k2_relat_1(sK5),sK4)
    | ~ r1_tarski(k1_relat_1(sK5),sK2)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1506,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top
    | r1_tarski(k1_relat_1(sK5),sK2) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1505])).

cnf(c_6503,plain,
    ( sK4 = k1_xboole_0
    | k1_relat_1(sK5) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6500,c_43,c_1506,c_1715,c_1766,c_1853,c_2830])).

cnf(c_6504,plain,
    ( k1_relat_1(sK5) != sK2
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6503])).

cnf(c_6505,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2971,c_6504])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_6649,plain,
    ( sK4 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6505,c_36])).

cnf(c_6655,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK5),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6649,c_2830])).

cnf(c_11,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1447,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1455,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1453,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3264,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK0(X0,X2),X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_1453])).

cnf(c_5527,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_3264])).

cnf(c_5532,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1447,c_5527])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1450,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5633,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5532,c_1450])).

cnf(c_6749,plain,
    ( k2_relat_1(sK5) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6655,c_5633])).

cnf(c_6648,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6505,c_1435])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_6650,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6648,c_12])).

cnf(c_14,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_104,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_105,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_110,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_112,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_611,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | sK3 != sK4
    | sK2 != sK2
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_206,c_39])).

cnf(c_612,plain,
    ( sK3 != sK4
    | sK2 != sK2
    | sK5 != sK5
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_920,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1516,plain,
    ( sK3 != X0
    | sK3 = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_920])).

cnf(c_1517,plain,
    ( sK3 = sK4
    | sK3 != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1516])).

cnf(c_919,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1585,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_1666,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_23,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1441,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3058,plain,
    ( k2_relat_1(sK5) = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 != k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2971,c_1441])).

cnf(c_921,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2202,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X2),X3)
    | X3 != X1
    | k2_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_921])).

cnf(c_3470,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK5),X2)
    | X2 != X1
    | k2_relat_1(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_2202])).

cnf(c_3471,plain,
    ( X0 != X1
    | k2_relat_1(sK5) != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3470])).

cnf(c_3473,plain,
    ( k2_relat_1(sK5) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_relat_1(sK5),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3471])).

cnf(c_2665,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_1437])).

cnf(c_4063,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1876,c_2665])).

cnf(c_4273,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4063,c_43,c_1766,c_1853])).

cnf(c_4274,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4273])).

cnf(c_6748,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6655,c_4274])).

cnf(c_7026,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6650,c_43,c_104,c_105,c_112,c_612,c_1506,c_1517,c_1585,c_1666,c_1715,c_1766,c_1853,c_2830,c_3058,c_3473,c_4063,c_6748])).

cnf(c_2963,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1439])).

cnf(c_7033,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_7026,c_2963])).

cnf(c_31,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK4 != X1
    | sK2 != k1_xboole_0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_206])).

cnf(c_559,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
    | k1_relset_1(k1_xboole_0,sK4,sK5) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_1430,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_559])).

cnf(c_1459,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1430,c_13])).

cnf(c_7045,plain,
    ( k1_relat_1(sK5) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7033,c_1459])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK3 != X1
    | sK2 != k1_xboole_0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_39])).

cnf(c_575,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_1429,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_1457,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1429,c_13])).

cnf(c_7046,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7033,c_1457])).

cnf(c_7410,plain,
    ( k2_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6749,c_43,c_104,c_105,c_112,c_612,c_1506,c_1517,c_1585,c_1666,c_1715,c_1766,c_1853,c_2830,c_3058,c_3473,c_4063,c_6650,c_6748,c_7045,c_7046])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1442,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7414,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7410,c_1442])).

cnf(c_3186,plain,
    ( k2_relat_1(sK5) = sK4
    | r1_tarski(sK4,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2830,c_1450])).

cnf(c_6654,plain,
    ( k2_relat_1(sK5) = sK4
    | sK2 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6649,c_3186])).

cnf(c_7220,plain,
    ( k2_relat_1(sK5) = sK4
    | r1_tarski(k1_xboole_0,k2_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6654,c_43,c_104,c_105,c_112,c_612,c_1506,c_1517,c_1585,c_1666,c_1715,c_1766,c_1853,c_2830,c_3058,c_3473,c_4063,c_6650,c_6748,c_7045,c_7046])).

cnf(c_7224,plain,
    ( k2_relat_1(sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_5532,c_7220])).

cnf(c_7325,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | sK4 != k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7224,c_1442])).

cnf(c_7412,plain,
    ( sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7410,c_7224])).

cnf(c_7516,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7414,c_43,c_104,c_105,c_112,c_612,c_1506,c_1517,c_1585,c_1666,c_1715,c_1766,c_1853,c_2830,c_3058,c_3473,c_4063,c_6649,c_6650,c_6748,c_7045,c_7046,c_7325])).

cnf(c_7523,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7516,c_2971])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7523,c_7412,c_7325,c_7045,c_7026,c_2830,c_1853,c_1766,c_1715,c_1666,c_1585,c_1517,c_1506,c_612,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.68/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/0.98  
% 3.68/0.98  ------  iProver source info
% 3.68/0.98  
% 3.68/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.68/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/0.98  git: non_committed_changes: false
% 3.68/0.98  git: last_make_outside_of_git: false
% 3.68/0.98  
% 3.68/0.98  ------ 
% 3.68/0.98  
% 3.68/0.98  ------ Input Options
% 3.68/0.98  
% 3.68/0.98  --out_options                           all
% 3.68/0.98  --tptp_safe_out                         true
% 3.68/0.98  --problem_path                          ""
% 3.68/0.98  --include_path                          ""
% 3.68/0.98  --clausifier                            res/vclausify_rel
% 3.68/0.98  --clausifier_options                    ""
% 3.68/0.98  --stdin                                 false
% 3.68/0.98  --stats_out                             all
% 3.68/0.98  
% 3.68/0.98  ------ General Options
% 3.68/0.98  
% 3.68/0.98  --fof                                   false
% 3.68/0.98  --time_out_real                         305.
% 3.68/0.98  --time_out_virtual                      -1.
% 3.68/0.98  --symbol_type_check                     false
% 3.68/0.98  --clausify_out                          false
% 3.68/0.98  --sig_cnt_out                           false
% 3.68/0.98  --trig_cnt_out                          false
% 3.68/0.98  --trig_cnt_out_tolerance                1.
% 3.68/0.98  --trig_cnt_out_sk_spl                   false
% 3.68/0.98  --abstr_cl_out                          false
% 3.68/0.98  
% 3.68/0.98  ------ Global Options
% 3.68/0.98  
% 3.68/0.98  --schedule                              default
% 3.68/0.98  --add_important_lit                     false
% 3.68/0.98  --prop_solver_per_cl                    1000
% 3.68/0.98  --min_unsat_core                        false
% 3.68/0.98  --soft_assumptions                      false
% 3.68/0.98  --soft_lemma_size                       3
% 3.68/0.98  --prop_impl_unit_size                   0
% 3.68/0.98  --prop_impl_unit                        []
% 3.68/0.98  --share_sel_clauses                     true
% 3.68/0.98  --reset_solvers                         false
% 3.68/0.98  --bc_imp_inh                            [conj_cone]
% 3.68/0.98  --conj_cone_tolerance                   3.
% 3.68/0.98  --extra_neg_conj                        none
% 3.68/0.98  --large_theory_mode                     true
% 3.68/0.98  --prolific_symb_bound                   200
% 3.68/0.98  --lt_threshold                          2000
% 3.68/0.98  --clause_weak_htbl                      true
% 3.68/0.98  --gc_record_bc_elim                     false
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing Options
% 3.68/0.98  
% 3.68/0.98  --preprocessing_flag                    true
% 3.68/0.98  --time_out_prep_mult                    0.1
% 3.68/0.98  --splitting_mode                        input
% 3.68/0.98  --splitting_grd                         true
% 3.68/0.98  --splitting_cvd                         false
% 3.68/0.98  --splitting_cvd_svl                     false
% 3.68/0.98  --splitting_nvd                         32
% 3.68/0.98  --sub_typing                            true
% 3.68/0.98  --prep_gs_sim                           true
% 3.68/0.98  --prep_unflatten                        true
% 3.68/0.98  --prep_res_sim                          true
% 3.68/0.98  --prep_upred                            true
% 3.68/0.98  --prep_sem_filter                       exhaustive
% 3.68/0.98  --prep_sem_filter_out                   false
% 3.68/0.98  --pred_elim                             true
% 3.68/0.98  --res_sim_input                         true
% 3.68/0.98  --eq_ax_congr_red                       true
% 3.68/0.98  --pure_diseq_elim                       true
% 3.68/0.98  --brand_transform                       false
% 3.68/0.98  --non_eq_to_eq                          false
% 3.68/0.98  --prep_def_merge                        true
% 3.68/0.98  --prep_def_merge_prop_impl              false
% 3.68/0.98  --prep_def_merge_mbd                    true
% 3.68/0.98  --prep_def_merge_tr_red                 false
% 3.68/0.98  --prep_def_merge_tr_cl                  false
% 3.68/0.98  --smt_preprocessing                     true
% 3.68/0.98  --smt_ac_axioms                         fast
% 3.68/0.98  --preprocessed_out                      false
% 3.68/0.98  --preprocessed_stats                    false
% 3.68/0.98  
% 3.68/0.98  ------ Abstraction refinement Options
% 3.68/0.98  
% 3.68/0.98  --abstr_ref                             []
% 3.68/0.98  --abstr_ref_prep                        false
% 3.68/0.98  --abstr_ref_until_sat                   false
% 3.68/0.98  --abstr_ref_sig_restrict                funpre
% 3.68/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.98  --abstr_ref_under                       []
% 3.68/0.98  
% 3.68/0.98  ------ SAT Options
% 3.68/0.98  
% 3.68/0.98  --sat_mode                              false
% 3.68/0.98  --sat_fm_restart_options                ""
% 3.68/0.98  --sat_gr_def                            false
% 3.68/0.98  --sat_epr_types                         true
% 3.68/0.98  --sat_non_cyclic_types                  false
% 3.68/0.98  --sat_finite_models                     false
% 3.68/0.98  --sat_fm_lemmas                         false
% 3.68/0.98  --sat_fm_prep                           false
% 3.68/0.98  --sat_fm_uc_incr                        true
% 3.68/0.98  --sat_out_model                         small
% 3.68/0.98  --sat_out_clauses                       false
% 3.68/0.98  
% 3.68/0.98  ------ QBF Options
% 3.68/0.98  
% 3.68/0.98  --qbf_mode                              false
% 3.68/0.98  --qbf_elim_univ                         false
% 3.68/0.98  --qbf_dom_inst                          none
% 3.68/0.98  --qbf_dom_pre_inst                      false
% 3.68/0.98  --qbf_sk_in                             false
% 3.68/0.98  --qbf_pred_elim                         true
% 3.68/0.98  --qbf_split                             512
% 3.68/0.98  
% 3.68/0.98  ------ BMC1 Options
% 3.68/0.98  
% 3.68/0.98  --bmc1_incremental                      false
% 3.68/0.98  --bmc1_axioms                           reachable_all
% 3.68/0.98  --bmc1_min_bound                        0
% 3.68/0.98  --bmc1_max_bound                        -1
% 3.68/0.98  --bmc1_max_bound_default                -1
% 3.68/0.98  --bmc1_symbol_reachability              true
% 3.68/0.98  --bmc1_property_lemmas                  false
% 3.68/0.98  --bmc1_k_induction                      false
% 3.68/0.98  --bmc1_non_equiv_states                 false
% 3.68/0.98  --bmc1_deadlock                         false
% 3.68/0.98  --bmc1_ucm                              false
% 3.68/0.98  --bmc1_add_unsat_core                   none
% 3.68/0.98  --bmc1_unsat_core_children              false
% 3.68/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.98  --bmc1_out_stat                         full
% 3.68/0.98  --bmc1_ground_init                      false
% 3.68/0.98  --bmc1_pre_inst_next_state              false
% 3.68/0.98  --bmc1_pre_inst_state                   false
% 3.68/0.98  --bmc1_pre_inst_reach_state             false
% 3.68/0.98  --bmc1_out_unsat_core                   false
% 3.68/0.98  --bmc1_aig_witness_out                  false
% 3.68/0.98  --bmc1_verbose                          false
% 3.68/0.98  --bmc1_dump_clauses_tptp                false
% 3.68/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.98  --bmc1_dump_file                        -
% 3.68/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.98  --bmc1_ucm_extend_mode                  1
% 3.68/0.98  --bmc1_ucm_init_mode                    2
% 3.68/0.98  --bmc1_ucm_cone_mode                    none
% 3.68/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.98  --bmc1_ucm_relax_model                  4
% 3.68/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.98  --bmc1_ucm_layered_model                none
% 3.68/0.98  --bmc1_ucm_max_lemma_size               10
% 3.68/0.98  
% 3.68/0.98  ------ AIG Options
% 3.68/0.98  
% 3.68/0.98  --aig_mode                              false
% 3.68/0.98  
% 3.68/0.98  ------ Instantiation Options
% 3.68/0.98  
% 3.68/0.98  --instantiation_flag                    true
% 3.68/0.98  --inst_sos_flag                         true
% 3.68/0.98  --inst_sos_phase                        true
% 3.68/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel_side                     num_symb
% 3.68/0.98  --inst_solver_per_active                1400
% 3.68/0.98  --inst_solver_calls_frac                1.
% 3.68/0.98  --inst_passive_queue_type               priority_queues
% 3.68/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.98  --inst_passive_queues_freq              [25;2]
% 3.68/0.98  --inst_dismatching                      true
% 3.68/0.98  --inst_eager_unprocessed_to_passive     true
% 3.68/0.98  --inst_prop_sim_given                   true
% 3.68/0.98  --inst_prop_sim_new                     false
% 3.68/0.98  --inst_subs_new                         false
% 3.68/0.98  --inst_eq_res_simp                      false
% 3.68/0.98  --inst_subs_given                       false
% 3.68/0.98  --inst_orphan_elimination               true
% 3.68/0.98  --inst_learning_loop_flag               true
% 3.68/0.98  --inst_learning_start                   3000
% 3.68/0.98  --inst_learning_factor                  2
% 3.68/0.98  --inst_start_prop_sim_after_learn       3
% 3.68/0.98  --inst_sel_renew                        solver
% 3.68/0.98  --inst_lit_activity_flag                true
% 3.68/0.98  --inst_restr_to_given                   false
% 3.68/0.98  --inst_activity_threshold               500
% 3.68/0.98  --inst_out_proof                        true
% 3.68/0.98  
% 3.68/0.98  ------ Resolution Options
% 3.68/0.98  
% 3.68/0.98  --resolution_flag                       true
% 3.68/0.98  --res_lit_sel                           adaptive
% 3.68/0.98  --res_lit_sel_side                      none
% 3.68/0.98  --res_ordering                          kbo
% 3.68/0.98  --res_to_prop_solver                    active
% 3.68/0.98  --res_prop_simpl_new                    false
% 3.68/0.98  --res_prop_simpl_given                  true
% 3.68/0.98  --res_passive_queue_type                priority_queues
% 3.68/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.98  --res_passive_queues_freq               [15;5]
% 3.68/0.98  --res_forward_subs                      full
% 3.68/0.98  --res_backward_subs                     full
% 3.68/0.98  --res_forward_subs_resolution           true
% 3.68/0.98  --res_backward_subs_resolution          true
% 3.68/0.98  --res_orphan_elimination                true
% 3.68/0.98  --res_time_limit                        2.
% 3.68/0.98  --res_out_proof                         true
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Options
% 3.68/0.98  
% 3.68/0.98  --superposition_flag                    true
% 3.68/0.98  --sup_passive_queue_type                priority_queues
% 3.68/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.98  --demod_completeness_check              fast
% 3.68/0.98  --demod_use_ground                      true
% 3.68/0.98  --sup_to_prop_solver                    passive
% 3.68/0.98  --sup_prop_simpl_new                    true
% 3.68/0.98  --sup_prop_simpl_given                  true
% 3.68/0.98  --sup_fun_splitting                     true
% 3.68/0.98  --sup_smt_interval                      50000
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Simplification Setup
% 3.68/0.98  
% 3.68/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.68/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.68/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.68/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.68/0.98  --sup_immed_triv                        [TrivRules]
% 3.68/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_immed_bw_main                     []
% 3.68/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.68/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_input_bw                          []
% 3.68/0.98  
% 3.68/0.98  ------ Combination Options
% 3.68/0.98  
% 3.68/0.98  --comb_res_mult                         3
% 3.68/0.98  --comb_sup_mult                         2
% 3.68/0.98  --comb_inst_mult                        10
% 3.68/0.98  
% 3.68/0.98  ------ Debug Options
% 3.68/0.98  
% 3.68/0.98  --dbg_backtrace                         false
% 3.68/0.98  --dbg_dump_prop_clauses                 false
% 3.68/0.98  --dbg_dump_prop_clauses_file            -
% 3.68/0.98  --dbg_out_stat                          false
% 3.68/0.98  ------ Parsing...
% 3.68/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.98  ------ Proving...
% 3.68/0.98  ------ Problem Properties 
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  clauses                                 35
% 3.68/0.98  conjectures                             3
% 3.68/0.98  EPR                                     7
% 3.68/0.98  Horn                                    29
% 3.68/0.98  unary                                   7
% 3.68/0.98  binary                                  14
% 3.68/0.98  lits                                    82
% 3.68/0.98  lits eq                                 32
% 3.68/0.98  fd_pure                                 0
% 3.68/0.98  fd_pseudo                               0
% 3.68/0.98  fd_cond                                 2
% 3.68/0.98  fd_pseudo_cond                          1
% 3.68/0.98  AC symbols                              0
% 3.68/0.98  
% 3.68/0.98  ------ Schedule dynamic 5 is on 
% 3.68/0.98  
% 3.68/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ 
% 3.68/0.98  Current options:
% 3.68/0.98  ------ 
% 3.68/0.98  
% 3.68/0.98  ------ Input Options
% 3.68/0.98  
% 3.68/0.98  --out_options                           all
% 3.68/0.98  --tptp_safe_out                         true
% 3.68/0.98  --problem_path                          ""
% 3.68/0.98  --include_path                          ""
% 3.68/0.98  --clausifier                            res/vclausify_rel
% 3.68/0.98  --clausifier_options                    ""
% 3.68/0.98  --stdin                                 false
% 3.68/0.98  --stats_out                             all
% 3.68/0.98  
% 3.68/0.98  ------ General Options
% 3.68/0.98  
% 3.68/0.98  --fof                                   false
% 3.68/0.98  --time_out_real                         305.
% 3.68/0.98  --time_out_virtual                      -1.
% 3.68/0.98  --symbol_type_check                     false
% 3.68/0.98  --clausify_out                          false
% 3.68/0.98  --sig_cnt_out                           false
% 3.68/0.98  --trig_cnt_out                          false
% 3.68/0.98  --trig_cnt_out_tolerance                1.
% 3.68/0.98  --trig_cnt_out_sk_spl                   false
% 3.68/0.98  --abstr_cl_out                          false
% 3.68/0.98  
% 3.68/0.98  ------ Global Options
% 3.68/0.98  
% 3.68/0.98  --schedule                              default
% 3.68/0.98  --add_important_lit                     false
% 3.68/0.98  --prop_solver_per_cl                    1000
% 3.68/0.98  --min_unsat_core                        false
% 3.68/0.98  --soft_assumptions                      false
% 3.68/0.98  --soft_lemma_size                       3
% 3.68/0.98  --prop_impl_unit_size                   0
% 3.68/0.98  --prop_impl_unit                        []
% 3.68/0.98  --share_sel_clauses                     true
% 3.68/0.98  --reset_solvers                         false
% 3.68/0.98  --bc_imp_inh                            [conj_cone]
% 3.68/0.98  --conj_cone_tolerance                   3.
% 3.68/0.98  --extra_neg_conj                        none
% 3.68/0.98  --large_theory_mode                     true
% 3.68/0.98  --prolific_symb_bound                   200
% 3.68/0.98  --lt_threshold                          2000
% 3.68/0.98  --clause_weak_htbl                      true
% 3.68/0.98  --gc_record_bc_elim                     false
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing Options
% 3.68/0.98  
% 3.68/0.98  --preprocessing_flag                    true
% 3.68/0.98  --time_out_prep_mult                    0.1
% 3.68/0.98  --splitting_mode                        input
% 3.68/0.98  --splitting_grd                         true
% 3.68/0.98  --splitting_cvd                         false
% 3.68/0.98  --splitting_cvd_svl                     false
% 3.68/0.98  --splitting_nvd                         32
% 3.68/0.98  --sub_typing                            true
% 3.68/0.98  --prep_gs_sim                           true
% 3.68/0.98  --prep_unflatten                        true
% 3.68/0.98  --prep_res_sim                          true
% 3.68/0.98  --prep_upred                            true
% 3.68/0.98  --prep_sem_filter                       exhaustive
% 3.68/0.98  --prep_sem_filter_out                   false
% 3.68/0.98  --pred_elim                             true
% 3.68/0.98  --res_sim_input                         true
% 3.68/0.98  --eq_ax_congr_red                       true
% 3.68/0.98  --pure_diseq_elim                       true
% 3.68/0.98  --brand_transform                       false
% 3.68/0.98  --non_eq_to_eq                          false
% 3.68/0.98  --prep_def_merge                        true
% 3.68/0.98  --prep_def_merge_prop_impl              false
% 3.68/0.98  --prep_def_merge_mbd                    true
% 3.68/0.98  --prep_def_merge_tr_red                 false
% 3.68/0.98  --prep_def_merge_tr_cl                  false
% 3.68/0.98  --smt_preprocessing                     true
% 3.68/0.98  --smt_ac_axioms                         fast
% 3.68/0.98  --preprocessed_out                      false
% 3.68/0.98  --preprocessed_stats                    false
% 3.68/0.98  
% 3.68/0.98  ------ Abstraction refinement Options
% 3.68/0.98  
% 3.68/0.98  --abstr_ref                             []
% 3.68/0.98  --abstr_ref_prep                        false
% 3.68/0.98  --abstr_ref_until_sat                   false
% 3.68/0.98  --abstr_ref_sig_restrict                funpre
% 3.68/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.98  --abstr_ref_under                       []
% 3.68/0.98  
% 3.68/0.98  ------ SAT Options
% 3.68/0.98  
% 3.68/0.98  --sat_mode                              false
% 3.68/0.98  --sat_fm_restart_options                ""
% 3.68/0.98  --sat_gr_def                            false
% 3.68/0.98  --sat_epr_types                         true
% 3.68/0.98  --sat_non_cyclic_types                  false
% 3.68/0.98  --sat_finite_models                     false
% 3.68/0.98  --sat_fm_lemmas                         false
% 3.68/0.98  --sat_fm_prep                           false
% 3.68/0.98  --sat_fm_uc_incr                        true
% 3.68/0.98  --sat_out_model                         small
% 3.68/0.98  --sat_out_clauses                       false
% 3.68/0.98  
% 3.68/0.98  ------ QBF Options
% 3.68/0.98  
% 3.68/0.98  --qbf_mode                              false
% 3.68/0.98  --qbf_elim_univ                         false
% 3.68/0.98  --qbf_dom_inst                          none
% 3.68/0.98  --qbf_dom_pre_inst                      false
% 3.68/0.98  --qbf_sk_in                             false
% 3.68/0.98  --qbf_pred_elim                         true
% 3.68/0.98  --qbf_split                             512
% 3.68/0.98  
% 3.68/0.98  ------ BMC1 Options
% 3.68/0.98  
% 3.68/0.98  --bmc1_incremental                      false
% 3.68/0.98  --bmc1_axioms                           reachable_all
% 3.68/0.98  --bmc1_min_bound                        0
% 3.68/0.98  --bmc1_max_bound                        -1
% 3.68/0.98  --bmc1_max_bound_default                -1
% 3.68/0.98  --bmc1_symbol_reachability              true
% 3.68/0.98  --bmc1_property_lemmas                  false
% 3.68/0.98  --bmc1_k_induction                      false
% 3.68/0.98  --bmc1_non_equiv_states                 false
% 3.68/0.98  --bmc1_deadlock                         false
% 3.68/0.98  --bmc1_ucm                              false
% 3.68/0.98  --bmc1_add_unsat_core                   none
% 3.68/0.98  --bmc1_unsat_core_children              false
% 3.68/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.98  --bmc1_out_stat                         full
% 3.68/0.98  --bmc1_ground_init                      false
% 3.68/0.98  --bmc1_pre_inst_next_state              false
% 3.68/0.98  --bmc1_pre_inst_state                   false
% 3.68/0.98  --bmc1_pre_inst_reach_state             false
% 3.68/0.98  --bmc1_out_unsat_core                   false
% 3.68/0.98  --bmc1_aig_witness_out                  false
% 3.68/0.98  --bmc1_verbose                          false
% 3.68/0.98  --bmc1_dump_clauses_tptp                false
% 3.68/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.98  --bmc1_dump_file                        -
% 3.68/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.98  --bmc1_ucm_extend_mode                  1
% 3.68/0.98  --bmc1_ucm_init_mode                    2
% 3.68/0.98  --bmc1_ucm_cone_mode                    none
% 3.68/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.98  --bmc1_ucm_relax_model                  4
% 3.68/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.98  --bmc1_ucm_layered_model                none
% 3.68/0.98  --bmc1_ucm_max_lemma_size               10
% 3.68/0.98  
% 3.68/0.98  ------ AIG Options
% 3.68/0.98  
% 3.68/0.98  --aig_mode                              false
% 3.68/0.98  
% 3.68/0.98  ------ Instantiation Options
% 3.68/0.98  
% 3.68/0.98  --instantiation_flag                    true
% 3.68/0.98  --inst_sos_flag                         true
% 3.68/0.98  --inst_sos_phase                        true
% 3.68/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel_side                     none
% 3.68/0.98  --inst_solver_per_active                1400
% 3.68/0.98  --inst_solver_calls_frac                1.
% 3.68/0.98  --inst_passive_queue_type               priority_queues
% 3.68/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.98  --inst_passive_queues_freq              [25;2]
% 3.68/0.98  --inst_dismatching                      true
% 3.68/0.98  --inst_eager_unprocessed_to_passive     true
% 3.68/0.98  --inst_prop_sim_given                   true
% 3.68/0.98  --inst_prop_sim_new                     false
% 3.68/0.98  --inst_subs_new                         false
% 3.68/0.98  --inst_eq_res_simp                      false
% 3.68/0.98  --inst_subs_given                       false
% 3.68/0.98  --inst_orphan_elimination               true
% 3.68/0.98  --inst_learning_loop_flag               true
% 3.68/0.98  --inst_learning_start                   3000
% 3.68/0.98  --inst_learning_factor                  2
% 3.68/0.98  --inst_start_prop_sim_after_learn       3
% 3.68/0.98  --inst_sel_renew                        solver
% 3.68/0.98  --inst_lit_activity_flag                true
% 3.68/0.98  --inst_restr_to_given                   false
% 3.68/0.98  --inst_activity_threshold               500
% 3.68/0.98  --inst_out_proof                        true
% 3.68/0.98  
% 3.68/0.98  ------ Resolution Options
% 3.68/0.98  
% 3.68/0.98  --resolution_flag                       false
% 3.68/0.98  --res_lit_sel                           adaptive
% 3.68/0.98  --res_lit_sel_side                      none
% 3.68/0.98  --res_ordering                          kbo
% 3.68/0.98  --res_to_prop_solver                    active
% 3.68/0.98  --res_prop_simpl_new                    false
% 3.68/0.98  --res_prop_simpl_given                  true
% 3.68/0.98  --res_passive_queue_type                priority_queues
% 3.68/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.98  --res_passive_queues_freq               [15;5]
% 3.68/0.98  --res_forward_subs                      full
% 3.68/0.98  --res_backward_subs                     full
% 3.68/0.98  --res_forward_subs_resolution           true
% 3.68/0.98  --res_backward_subs_resolution          true
% 3.68/0.98  --res_orphan_elimination                true
% 3.68/0.98  --res_time_limit                        2.
% 3.68/0.98  --res_out_proof                         true
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Options
% 3.68/0.98  
% 3.68/0.98  --superposition_flag                    true
% 3.68/0.98  --sup_passive_queue_type                priority_queues
% 3.68/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.98  --demod_completeness_check              fast
% 3.68/0.98  --demod_use_ground                      true
% 3.68/0.98  --sup_to_prop_solver                    passive
% 3.68/0.98  --sup_prop_simpl_new                    true
% 3.68/0.98  --sup_prop_simpl_given                  true
% 3.68/0.98  --sup_fun_splitting                     true
% 3.68/0.98  --sup_smt_interval                      50000
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Simplification Setup
% 3.68/0.98  
% 3.68/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.68/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.68/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.68/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.68/0.98  --sup_immed_triv                        [TrivRules]
% 3.68/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_immed_bw_main                     []
% 3.68/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.68/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_input_bw                          []
% 3.68/0.98  
% 3.68/0.98  ------ Combination Options
% 3.68/0.98  
% 3.68/0.98  --comb_res_mult                         3
% 3.68/0.98  --comb_sup_mult                         2
% 3.68/0.98  --comb_inst_mult                        10
% 3.68/0.98  
% 3.68/0.98  ------ Debug Options
% 3.68/0.98  
% 3.68/0.98  --dbg_backtrace                         false
% 3.68/0.98  --dbg_dump_prop_clauses                 false
% 3.68/0.98  --dbg_dump_prop_clauses_file            -
% 3.68/0.98  --dbg_out_stat                          false
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ Proving...
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  % SZS status Theorem for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  fof(f19,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f39,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.98    inference(ennf_transformation,[],[f19])).
% 3.68/0.98  
% 3.68/0.98  fof(f40,plain,(
% 3.68/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.98    inference(flattening,[],[f39])).
% 3.68/0.98  
% 3.68/0.98  fof(f55,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.98    inference(nnf_transformation,[],[f40])).
% 3.68/0.98  
% 3.68/0.98  fof(f87,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f55])).
% 3.68/0.98  
% 3.68/0.98  fof(f20,conjecture,(
% 3.68/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f21,negated_conjecture,(
% 3.68/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.68/0.98    inference(negated_conjecture,[],[f20])).
% 3.68/0.98  
% 3.68/0.98  fof(f41,plain,(
% 3.68/0.98    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.68/0.98    inference(ennf_transformation,[],[f21])).
% 3.68/0.98  
% 3.68/0.98  fof(f42,plain,(
% 3.68/0.98    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.68/0.98    inference(flattening,[],[f41])).
% 3.68/0.98  
% 3.68/0.98  fof(f56,plain,(
% 3.68/0.98    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~v1_funct_2(sK5,sK2,sK4) | ~v1_funct_1(sK5)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5))),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f57,plain,(
% 3.68/0.98    (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~v1_funct_2(sK5,sK2,sK4) | ~v1_funct_1(sK5)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)),
% 3.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f42,f56])).
% 3.68/0.98  
% 3.68/0.98  fof(f94,plain,(
% 3.68/0.98    v1_funct_2(sK5,sK2,sK3)),
% 3.68/0.98    inference(cnf_transformation,[],[f57])).
% 3.68/0.98  
% 3.68/0.98  fof(f95,plain,(
% 3.68/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.68/0.98    inference(cnf_transformation,[],[f57])).
% 3.68/0.98  
% 3.68/0.98  fof(f16,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f35,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.98    inference(ennf_transformation,[],[f16])).
% 3.68/0.98  
% 3.68/0.98  fof(f84,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f35])).
% 3.68/0.98  
% 3.68/0.98  fof(f17,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f36,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.98    inference(ennf_transformation,[],[f17])).
% 3.68/0.98  
% 3.68/0.98  fof(f85,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f36])).
% 3.68/0.98  
% 3.68/0.98  fof(f96,plain,(
% 3.68/0.98    r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4)),
% 3.68/0.98    inference(cnf_transformation,[],[f57])).
% 3.68/0.98  
% 3.68/0.98  fof(f15,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f23,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.68/0.98    inference(pure_predicate_removal,[],[f15])).
% 3.68/0.98  
% 3.68/0.98  fof(f34,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.98    inference(ennf_transformation,[],[f23])).
% 3.68/0.98  
% 3.68/0.98  fof(f83,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f34])).
% 3.68/0.98  
% 3.68/0.98  fof(f9,axiom,(
% 3.68/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f29,plain,(
% 3.68/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.68/0.98    inference(ennf_transformation,[],[f9])).
% 3.68/0.98  
% 3.68/0.98  fof(f53,plain,(
% 3.68/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.68/0.98    inference(nnf_transformation,[],[f29])).
% 3.68/0.98  
% 3.68/0.98  fof(f75,plain,(
% 3.68/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f53])).
% 3.68/0.98  
% 3.68/0.98  fof(f8,axiom,(
% 3.68/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f28,plain,(
% 3.68/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.68/0.98    inference(ennf_transformation,[],[f8])).
% 3.68/0.98  
% 3.68/0.98  fof(f74,plain,(
% 3.68/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f28])).
% 3.68/0.98  
% 3.68/0.98  fof(f10,axiom,(
% 3.68/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f77,plain,(
% 3.68/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f10])).
% 3.68/0.98  
% 3.68/0.98  fof(f18,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f37,plain,(
% 3.68/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.68/0.98    inference(ennf_transformation,[],[f18])).
% 3.68/0.98  
% 3.68/0.98  fof(f38,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.68/0.98    inference(flattening,[],[f37])).
% 3.68/0.98  
% 3.68/0.98  fof(f86,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f38])).
% 3.68/0.98  
% 3.68/0.98  fof(f89,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f55])).
% 3.68/0.98  
% 3.68/0.98  fof(f98,plain,(
% 3.68/0.98    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~v1_funct_2(sK5,sK2,sK4) | ~v1_funct_1(sK5)),
% 3.68/0.98    inference(cnf_transformation,[],[f57])).
% 3.68/0.98  
% 3.68/0.98  fof(f93,plain,(
% 3.68/0.98    v1_funct_1(sK5)),
% 3.68/0.98    inference(cnf_transformation,[],[f57])).
% 3.68/0.98  
% 3.68/0.98  fof(f97,plain,(
% 3.68/0.98    k1_xboole_0 = sK2 | k1_xboole_0 != sK3),
% 3.68/0.98    inference(cnf_transformation,[],[f57])).
% 3.68/0.98  
% 3.68/0.98  fof(f5,axiom,(
% 3.68/0.98    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f26,plain,(
% 3.68/0.98    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 3.68/0.98    inference(ennf_transformation,[],[f5])).
% 3.68/0.98  
% 3.68/0.98  fof(f68,plain,(
% 3.68/0.98    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f26])).
% 3.68/0.98  
% 3.68/0.98  fof(f101,plain,(
% 3.68/0.98    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.68/0.98    inference(equality_resolution,[],[f68])).
% 3.68/0.98  
% 3.68/0.98  fof(f1,axiom,(
% 3.68/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f24,plain,(
% 3.68/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.68/0.98    inference(ennf_transformation,[],[f1])).
% 3.68/0.98  
% 3.68/0.98  fof(f43,plain,(
% 3.68/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.68/0.98    inference(nnf_transformation,[],[f24])).
% 3.68/0.98  
% 3.68/0.98  fof(f44,plain,(
% 3.68/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.68/0.98    inference(rectify,[],[f43])).
% 3.68/0.98  
% 3.68/0.98  fof(f45,plain,(
% 3.68/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f46,plain,(
% 3.68/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).
% 3.68/0.98  
% 3.68/0.98  fof(f59,plain,(
% 3.68/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f46])).
% 3.68/0.98  
% 3.68/0.98  fof(f3,axiom,(
% 3.68/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f22,plain,(
% 3.68/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.68/0.98    inference(rectify,[],[f3])).
% 3.68/0.98  
% 3.68/0.98  fof(f25,plain,(
% 3.68/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.68/0.98    inference(ennf_transformation,[],[f22])).
% 3.68/0.98  
% 3.68/0.98  fof(f47,plain,(
% 3.68/0.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f48,plain,(
% 3.68/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f47])).
% 3.68/0.98  
% 3.68/0.98  fof(f64,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f48])).
% 3.68/0.98  
% 3.68/0.98  fof(f4,axiom,(
% 3.68/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f49,plain,(
% 3.68/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.68/0.98    inference(nnf_transformation,[],[f4])).
% 3.68/0.98  
% 3.68/0.98  fof(f50,plain,(
% 3.68/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.68/0.98    inference(flattening,[],[f49])).
% 3.68/0.98  
% 3.68/0.98  fof(f67,plain,(
% 3.68/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f50])).
% 3.68/0.98  
% 3.68/0.98  fof(f6,axiom,(
% 3.68/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f51,plain,(
% 3.68/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.68/0.98    inference(nnf_transformation,[],[f6])).
% 3.68/0.98  
% 3.68/0.98  fof(f52,plain,(
% 3.68/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.68/0.98    inference(flattening,[],[f51])).
% 3.68/0.98  
% 3.68/0.98  fof(f72,plain,(
% 3.68/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.68/0.98    inference(cnf_transformation,[],[f52])).
% 3.68/0.98  
% 3.68/0.98  fof(f102,plain,(
% 3.68/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.68/0.98    inference(equality_resolution,[],[f72])).
% 3.68/0.98  
% 3.68/0.98  fof(f70,plain,(
% 3.68/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f52])).
% 3.68/0.98  
% 3.68/0.98  fof(f71,plain,(
% 3.68/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.68/0.98    inference(cnf_transformation,[],[f52])).
% 3.68/0.98  
% 3.68/0.98  fof(f103,plain,(
% 3.68/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.68/0.98    inference(equality_resolution,[],[f71])).
% 3.68/0.98  
% 3.68/0.98  fof(f65,plain,(
% 3.68/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.68/0.98    inference(cnf_transformation,[],[f50])).
% 3.68/0.98  
% 3.68/0.98  fof(f100,plain,(
% 3.68/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.68/0.98    inference(equality_resolution,[],[f65])).
% 3.68/0.98  
% 3.68/0.98  fof(f13,axiom,(
% 3.68/0.98    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f32,plain,(
% 3.68/0.98    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.68/0.98    inference(ennf_transformation,[],[f13])).
% 3.68/0.98  
% 3.68/0.98  fof(f54,plain,(
% 3.68/0.98    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.68/0.98    inference(nnf_transformation,[],[f32])).
% 3.68/0.98  
% 3.68/0.98  fof(f80,plain,(
% 3.68/0.98    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f54])).
% 3.68/0.98  
% 3.68/0.98  fof(f90,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f55])).
% 3.68/0.98  
% 3.68/0.98  fof(f107,plain,(
% 3.68/0.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.68/0.98    inference(equality_resolution,[],[f90])).
% 3.68/0.98  
% 3.68/0.98  fof(f88,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f55])).
% 3.68/0.98  
% 3.68/0.98  fof(f108,plain,(
% 3.68/0.98    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.68/0.98    inference(equality_resolution,[],[f88])).
% 3.68/0.98  
% 3.68/0.98  fof(f81,plain,(
% 3.68/0.98    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f54])).
% 3.68/0.98  
% 3.68/0.98  cnf(c_34,plain,
% 3.68/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.68/0.98      | k1_xboole_0 = X2 ),
% 3.68/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_39,negated_conjecture,
% 3.68/0.98      ( v1_funct_2(sK5,sK2,sK3) ),
% 3.68/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_600,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.68/0.98      | sK3 != X2
% 3.68/0.98      | sK2 != X1
% 3.68/0.98      | sK5 != X0
% 3.68/0.98      | k1_xboole_0 = X2 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_34,c_39]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_601,plain,
% 3.68/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.68/0.98      | k1_relset_1(sK2,sK3,sK5) = sK2
% 3.68/0.98      | k1_xboole_0 = sK3 ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_600]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_38,negated_conjecture,
% 3.68/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.68/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_603,plain,
% 3.68/0.98      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_601,c_38]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1435,plain,
% 3.68/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_26,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1439,plain,
% 3.68/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.68/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2961,plain,
% 3.68/0.98      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1435,c_1439]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2971,plain,
% 3.68/0.98      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_603,c_2961]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_27,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1438,plain,
% 3.68/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.68/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2760,plain,
% 3.68/0.98      ( k2_relset_1(sK2,sK3,sK5) = k2_relat_1(sK5) ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1435,c_1438]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_37,negated_conjecture,
% 3.68/0.98      ( r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4) ),
% 3.68/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1436,plain,
% 3.68/0.98      ( r1_tarski(k2_relset_1(sK2,sK3,sK5),sK4) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2830,plain,
% 3.68/0.98      ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_2760,c_1436]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_25,plain,
% 3.68/0.98      ( v4_relat_1(X0,X1)
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.68/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_18,plain,
% 3.68/0.98      ( ~ v4_relat_1(X0,X1)
% 3.68/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.68/0.98      | ~ v1_relat_1(X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_428,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.68/0.98      | ~ v1_relat_1(X0) ),
% 3.68/0.98      inference(resolution,[status(thm)],[c_25,c_18]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1433,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.68/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.68/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1715,plain,
% 3.68/0.98      ( r1_tarski(k1_relat_1(sK5),sK2) = iProver_top
% 3.68/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1435,c_1433]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_43,plain,
% 3.68/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_16,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.68/0.98      | ~ v1_relat_1(X1)
% 3.68/0.98      | v1_relat_1(X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1530,plain,
% 3.68/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 3.68/0.98      | ~ v1_relat_1(X0)
% 3.68/0.98      | v1_relat_1(sK5) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1599,plain,
% 3.68/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.68/0.98      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.68/0.98      | v1_relat_1(sK5) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1530]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1765,plain,
% 3.68/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.68/0.98      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
% 3.68/0.98      | v1_relat_1(sK5) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1599]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1766,plain,
% 3.68/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.68/0.98      | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 3.68/0.98      | v1_relat_1(sK5) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1765]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_19,plain,
% 3.68/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1852,plain,
% 3.68/0.98      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_19]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1853,plain,
% 3.68/0.98      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1852]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1876,plain,
% 3.68/0.98      ( r1_tarski(k1_relat_1(sK5),sK2) = iProver_top ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_1715,c_43,c_1766,c_1853]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_28,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.68/0.98      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.68/0.98      | ~ v1_relat_1(X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1437,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.68/0.98      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.68/0.98      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.68/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2960,plain,
% 3.68/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.68/0.98      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.68/0.98      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.68/0.98      | v1_relat_1(X2) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1437,c_1439]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6045,plain,
% 3.68/0.98      ( k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5)
% 3.68/0.98      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.68/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1876,c_2960]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6422,plain,
% 3.68/0.98      ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.68/0.98      | k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5) ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_6045,c_43,c_1766,c_1853]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6423,plain,
% 3.68/0.98      ( k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5)
% 3.68/0.98      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_6422]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6429,plain,
% 3.68/0.98      ( k1_relset_1(sK2,sK4,sK5) = k1_relat_1(sK5) ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2830,c_6423]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_32,plain,
% 3.68/0.98      ( v1_funct_2(X0,X1,X2)
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | k1_relset_1(X1,X2,X0) != X1
% 3.68/0.98      | k1_xboole_0 = X2 ),
% 3.68/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_35,negated_conjecture,
% 3.68/0.98      ( ~ v1_funct_2(sK5,sK2,sK4)
% 3.68/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.68/0.98      | ~ v1_funct_1(sK5) ),
% 3.68/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_40,negated_conjecture,
% 3.68/0.98      ( v1_funct_1(sK5) ),
% 3.68/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_205,plain,
% 3.68/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.68/0.98      | ~ v1_funct_2(sK5,sK2,sK4) ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_35,c_40]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_206,negated_conjecture,
% 3.68/0.98      ( ~ v1_funct_2(sK5,sK2,sK4)
% 3.68/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_205]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_587,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.68/0.98      | k1_relset_1(X1,X2,X0) != X1
% 3.68/0.98      | sK4 != X2
% 3.68/0.98      | sK2 != X1
% 3.68/0.98      | sK5 != X0
% 3.68/0.98      | k1_xboole_0 = X2 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_32,c_206]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_588,plain,
% 3.68/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.68/0.98      | k1_relset_1(sK2,sK4,sK5) != sK2
% 3.68/0.98      | k1_xboole_0 = sK4 ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_587]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1428,plain,
% 3.68/0.98      ( k1_relset_1(sK2,sK4,sK5) != sK2
% 3.68/0.98      | k1_xboole_0 = sK4
% 3.68/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_588]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6500,plain,
% 3.68/0.98      ( k1_relat_1(sK5) != sK2
% 3.68/0.98      | sK4 = k1_xboole_0
% 3.68/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_6429,c_1428]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1505,plain,
% 3.68/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.68/0.98      | ~ r1_tarski(k2_relat_1(sK5),sK4)
% 3.68/0.98      | ~ r1_tarski(k1_relat_1(sK5),sK2)
% 3.68/0.98      | ~ v1_relat_1(sK5) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_28]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1506,plain,
% 3.68/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) = iProver_top
% 3.68/0.98      | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top
% 3.68/0.98      | r1_tarski(k1_relat_1(sK5),sK2) != iProver_top
% 3.68/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1505]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6503,plain,
% 3.68/0.98      ( sK4 = k1_xboole_0 | k1_relat_1(sK5) != sK2 ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_6500,c_43,c_1506,c_1715,c_1766,c_1853,c_2830]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6504,plain,
% 3.68/0.98      ( k1_relat_1(sK5) != sK2 | sK4 = k1_xboole_0 ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_6503]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6505,plain,
% 3.68/0.98      ( sK3 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2971,c_6504]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_36,negated_conjecture,
% 3.68/0.98      ( k1_xboole_0 != sK3 | k1_xboole_0 = sK2 ),
% 3.68/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6649,plain,
% 3.68/0.98      ( sK4 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_6505,c_36]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6655,plain,
% 3.68/0.98      ( sK2 = k1_xboole_0
% 3.68/0.98      | r1_tarski(k2_relat_1(sK5),k1_xboole_0) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_6649,c_2830]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_11,plain,
% 3.68/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1447,plain,
% 3.68/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1,plain,
% 3.68/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.68/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1455,plain,
% 3.68/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.68/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4,plain,
% 3.68/0.98      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1453,plain,
% 3.68/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 3.68/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.68/0.98      | r2_hidden(X2,X1) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3264,plain,
% 3.68/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 3.68/0.98      | r2_hidden(sK0(X0,X2),X1) != iProver_top
% 3.68/0.98      | r1_tarski(X0,X2) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1455,c_1453]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5527,plain,
% 3.68/0.98      ( r1_xboole_0(X0,X0) != iProver_top
% 3.68/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1455,c_3264]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5532,plain,
% 3.68/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1447,c_5527]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.68/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1450,plain,
% 3.68/0.98      ( X0 = X1
% 3.68/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.68/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5633,plain,
% 3.68/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_5532,c_1450]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6749,plain,
% 3.68/0.98      ( k2_relat_1(sK5) = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_6655,c_5633]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6648,plain,
% 3.68/0.98      ( sK4 = k1_xboole_0
% 3.68/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_6505,c_1435]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_12,plain,
% 3.68/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.68/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6650,plain,
% 3.68/0.98      ( sK4 = k1_xboole_0
% 3.68/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_6648,c_12]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_14,plain,
% 3.68/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.68/0.98      | k1_xboole_0 = X0
% 3.68/0.98      | k1_xboole_0 = X1 ),
% 3.68/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_104,plain,
% 3.68/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.68/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_13,plain,
% 3.68/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.68/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_105,plain,
% 3.68/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_9,plain,
% 3.68/0.98      ( r1_tarski(X0,X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_110,plain,
% 3.68/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_112,plain,
% 3.68/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_110]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_611,plain,
% 3.68/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.68/0.98      | sK3 != sK4
% 3.68/0.98      | sK2 != sK2
% 3.68/0.98      | sK5 != sK5 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_206,c_39]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_612,plain,
% 3.68/0.98      ( sK3 != sK4
% 3.68/0.98      | sK2 != sK2
% 3.68/0.98      | sK5 != sK5
% 3.68/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_920,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1516,plain,
% 3.68/0.98      ( sK3 != X0 | sK3 = sK4 | sK4 != X0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_920]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1517,plain,
% 3.68/0.98      ( sK3 = sK4 | sK3 != k1_xboole_0 | sK4 != k1_xboole_0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1516]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_919,plain,( X0 = X0 ),theory(equality) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1585,plain,
% 3.68/0.98      ( sK2 = sK2 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_919]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1666,plain,
% 3.68/0.98      ( sK5 = sK5 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_919]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_23,plain,
% 3.68/0.98      ( ~ v1_relat_1(X0)
% 3.68/0.98      | k2_relat_1(X0) = k1_xboole_0
% 3.68/0.98      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.68/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1441,plain,
% 3.68/0.98      ( k2_relat_1(X0) = k1_xboole_0
% 3.68/0.98      | k1_relat_1(X0) != k1_xboole_0
% 3.68/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3058,plain,
% 3.68/0.98      ( k2_relat_1(sK5) = k1_xboole_0
% 3.68/0.98      | sK3 = k1_xboole_0
% 3.68/0.98      | sK2 != k1_xboole_0
% 3.68/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2971,c_1441]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_921,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.68/0.98      theory(equality) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2202,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,X1)
% 3.68/0.98      | r1_tarski(k2_relat_1(X2),X3)
% 3.68/0.98      | X3 != X1
% 3.68/0.98      | k2_relat_1(X2) != X0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_921]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3470,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,X1)
% 3.68/0.98      | r1_tarski(k2_relat_1(sK5),X2)
% 3.68/0.98      | X2 != X1
% 3.68/0.98      | k2_relat_1(sK5) != X0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_2202]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3471,plain,
% 3.68/0.98      ( X0 != X1
% 3.68/0.98      | k2_relat_1(sK5) != X2
% 3.68/0.98      | r1_tarski(X2,X1) != iProver_top
% 3.68/0.98      | r1_tarski(k2_relat_1(sK5),X0) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_3470]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3473,plain,
% 3.68/0.98      ( k2_relat_1(sK5) != k1_xboole_0
% 3.68/0.98      | k1_xboole_0 != k1_xboole_0
% 3.68/0.98      | r1_tarski(k2_relat_1(sK5),k1_xboole_0) = iProver_top
% 3.68/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_3471]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2665,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.68/0.98      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.68/0.98      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.68/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_12,c_1437]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4063,plain,
% 3.68/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.68/0.98      | r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top
% 3.68/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1876,c_2665]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4273,plain,
% 3.68/0.98      ( r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top
% 3.68/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_4063,c_43,c_1766,c_1853]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4274,plain,
% 3.68/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.68/0.98      | r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_4273]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6748,plain,
% 3.68/0.98      ( sK2 = k1_xboole_0
% 3.68/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_6655,c_4274]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7026,plain,
% 3.68/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_6650,c_43,c_104,c_105,c_112,c_612,c_1506,c_1517,
% 3.68/0.99                 c_1585,c_1666,c_1715,c_1766,c_1853,c_2830,c_3058,c_3473,
% 3.68/0.99                 c_4063,c_6748]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2963,plain,
% 3.68/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.68/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_13,c_1439]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7033,plain,
% 3.68/0.99      ( k1_relset_1(k1_xboole_0,X0,sK5) = k1_relat_1(sK5) ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_7026,c_2963]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_31,plain,
% 3.68/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.68/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.68/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_558,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.68/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.68/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.68/0.99      | sK4 != X1
% 3.68/0.99      | sK2 != k1_xboole_0
% 3.68/0.99      | sK5 != X0 ),
% 3.68/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_206]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_559,plain,
% 3.68/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.68/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
% 3.68/0.99      | k1_relset_1(k1_xboole_0,sK4,sK5) != k1_xboole_0
% 3.68/0.99      | sK2 != k1_xboole_0 ),
% 3.68/0.99      inference(unflattening,[status(thm)],[c_558]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1430,plain,
% 3.68/0.99      ( k1_relset_1(k1_xboole_0,sK4,sK5) != k1_xboole_0
% 3.68/0.99      | sK2 != k1_xboole_0
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_559]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1459,plain,
% 3.68/0.99      ( k1_relset_1(k1_xboole_0,sK4,sK5) != k1_xboole_0
% 3.68/0.99      | sK2 != k1_xboole_0
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_1430,c_13]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7045,plain,
% 3.68/0.99      ( k1_relat_1(sK5) != k1_xboole_0
% 3.68/0.99      | sK2 != k1_xboole_0
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_7033,c_1459]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_33,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.68/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.68/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_574,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.68/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.68/0.99      | sK3 != X1
% 3.68/0.99      | sK2 != k1_xboole_0
% 3.68/0.99      | sK5 != X0 ),
% 3.68/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_39]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_575,plain,
% 3.68/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 3.68/0.99      | k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
% 3.68/0.99      | sK2 != k1_xboole_0 ),
% 3.68/0.99      inference(unflattening,[status(thm)],[c_574]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1429,plain,
% 3.68/0.99      ( k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
% 3.68/0.99      | sK2 != k1_xboole_0
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_575]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1457,plain,
% 3.68/0.99      ( k1_relset_1(k1_xboole_0,sK3,sK5) = k1_xboole_0
% 3.68/0.99      | sK2 != k1_xboole_0
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_1429,c_13]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7046,plain,
% 3.68/0.99      ( k1_relat_1(sK5) = k1_xboole_0
% 3.68/0.99      | sK2 != k1_xboole_0
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_7033,c_1457]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7410,plain,
% 3.68/0.99      ( k2_relat_1(sK5) = k1_xboole_0 ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_6749,c_43,c_104,c_105,c_112,c_612,c_1506,c_1517,
% 3.68/0.99                 c_1585,c_1666,c_1715,c_1766,c_1853,c_2830,c_3058,c_3473,
% 3.68/0.99                 c_4063,c_6650,c_6748,c_7045,c_7046]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_22,plain,
% 3.68/0.99      ( ~ v1_relat_1(X0)
% 3.68/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.68/0.99      | k1_relat_1(X0) = k1_xboole_0 ),
% 3.68/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1442,plain,
% 3.68/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.68/0.99      | k1_relat_1(X0) = k1_xboole_0
% 3.68/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7414,plain,
% 3.68/0.99      ( k1_relat_1(sK5) = k1_xboole_0 | v1_relat_1(sK5) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_7410,c_1442]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3186,plain,
% 3.68/0.99      ( k2_relat_1(sK5) = sK4
% 3.68/0.99      | r1_tarski(sK4,k2_relat_1(sK5)) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2830,c_1450]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_6654,plain,
% 3.68/0.99      ( k2_relat_1(sK5) = sK4
% 3.68/0.99      | sK2 = k1_xboole_0
% 3.68/0.99      | r1_tarski(k1_xboole_0,k2_relat_1(sK5)) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_6649,c_3186]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7220,plain,
% 3.68/0.99      ( k2_relat_1(sK5) = sK4
% 3.68/0.99      | r1_tarski(k1_xboole_0,k2_relat_1(sK5)) != iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_6654,c_43,c_104,c_105,c_112,c_612,c_1506,c_1517,
% 3.68/0.99                 c_1585,c_1666,c_1715,c_1766,c_1853,c_2830,c_3058,c_3473,
% 3.68/0.99                 c_4063,c_6650,c_6748,c_7045,c_7046]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7224,plain,
% 3.68/0.99      ( k2_relat_1(sK5) = sK4 ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_5532,c_7220]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7325,plain,
% 3.68/0.99      ( k1_relat_1(sK5) = k1_xboole_0
% 3.68/0.99      | sK4 != k1_xboole_0
% 3.68/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_7224,c_1442]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7412,plain,
% 3.68/0.99      ( sK4 = k1_xboole_0 ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_7410,c_7224]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7516,plain,
% 3.68/0.99      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_7414,c_43,c_104,c_105,c_112,c_612,c_1506,c_1517,
% 3.68/0.99                 c_1585,c_1666,c_1715,c_1766,c_1853,c_2830,c_3058,c_3473,
% 3.68/0.99                 c_4063,c_6649,c_6650,c_6748,c_7045,c_7046,c_7325]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7523,plain,
% 3.68/0.99      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_7516,c_2971]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(contradiction,plain,
% 3.68/0.99      ( $false ),
% 3.68/0.99      inference(minisat,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_7523,c_7412,c_7325,c_7045,c_7026,c_2830,c_1853,c_1766,
% 3.68/0.99                 c_1715,c_1666,c_1585,c_1517,c_1506,c_612,c_43]) ).
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  ------                               Statistics
% 3.68/0.99  
% 3.68/0.99  ------ General
% 3.68/0.99  
% 3.68/0.99  abstr_ref_over_cycles:                  0
% 3.68/0.99  abstr_ref_under_cycles:                 0
% 3.68/0.99  gc_basic_clause_elim:                   0
% 3.68/0.99  forced_gc_time:                         0
% 3.68/0.99  parsing_time:                           0.008
% 3.68/0.99  unif_index_cands_time:                  0.
% 3.68/0.99  unif_index_add_time:                    0.
% 3.68/0.99  orderings_time:                         0.
% 3.68/0.99  out_proof_time:                         0.025
% 3.68/0.99  total_time:                             0.299
% 3.68/0.99  num_of_symbols:                         55
% 3.68/0.99  num_of_terms:                           6370
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing
% 3.68/0.99  
% 3.68/0.99  num_of_splits:                          0
% 3.68/0.99  num_of_split_atoms:                     0
% 3.68/0.99  num_of_reused_defs:                     0
% 3.68/0.99  num_eq_ax_congr_red:                    31
% 3.68/0.99  num_of_sem_filtered_clauses:            2
% 3.68/0.99  num_of_subtypes:                        0
% 3.68/0.99  monotx_restored_types:                  0
% 3.68/0.99  sat_num_of_epr_types:                   0
% 3.68/0.99  sat_num_of_non_cyclic_types:            0
% 3.68/0.99  sat_guarded_non_collapsed_types:        0
% 3.68/0.99  num_pure_diseq_elim:                    0
% 3.68/0.99  simp_replaced_by:                       0
% 3.68/0.99  res_preprocessed:                       172
% 3.68/0.99  prep_upred:                             0
% 3.68/0.99  prep_unflattend:                        48
% 3.68/0.99  smt_new_axioms:                         0
% 3.68/0.99  pred_elim_cands:                        5
% 3.68/0.99  pred_elim:                              3
% 3.68/0.99  pred_elim_cl:                           4
% 3.68/0.99  pred_elim_cycles:                       6
% 3.68/0.99  merged_defs:                            0
% 3.68/0.99  merged_defs_ncl:                        0
% 3.68/0.99  bin_hyper_res:                          0
% 3.68/0.99  prep_cycles:                            4
% 3.68/0.99  pred_elim_time:                         0.004
% 3.68/0.99  splitting_time:                         0.
% 3.68/0.99  sem_filter_time:                        0.
% 3.68/0.99  monotx_time:                            0.
% 3.68/0.99  subtype_inf_time:                       0.
% 3.68/0.99  
% 3.68/0.99  ------ Problem properties
% 3.68/0.99  
% 3.68/0.99  clauses:                                35
% 3.68/0.99  conjectures:                            3
% 3.68/0.99  epr:                                    7
% 3.68/0.99  horn:                                   29
% 3.68/0.99  ground:                                 11
% 3.68/0.99  unary:                                  7
% 3.68/0.99  binary:                                 14
% 3.68/0.99  lits:                                   82
% 3.68/0.99  lits_eq:                                32
% 3.68/0.99  fd_pure:                                0
% 3.68/0.99  fd_pseudo:                              0
% 3.68/0.99  fd_cond:                                2
% 3.68/0.99  fd_pseudo_cond:                         1
% 3.68/0.99  ac_symbols:                             0
% 3.68/0.99  
% 3.68/0.99  ------ Propositional Solver
% 3.68/0.99  
% 3.68/0.99  prop_solver_calls:                      32
% 3.68/0.99  prop_fast_solver_calls:                 1232
% 3.68/0.99  smt_solver_calls:                       0
% 3.68/0.99  smt_fast_solver_calls:                  0
% 3.68/0.99  prop_num_of_clauses:                    3108
% 3.68/0.99  prop_preprocess_simplified:             8604
% 3.68/0.99  prop_fo_subsumed:                       25
% 3.68/0.99  prop_solver_time:                       0.
% 3.68/0.99  smt_solver_time:                        0.
% 3.68/0.99  smt_fast_solver_time:                   0.
% 3.68/0.99  prop_fast_solver_time:                  0.
% 3.68/0.99  prop_unsat_core_time:                   0.
% 3.68/0.99  
% 3.68/0.99  ------ QBF
% 3.68/0.99  
% 3.68/0.99  qbf_q_res:                              0
% 3.68/0.99  qbf_num_tautologies:                    0
% 3.68/0.99  qbf_prep_cycles:                        0
% 3.68/0.99  
% 3.68/0.99  ------ BMC1
% 3.68/0.99  
% 3.68/0.99  bmc1_current_bound:                     -1
% 3.68/0.99  bmc1_last_solved_bound:                 -1
% 3.68/0.99  bmc1_unsat_core_size:                   -1
% 3.68/0.99  bmc1_unsat_core_parents_size:           -1
% 3.68/0.99  bmc1_merge_next_fun:                    0
% 3.68/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.68/0.99  
% 3.68/0.99  ------ Instantiation
% 3.68/0.99  
% 3.68/0.99  inst_num_of_clauses:                    916
% 3.68/0.99  inst_num_in_passive:                    464
% 3.68/0.99  inst_num_in_active:                     404
% 3.68/0.99  inst_num_in_unprocessed:                48
% 3.68/0.99  inst_num_of_loops:                      620
% 3.68/0.99  inst_num_of_learning_restarts:          0
% 3.68/0.99  inst_num_moves_active_passive:          212
% 3.68/0.99  inst_lit_activity:                      0
% 3.68/0.99  inst_lit_activity_moves:                0
% 3.68/0.99  inst_num_tautologies:                   0
% 3.68/0.99  inst_num_prop_implied:                  0
% 3.68/0.99  inst_num_existing_simplified:           0
% 3.68/0.99  inst_num_eq_res_simplified:             0
% 3.68/0.99  inst_num_child_elim:                    0
% 3.68/0.99  inst_num_of_dismatching_blockings:      244
% 3.68/0.99  inst_num_of_non_proper_insts:           1213
% 3.68/0.99  inst_num_of_duplicates:                 0
% 3.68/0.99  inst_inst_num_from_inst_to_res:         0
% 3.68/0.99  inst_dismatching_checking_time:         0.
% 3.68/0.99  
% 3.68/0.99  ------ Resolution
% 3.68/0.99  
% 3.68/0.99  res_num_of_clauses:                     0
% 3.68/0.99  res_num_in_passive:                     0
% 3.68/0.99  res_num_in_active:                      0
% 3.68/0.99  res_num_of_loops:                       176
% 3.68/0.99  res_forward_subset_subsumed:            69
% 3.68/0.99  res_backward_subset_subsumed:           0
% 3.68/0.99  res_forward_subsumed:                   0
% 3.68/0.99  res_backward_subsumed:                  0
% 3.68/0.99  res_forward_subsumption_resolution:     0
% 3.68/0.99  res_backward_subsumption_resolution:    0
% 3.68/0.99  res_clause_to_clause_subsumption:       471
% 3.68/0.99  res_orphan_elimination:                 0
% 3.68/0.99  res_tautology_del:                      62
% 3.68/0.99  res_num_eq_res_simplified:              1
% 3.68/0.99  res_num_sel_changes:                    0
% 3.68/0.99  res_moves_from_active_to_pass:          0
% 3.68/0.99  
% 3.68/0.99  ------ Superposition
% 3.68/0.99  
% 3.68/0.99  sup_time_total:                         0.
% 3.68/0.99  sup_time_generating:                    0.
% 3.68/0.99  sup_time_sim_full:                      0.
% 3.68/0.99  sup_time_sim_immed:                     0.
% 3.68/0.99  
% 3.68/0.99  sup_num_of_clauses:                     133
% 3.68/0.99  sup_num_in_active:                      81
% 3.68/0.99  sup_num_in_passive:                     52
% 3.68/0.99  sup_num_of_loops:                       122
% 3.68/0.99  sup_fw_superposition:                   102
% 3.68/0.99  sup_bw_superposition:                   70
% 3.68/0.99  sup_immediate_simplified:               34
% 3.68/0.99  sup_given_eliminated:                   1
% 3.68/0.99  comparisons_done:                       0
% 3.68/0.99  comparisons_avoided:                    24
% 3.68/0.99  
% 3.68/0.99  ------ Simplifications
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  sim_fw_subset_subsumed:                 15
% 3.68/0.99  sim_bw_subset_subsumed:                 15
% 3.68/0.99  sim_fw_subsumed:                        6
% 3.68/0.99  sim_bw_subsumed:                        10
% 3.68/0.99  sim_fw_subsumption_res:                 0
% 3.68/0.99  sim_bw_subsumption_res:                 0
% 3.68/0.99  sim_tautology_del:                      6
% 3.68/0.99  sim_eq_tautology_del:                   3
% 3.68/0.99  sim_eq_res_simp:                        0
% 3.68/0.99  sim_fw_demodulated:                     11
% 3.68/0.99  sim_bw_demodulated:                     27
% 3.68/0.99  sim_light_normalised:                   10
% 3.68/0.99  sim_joinable_taut:                      0
% 3.68/0.99  sim_joinable_simp:                      0
% 3.68/0.99  sim_ac_normalised:                      0
% 3.68/0.99  sim_smt_subsumption:                    0
% 3.68/0.99  
%------------------------------------------------------------------------------
