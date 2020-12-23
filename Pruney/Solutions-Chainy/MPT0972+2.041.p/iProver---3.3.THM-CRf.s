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
% DateTime   : Thu Dec  3 12:01:16 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  162 (1686 expanded)
%              Number of clauses        :   99 ( 508 expanded)
%              Number of leaves         :   19 ( 415 expanded)
%              Depth                    :   26
%              Number of atoms          :  564 (10783 expanded)
%              Number of equality atoms :  230 (2398 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(nnf_transformation,[],[f36])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK6)
        & ! [X4] :
            ( k1_funct_1(sK6,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK6,X0,X1)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK3,sK4,sK5,X3)
          & ! [X4] :
              ( k1_funct_1(sK5,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
    & ! [X4] :
        ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
        | ~ r2_hidden(X4,sK3) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f38,f58,f57])).

fof(f97,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f98,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f59])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f53])).

fof(f80,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f96,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f93,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f86])).

fof(f100,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f99,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f81,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

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
    inference(nnf_transformation,[],[f21])).

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
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_7304,plain,
    ( ~ r2_hidden(sK1(sK5,X0),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7306,plain,
    ( ~ r2_hidden(sK1(sK5,k1_xboole_0),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_7304])).

cnf(c_7273,plain,
    ( ~ r2_hidden(sK1(sK6,X0),sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7275,plain,
    ( ~ r2_hidden(sK1(sK6,k1_xboole_0),sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_7273])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_36])).

cnf(c_516,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_518,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_516,c_35])).

cnf(c_1268,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1270,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2126,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1268,c_1270])).

cnf(c_2235,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_518,c_2126])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_39])).

cnf(c_527,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_529,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_38])).

cnf(c_1266,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2127,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1266,c_1270])).

cnf(c_2335,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_529,c_2127])).

cnf(c_21,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1272,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3243,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2235,c_1272])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_44,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_46,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1960,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2438,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1960])).

cnf(c_2439,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2438])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3185,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3186,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3185])).

cnf(c_3734,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3243,c_44,c_46,c_2439,c_3186])).

cnf(c_3735,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3734])).

cnf(c_3747,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2335,c_3735])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_41,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_43,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_25,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_33,negated_conjecture,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK6 != X0
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_433,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | sK5 != sK6 ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_1626,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1627,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK5)
    | sK5 = sK6
    | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1626])).

cnf(c_1967,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2441,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1967])).

cnf(c_2442,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2441])).

cnf(c_761,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_3561,plain,
    ( k1_relat_1(sK6) = k1_relat_1(sK5)
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_3801,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3747,c_41,c_43,c_44,c_35,c_46,c_433,c_1627,c_2439,c_2442,c_3186,c_3561])).

cnf(c_3807,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2235,c_3801])).

cnf(c_34,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1269,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3823,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = k1_funct_1(sK5,sK2(sK6,sK5))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3807,c_1269])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1273,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4253,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3823,c_1273])).

cnf(c_4254,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4253])).

cnf(c_4256,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4253,c_40,c_38,c_37,c_35,c_2438,c_2441,c_3185,c_4254])).

cnf(c_4261,plain,
    ( k1_relat_1(sK5) != sK3
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2235,c_4256])).

cnf(c_4336,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4261,c_2335])).

cnf(c_435,plain,
    ( sK5 != sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_433,c_35])).

cnf(c_4353,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4336,c_435])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1271,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2666,plain,
    ( v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1268,c_1271])).

cnf(c_4364,plain,
    ( v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4353,c_2666])).

cnf(c_4430,plain,
    ( v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4364])).

cnf(c_2667,plain,
    ( v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1266,c_1271])).

cnf(c_4363,plain,
    ( v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4353,c_2667])).

cnf(c_4429,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4363])).

cnf(c_3856,plain,
    ( ~ r2_hidden(sK1(X0,sK5),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3858,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK5),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3856])).

cnf(c_3608,plain,
    ( ~ r2_hidden(sK1(X0,sK6),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3610,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3608])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2425,plain,
    ( r1_tarski(sK5,X0)
    | r2_hidden(sK1(sK5,X0),sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2432,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | r2_hidden(sK1(sK5,k1_xboole_0),sK5) ),
    inference(instantiation,[status(thm)],[c_2425])).

cnf(c_2411,plain,
    ( r1_tarski(sK6,X0)
    | r2_hidden(sK1(sK6,X0),sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2418,plain,
    ( r1_tarski(sK6,k1_xboole_0)
    | r2_hidden(sK1(sK6,k1_xboole_0),sK6) ),
    inference(instantiation,[status(thm)],[c_2411])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1932,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1934,plain,
    ( ~ r1_tarski(sK5,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK5)
    | sK5 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1932])).

cnf(c_1913,plain,
    ( r1_tarski(X0,sK5)
    | r2_hidden(sK1(X0,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1920,plain,
    ( r1_tarski(k1_xboole_0,sK5)
    | r2_hidden(sK1(k1_xboole_0,sK5),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1913])).

cnf(c_1902,plain,
    ( r1_tarski(X0,sK6)
    | r2_hidden(sK1(X0,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1909,plain,
    ( r1_tarski(k1_xboole_0,sK6)
    | r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1902])).

cnf(c_1792,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1794,plain,
    ( ~ r1_tarski(sK6,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK6)
    | sK6 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1792])).

cnf(c_754,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1579,plain,
    ( sK6 != X0
    | sK5 != X0
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_1580,plain,
    ( sK6 != k1_xboole_0
    | sK5 = sK6
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1579])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7306,c_7275,c_4430,c_4429,c_3858,c_3610,c_2432,c_2418,c_1934,c_1920,c_1909,c_1794,c_1580,c_433,c_5,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 3.03/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/0.99  
% 3.03/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.03/0.99  
% 3.03/0.99  ------  iProver source info
% 3.03/0.99  
% 3.03/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.03/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.03/0.99  git: non_committed_changes: false
% 3.03/0.99  git: last_make_outside_of_git: false
% 3.03/0.99  
% 3.03/0.99  ------ 
% 3.03/0.99  
% 3.03/0.99  ------ Input Options
% 3.03/0.99  
% 3.03/0.99  --out_options                           all
% 3.03/0.99  --tptp_safe_out                         true
% 3.03/0.99  --problem_path                          ""
% 3.03/0.99  --include_path                          ""
% 3.03/0.99  --clausifier                            res/vclausify_rel
% 3.03/0.99  --clausifier_options                    --mode clausify
% 3.03/0.99  --stdin                                 false
% 3.03/0.99  --stats_out                             all
% 3.03/0.99  
% 3.03/0.99  ------ General Options
% 3.03/0.99  
% 3.03/0.99  --fof                                   false
% 3.03/0.99  --time_out_real                         305.
% 3.03/0.99  --time_out_virtual                      -1.
% 3.03/0.99  --symbol_type_check                     false
% 3.03/0.99  --clausify_out                          false
% 3.03/0.99  --sig_cnt_out                           false
% 3.03/0.99  --trig_cnt_out                          false
% 3.03/0.99  --trig_cnt_out_tolerance                1.
% 3.03/0.99  --trig_cnt_out_sk_spl                   false
% 3.03/0.99  --abstr_cl_out                          false
% 3.03/0.99  
% 3.03/0.99  ------ Global Options
% 3.03/0.99  
% 3.03/0.99  --schedule                              default
% 3.03/0.99  --add_important_lit                     false
% 3.03/0.99  --prop_solver_per_cl                    1000
% 3.03/0.99  --min_unsat_core                        false
% 3.03/0.99  --soft_assumptions                      false
% 3.03/0.99  --soft_lemma_size                       3
% 3.03/0.99  --prop_impl_unit_size                   0
% 3.03/0.99  --prop_impl_unit                        []
% 3.03/0.99  --share_sel_clauses                     true
% 3.03/0.99  --reset_solvers                         false
% 3.03/0.99  --bc_imp_inh                            [conj_cone]
% 3.03/0.99  --conj_cone_tolerance                   3.
% 3.03/0.99  --extra_neg_conj                        none
% 3.03/0.99  --large_theory_mode                     true
% 3.03/0.99  --prolific_symb_bound                   200
% 3.03/0.99  --lt_threshold                          2000
% 3.03/0.99  --clause_weak_htbl                      true
% 3.03/0.99  --gc_record_bc_elim                     false
% 3.03/0.99  
% 3.03/0.99  ------ Preprocessing Options
% 3.03/0.99  
% 3.03/0.99  --preprocessing_flag                    true
% 3.03/0.99  --time_out_prep_mult                    0.1
% 3.03/0.99  --splitting_mode                        input
% 3.03/0.99  --splitting_grd                         true
% 3.03/0.99  --splitting_cvd                         false
% 3.03/0.99  --splitting_cvd_svl                     false
% 3.03/0.99  --splitting_nvd                         32
% 3.03/0.99  --sub_typing                            true
% 3.03/0.99  --prep_gs_sim                           true
% 3.03/0.99  --prep_unflatten                        true
% 3.03/0.99  --prep_res_sim                          true
% 3.03/0.99  --prep_upred                            true
% 3.03/0.99  --prep_sem_filter                       exhaustive
% 3.03/0.99  --prep_sem_filter_out                   false
% 3.03/0.99  --pred_elim                             true
% 3.03/0.99  --res_sim_input                         true
% 3.03/0.99  --eq_ax_congr_red                       true
% 3.03/0.99  --pure_diseq_elim                       true
% 3.03/0.99  --brand_transform                       false
% 3.03/0.99  --non_eq_to_eq                          false
% 3.03/0.99  --prep_def_merge                        true
% 3.03/0.99  --prep_def_merge_prop_impl              false
% 3.03/0.99  --prep_def_merge_mbd                    true
% 3.03/0.99  --prep_def_merge_tr_red                 false
% 3.03/0.99  --prep_def_merge_tr_cl                  false
% 3.03/0.99  --smt_preprocessing                     true
% 3.03/0.99  --smt_ac_axioms                         fast
% 3.03/0.99  --preprocessed_out                      false
% 3.03/0.99  --preprocessed_stats                    false
% 3.03/0.99  
% 3.03/0.99  ------ Abstraction refinement Options
% 3.03/0.99  
% 3.03/0.99  --abstr_ref                             []
% 3.03/0.99  --abstr_ref_prep                        false
% 3.03/0.99  --abstr_ref_until_sat                   false
% 3.03/0.99  --abstr_ref_sig_restrict                funpre
% 3.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/0.99  --abstr_ref_under                       []
% 3.03/0.99  
% 3.03/0.99  ------ SAT Options
% 3.03/0.99  
% 3.03/0.99  --sat_mode                              false
% 3.03/0.99  --sat_fm_restart_options                ""
% 3.03/0.99  --sat_gr_def                            false
% 3.03/0.99  --sat_epr_types                         true
% 3.03/0.99  --sat_non_cyclic_types                  false
% 3.03/0.99  --sat_finite_models                     false
% 3.03/0.99  --sat_fm_lemmas                         false
% 3.03/0.99  --sat_fm_prep                           false
% 3.03/0.99  --sat_fm_uc_incr                        true
% 3.03/0.99  --sat_out_model                         small
% 3.03/0.99  --sat_out_clauses                       false
% 3.03/0.99  
% 3.03/0.99  ------ QBF Options
% 3.03/0.99  
% 3.03/0.99  --qbf_mode                              false
% 3.03/0.99  --qbf_elim_univ                         false
% 3.03/0.99  --qbf_dom_inst                          none
% 3.03/0.99  --qbf_dom_pre_inst                      false
% 3.03/0.99  --qbf_sk_in                             false
% 3.03/0.99  --qbf_pred_elim                         true
% 3.03/0.99  --qbf_split                             512
% 3.03/0.99  
% 3.03/0.99  ------ BMC1 Options
% 3.03/0.99  
% 3.03/0.99  --bmc1_incremental                      false
% 3.03/0.99  --bmc1_axioms                           reachable_all
% 3.03/0.99  --bmc1_min_bound                        0
% 3.03/0.99  --bmc1_max_bound                        -1
% 3.03/0.99  --bmc1_max_bound_default                -1
% 3.03/0.99  --bmc1_symbol_reachability              true
% 3.03/0.99  --bmc1_property_lemmas                  false
% 3.03/0.99  --bmc1_k_induction                      false
% 3.03/0.99  --bmc1_non_equiv_states                 false
% 3.03/0.99  --bmc1_deadlock                         false
% 3.03/0.99  --bmc1_ucm                              false
% 3.03/0.99  --bmc1_add_unsat_core                   none
% 3.03/0.99  --bmc1_unsat_core_children              false
% 3.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/0.99  --bmc1_out_stat                         full
% 3.03/0.99  --bmc1_ground_init                      false
% 3.03/0.99  --bmc1_pre_inst_next_state              false
% 3.03/0.99  --bmc1_pre_inst_state                   false
% 3.03/0.99  --bmc1_pre_inst_reach_state             false
% 3.03/0.99  --bmc1_out_unsat_core                   false
% 3.03/0.99  --bmc1_aig_witness_out                  false
% 3.03/0.99  --bmc1_verbose                          false
% 3.03/0.99  --bmc1_dump_clauses_tptp                false
% 3.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.03/0.99  --bmc1_dump_file                        -
% 3.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.03/0.99  --bmc1_ucm_extend_mode                  1
% 3.03/0.99  --bmc1_ucm_init_mode                    2
% 3.03/0.99  --bmc1_ucm_cone_mode                    none
% 3.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.03/0.99  --bmc1_ucm_relax_model                  4
% 3.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/0.99  --bmc1_ucm_layered_model                none
% 3.03/0.99  --bmc1_ucm_max_lemma_size               10
% 3.03/0.99  
% 3.03/0.99  ------ AIG Options
% 3.03/0.99  
% 3.03/0.99  --aig_mode                              false
% 3.03/0.99  
% 3.03/0.99  ------ Instantiation Options
% 3.03/0.99  
% 3.03/0.99  --instantiation_flag                    true
% 3.03/0.99  --inst_sos_flag                         false
% 3.03/0.99  --inst_sos_phase                        true
% 3.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/0.99  --inst_lit_sel_side                     num_symb
% 3.03/0.99  --inst_solver_per_active                1400
% 3.03/0.99  --inst_solver_calls_frac                1.
% 3.03/0.99  --inst_passive_queue_type               priority_queues
% 3.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/0.99  --inst_passive_queues_freq              [25;2]
% 3.03/0.99  --inst_dismatching                      true
% 3.03/0.99  --inst_eager_unprocessed_to_passive     true
% 3.03/0.99  --inst_prop_sim_given                   true
% 3.03/0.99  --inst_prop_sim_new                     false
% 3.03/0.99  --inst_subs_new                         false
% 3.03/0.99  --inst_eq_res_simp                      false
% 3.03/0.99  --inst_subs_given                       false
% 3.03/0.99  --inst_orphan_elimination               true
% 3.03/0.99  --inst_learning_loop_flag               true
% 3.03/0.99  --inst_learning_start                   3000
% 3.03/0.99  --inst_learning_factor                  2
% 3.03/0.99  --inst_start_prop_sim_after_learn       3
% 3.03/0.99  --inst_sel_renew                        solver
% 3.03/0.99  --inst_lit_activity_flag                true
% 3.03/0.99  --inst_restr_to_given                   false
% 3.03/0.99  --inst_activity_threshold               500
% 3.03/0.99  --inst_out_proof                        true
% 3.03/0.99  
% 3.03/0.99  ------ Resolution Options
% 3.03/0.99  
% 3.03/0.99  --resolution_flag                       true
% 3.03/0.99  --res_lit_sel                           adaptive
% 3.03/0.99  --res_lit_sel_side                      none
% 3.03/0.99  --res_ordering                          kbo
% 3.03/0.99  --res_to_prop_solver                    active
% 3.03/0.99  --res_prop_simpl_new                    false
% 3.03/0.99  --res_prop_simpl_given                  true
% 3.03/0.99  --res_passive_queue_type                priority_queues
% 3.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/0.99  --res_passive_queues_freq               [15;5]
% 3.03/0.99  --res_forward_subs                      full
% 3.03/0.99  --res_backward_subs                     full
% 3.03/0.99  --res_forward_subs_resolution           true
% 3.03/0.99  --res_backward_subs_resolution          true
% 3.03/0.99  --res_orphan_elimination                true
% 3.03/0.99  --res_time_limit                        2.
% 3.03/0.99  --res_out_proof                         true
% 3.03/0.99  
% 3.03/0.99  ------ Superposition Options
% 3.03/0.99  
% 3.03/0.99  --superposition_flag                    true
% 3.03/0.99  --sup_passive_queue_type                priority_queues
% 3.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.03/0.99  --demod_completeness_check              fast
% 3.03/0.99  --demod_use_ground                      true
% 3.03/0.99  --sup_to_prop_solver                    passive
% 3.03/0.99  --sup_prop_simpl_new                    true
% 3.03/0.99  --sup_prop_simpl_given                  true
% 3.03/0.99  --sup_fun_splitting                     false
% 3.03/0.99  --sup_smt_interval                      50000
% 3.03/0.99  
% 3.03/0.99  ------ Superposition Simplification Setup
% 3.03/0.99  
% 3.03/0.99  --sup_indices_passive                   []
% 3.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.99  --sup_full_bw                           [BwDemod]
% 3.03/0.99  --sup_immed_triv                        [TrivRules]
% 3.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.99  --sup_immed_bw_main                     []
% 3.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.99  
% 3.03/0.99  ------ Combination Options
% 3.03/0.99  
% 3.03/0.99  --comb_res_mult                         3
% 3.03/0.99  --comb_sup_mult                         2
% 3.03/0.99  --comb_inst_mult                        10
% 3.03/0.99  
% 3.03/0.99  ------ Debug Options
% 3.03/0.99  
% 3.03/0.99  --dbg_backtrace                         false
% 3.03/0.99  --dbg_dump_prop_clauses                 false
% 3.03/0.99  --dbg_dump_prop_clauses_file            -
% 3.03/0.99  --dbg_out_stat                          false
% 3.03/0.99  ------ Parsing...
% 3.03/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.03/0.99  
% 3.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.03/0.99  
% 3.03/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.03/0.99  
% 3.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.03/0.99  ------ Proving...
% 3.03/0.99  ------ Problem Properties 
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  clauses                                 35
% 3.03/0.99  conjectures                             5
% 3.03/0.99  EPR                                     8
% 3.03/0.99  Horn                                    27
% 3.03/0.99  unary                                   11
% 3.03/0.99  binary                                  8
% 3.03/0.99  lits                                    86
% 3.03/0.99  lits eq                                 29
% 3.03/0.99  fd_pure                                 0
% 3.03/0.99  fd_pseudo                               0
% 3.03/0.99  fd_cond                                 1
% 3.03/0.99  fd_pseudo_cond                          3
% 3.03/0.99  AC symbols                              0
% 3.03/0.99  
% 3.03/0.99  ------ Schedule dynamic 5 is on 
% 3.03/0.99  
% 3.03/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  ------ 
% 3.03/0.99  Current options:
% 3.03/0.99  ------ 
% 3.03/0.99  
% 3.03/0.99  ------ Input Options
% 3.03/0.99  
% 3.03/0.99  --out_options                           all
% 3.03/0.99  --tptp_safe_out                         true
% 3.03/0.99  --problem_path                          ""
% 3.03/0.99  --include_path                          ""
% 3.03/0.99  --clausifier                            res/vclausify_rel
% 3.03/0.99  --clausifier_options                    --mode clausify
% 3.03/0.99  --stdin                                 false
% 3.03/0.99  --stats_out                             all
% 3.03/0.99  
% 3.03/0.99  ------ General Options
% 3.03/0.99  
% 3.03/0.99  --fof                                   false
% 3.03/0.99  --time_out_real                         305.
% 3.03/0.99  --time_out_virtual                      -1.
% 3.03/0.99  --symbol_type_check                     false
% 3.03/0.99  --clausify_out                          false
% 3.03/0.99  --sig_cnt_out                           false
% 3.03/0.99  --trig_cnt_out                          false
% 3.03/0.99  --trig_cnt_out_tolerance                1.
% 3.03/0.99  --trig_cnt_out_sk_spl                   false
% 3.03/0.99  --abstr_cl_out                          false
% 3.03/0.99  
% 3.03/0.99  ------ Global Options
% 3.03/0.99  
% 3.03/0.99  --schedule                              default
% 3.03/0.99  --add_important_lit                     false
% 3.03/0.99  --prop_solver_per_cl                    1000
% 3.03/0.99  --min_unsat_core                        false
% 3.03/0.99  --soft_assumptions                      false
% 3.03/0.99  --soft_lemma_size                       3
% 3.03/0.99  --prop_impl_unit_size                   0
% 3.03/0.99  --prop_impl_unit                        []
% 3.03/0.99  --share_sel_clauses                     true
% 3.03/0.99  --reset_solvers                         false
% 3.03/0.99  --bc_imp_inh                            [conj_cone]
% 3.03/0.99  --conj_cone_tolerance                   3.
% 3.03/0.99  --extra_neg_conj                        none
% 3.03/0.99  --large_theory_mode                     true
% 3.03/0.99  --prolific_symb_bound                   200
% 3.03/0.99  --lt_threshold                          2000
% 3.03/0.99  --clause_weak_htbl                      true
% 3.03/0.99  --gc_record_bc_elim                     false
% 3.03/0.99  
% 3.03/0.99  ------ Preprocessing Options
% 3.03/0.99  
% 3.03/0.99  --preprocessing_flag                    true
% 3.03/0.99  --time_out_prep_mult                    0.1
% 3.03/0.99  --splitting_mode                        input
% 3.03/0.99  --splitting_grd                         true
% 3.03/0.99  --splitting_cvd                         false
% 3.03/0.99  --splitting_cvd_svl                     false
% 3.03/0.99  --splitting_nvd                         32
% 3.03/0.99  --sub_typing                            true
% 3.03/0.99  --prep_gs_sim                           true
% 3.03/0.99  --prep_unflatten                        true
% 3.03/0.99  --prep_res_sim                          true
% 3.03/0.99  --prep_upred                            true
% 3.03/0.99  --prep_sem_filter                       exhaustive
% 3.03/0.99  --prep_sem_filter_out                   false
% 3.03/0.99  --pred_elim                             true
% 3.03/0.99  --res_sim_input                         true
% 3.03/0.99  --eq_ax_congr_red                       true
% 3.03/0.99  --pure_diseq_elim                       true
% 3.03/0.99  --brand_transform                       false
% 3.03/0.99  --non_eq_to_eq                          false
% 3.03/0.99  --prep_def_merge                        true
% 3.03/0.99  --prep_def_merge_prop_impl              false
% 3.03/0.99  --prep_def_merge_mbd                    true
% 3.03/0.99  --prep_def_merge_tr_red                 false
% 3.03/0.99  --prep_def_merge_tr_cl                  false
% 3.03/0.99  --smt_preprocessing                     true
% 3.03/0.99  --smt_ac_axioms                         fast
% 3.03/0.99  --preprocessed_out                      false
% 3.03/0.99  --preprocessed_stats                    false
% 3.03/0.99  
% 3.03/0.99  ------ Abstraction refinement Options
% 3.03/0.99  
% 3.03/0.99  --abstr_ref                             []
% 3.03/0.99  --abstr_ref_prep                        false
% 3.03/0.99  --abstr_ref_until_sat                   false
% 3.03/0.99  --abstr_ref_sig_restrict                funpre
% 3.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/0.99  --abstr_ref_under                       []
% 3.03/0.99  
% 3.03/0.99  ------ SAT Options
% 3.03/0.99  
% 3.03/0.99  --sat_mode                              false
% 3.03/0.99  --sat_fm_restart_options                ""
% 3.03/0.99  --sat_gr_def                            false
% 3.03/0.99  --sat_epr_types                         true
% 3.03/0.99  --sat_non_cyclic_types                  false
% 3.03/0.99  --sat_finite_models                     false
% 3.03/0.99  --sat_fm_lemmas                         false
% 3.03/0.99  --sat_fm_prep                           false
% 3.03/0.99  --sat_fm_uc_incr                        true
% 3.03/0.99  --sat_out_model                         small
% 3.03/0.99  --sat_out_clauses                       false
% 3.03/0.99  
% 3.03/0.99  ------ QBF Options
% 3.03/0.99  
% 3.03/0.99  --qbf_mode                              false
% 3.03/0.99  --qbf_elim_univ                         false
% 3.03/0.99  --qbf_dom_inst                          none
% 3.03/0.99  --qbf_dom_pre_inst                      false
% 3.03/0.99  --qbf_sk_in                             false
% 3.03/0.99  --qbf_pred_elim                         true
% 3.03/0.99  --qbf_split                             512
% 3.03/0.99  
% 3.03/0.99  ------ BMC1 Options
% 3.03/0.99  
% 3.03/0.99  --bmc1_incremental                      false
% 3.03/0.99  --bmc1_axioms                           reachable_all
% 3.03/0.99  --bmc1_min_bound                        0
% 3.03/0.99  --bmc1_max_bound                        -1
% 3.03/0.99  --bmc1_max_bound_default                -1
% 3.03/0.99  --bmc1_symbol_reachability              true
% 3.03/0.99  --bmc1_property_lemmas                  false
% 3.03/0.99  --bmc1_k_induction                      false
% 3.03/0.99  --bmc1_non_equiv_states                 false
% 3.03/0.99  --bmc1_deadlock                         false
% 3.03/0.99  --bmc1_ucm                              false
% 3.03/0.99  --bmc1_add_unsat_core                   none
% 3.03/0.99  --bmc1_unsat_core_children              false
% 3.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/0.99  --bmc1_out_stat                         full
% 3.03/0.99  --bmc1_ground_init                      false
% 3.03/0.99  --bmc1_pre_inst_next_state              false
% 3.03/0.99  --bmc1_pre_inst_state                   false
% 3.03/0.99  --bmc1_pre_inst_reach_state             false
% 3.03/0.99  --bmc1_out_unsat_core                   false
% 3.03/0.99  --bmc1_aig_witness_out                  false
% 3.03/0.99  --bmc1_verbose                          false
% 3.03/0.99  --bmc1_dump_clauses_tptp                false
% 3.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.03/0.99  --bmc1_dump_file                        -
% 3.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.03/0.99  --bmc1_ucm_extend_mode                  1
% 3.03/0.99  --bmc1_ucm_init_mode                    2
% 3.03/0.99  --bmc1_ucm_cone_mode                    none
% 3.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.03/0.99  --bmc1_ucm_relax_model                  4
% 3.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/0.99  --bmc1_ucm_layered_model                none
% 3.03/0.99  --bmc1_ucm_max_lemma_size               10
% 3.03/0.99  
% 3.03/0.99  ------ AIG Options
% 3.03/0.99  
% 3.03/0.99  --aig_mode                              false
% 3.03/0.99  
% 3.03/0.99  ------ Instantiation Options
% 3.03/0.99  
% 3.03/0.99  --instantiation_flag                    true
% 3.03/0.99  --inst_sos_flag                         false
% 3.03/0.99  --inst_sos_phase                        true
% 3.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/0.99  --inst_lit_sel_side                     none
% 3.03/0.99  --inst_solver_per_active                1400
% 3.03/0.99  --inst_solver_calls_frac                1.
% 3.03/0.99  --inst_passive_queue_type               priority_queues
% 3.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/0.99  --inst_passive_queues_freq              [25;2]
% 3.03/0.99  --inst_dismatching                      true
% 3.03/0.99  --inst_eager_unprocessed_to_passive     true
% 3.03/0.99  --inst_prop_sim_given                   true
% 3.03/0.99  --inst_prop_sim_new                     false
% 3.03/0.99  --inst_subs_new                         false
% 3.03/0.99  --inst_eq_res_simp                      false
% 3.03/0.99  --inst_subs_given                       false
% 3.03/0.99  --inst_orphan_elimination               true
% 3.03/0.99  --inst_learning_loop_flag               true
% 3.03/0.99  --inst_learning_start                   3000
% 3.03/0.99  --inst_learning_factor                  2
% 3.03/0.99  --inst_start_prop_sim_after_learn       3
% 3.03/0.99  --inst_sel_renew                        solver
% 3.03/0.99  --inst_lit_activity_flag                true
% 3.03/0.99  --inst_restr_to_given                   false
% 3.03/0.99  --inst_activity_threshold               500
% 3.03/0.99  --inst_out_proof                        true
% 3.03/0.99  
% 3.03/0.99  ------ Resolution Options
% 3.03/0.99  
% 3.03/0.99  --resolution_flag                       false
% 3.03/0.99  --res_lit_sel                           adaptive
% 3.03/0.99  --res_lit_sel_side                      none
% 3.03/0.99  --res_ordering                          kbo
% 3.03/0.99  --res_to_prop_solver                    active
% 3.03/0.99  --res_prop_simpl_new                    false
% 3.03/0.99  --res_prop_simpl_given                  true
% 3.03/0.99  --res_passive_queue_type                priority_queues
% 3.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/0.99  --res_passive_queues_freq               [15;5]
% 3.03/0.99  --res_forward_subs                      full
% 3.03/0.99  --res_backward_subs                     full
% 3.03/0.99  --res_forward_subs_resolution           true
% 3.03/0.99  --res_backward_subs_resolution          true
% 3.03/0.99  --res_orphan_elimination                true
% 3.03/0.99  --res_time_limit                        2.
% 3.03/0.99  --res_out_proof                         true
% 3.03/0.99  
% 3.03/0.99  ------ Superposition Options
% 3.03/0.99  
% 3.03/0.99  --superposition_flag                    true
% 3.03/0.99  --sup_passive_queue_type                priority_queues
% 3.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.03/0.99  --demod_completeness_check              fast
% 3.03/0.99  --demod_use_ground                      true
% 3.03/0.99  --sup_to_prop_solver                    passive
% 3.03/0.99  --sup_prop_simpl_new                    true
% 3.03/0.99  --sup_prop_simpl_given                  true
% 3.03/0.99  --sup_fun_splitting                     false
% 3.03/0.99  --sup_smt_interval                      50000
% 3.03/0.99  
% 3.03/0.99  ------ Superposition Simplification Setup
% 3.03/0.99  
% 3.03/0.99  --sup_indices_passive                   []
% 3.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.99  --sup_full_bw                           [BwDemod]
% 3.03/0.99  --sup_immed_triv                        [TrivRules]
% 3.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.99  --sup_immed_bw_main                     []
% 3.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.99  
% 3.03/0.99  ------ Combination Options
% 3.03/0.99  
% 3.03/0.99  --comb_res_mult                         3
% 3.03/0.99  --comb_sup_mult                         2
% 3.03/0.99  --comb_inst_mult                        10
% 3.03/0.99  
% 3.03/0.99  ------ Debug Options
% 3.03/0.99  
% 3.03/0.99  --dbg_backtrace                         false
% 3.03/0.99  --dbg_dump_prop_clauses                 false
% 3.03/0.99  --dbg_dump_prop_clauses_file            -
% 3.03/0.99  --dbg_out_stat                          false
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  ------ Proving...
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  % SZS status Theorem for theBenchmark.p
% 3.03/0.99  
% 3.03/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.03/0.99  
% 3.03/0.99  fof(f1,axiom,(
% 3.03/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f39,plain,(
% 3.03/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.03/0.99    inference(nnf_transformation,[],[f1])).
% 3.03/0.99  
% 3.03/0.99  fof(f40,plain,(
% 3.03/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.03/0.99    inference(rectify,[],[f39])).
% 3.03/0.99  
% 3.03/0.99  fof(f41,plain,(
% 3.03/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f42,plain,(
% 3.03/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.03/0.99  
% 3.03/0.99  fof(f60,plain,(
% 3.03/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f42])).
% 3.03/0.99  
% 3.03/0.99  fof(f17,axiom,(
% 3.03/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f35,plain,(
% 3.03/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.99    inference(ennf_transformation,[],[f17])).
% 3.03/0.99  
% 3.03/0.99  fof(f36,plain,(
% 3.03/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.99    inference(flattening,[],[f35])).
% 3.03/0.99  
% 3.03/0.99  fof(f56,plain,(
% 3.03/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.99    inference(nnf_transformation,[],[f36])).
% 3.03/0.99  
% 3.03/0.99  fof(f87,plain,(
% 3.03/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.99    inference(cnf_transformation,[],[f56])).
% 3.03/0.99  
% 3.03/0.99  fof(f18,conjecture,(
% 3.03/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f19,negated_conjecture,(
% 3.03/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.03/0.99    inference(negated_conjecture,[],[f18])).
% 3.03/0.99  
% 3.03/0.99  fof(f37,plain,(
% 3.03/0.99    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.03/0.99    inference(ennf_transformation,[],[f19])).
% 3.03/0.99  
% 3.03/0.99  fof(f38,plain,(
% 3.03/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.03/0.99    inference(flattening,[],[f37])).
% 3.03/0.99  
% 3.03/0.99  fof(f58,plain,(
% 3.03/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK6) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK6,X0,X1) & v1_funct_1(sK6))) )),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f57,plain,(
% 3.03/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f59,plain,(
% 3.03/0.99    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 3.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f38,f58,f57])).
% 3.03/0.99  
% 3.03/0.99  fof(f97,plain,(
% 3.03/0.99    v1_funct_2(sK6,sK3,sK4)),
% 3.03/0.99    inference(cnf_transformation,[],[f59])).
% 3.03/0.99  
% 3.03/0.99  fof(f98,plain,(
% 3.03/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.03/0.99    inference(cnf_transformation,[],[f59])).
% 3.03/0.99  
% 3.03/0.99  fof(f15,axiom,(
% 3.03/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f32,plain,(
% 3.03/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.99    inference(ennf_transformation,[],[f15])).
% 3.03/0.99  
% 3.03/0.99  fof(f84,plain,(
% 3.03/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.99    inference(cnf_transformation,[],[f32])).
% 3.03/0.99  
% 3.03/0.99  fof(f94,plain,(
% 3.03/0.99    v1_funct_2(sK5,sK3,sK4)),
% 3.03/0.99    inference(cnf_transformation,[],[f59])).
% 3.03/0.99  
% 3.03/0.99  fof(f95,plain,(
% 3.03/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.03/0.99    inference(cnf_transformation,[],[f59])).
% 3.03/0.99  
% 3.03/0.99  fof(f12,axiom,(
% 3.03/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f28,plain,(
% 3.03/0.99    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.03/0.99    inference(ennf_transformation,[],[f12])).
% 3.03/0.99  
% 3.03/0.99  fof(f29,plain,(
% 3.03/0.99    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.03/0.99    inference(flattening,[],[f28])).
% 3.03/0.99  
% 3.03/0.99  fof(f53,plain,(
% 3.03/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f54,plain,(
% 3.03/0.99    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f53])).
% 3.03/0.99  
% 3.03/0.99  fof(f80,plain,(
% 3.03/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f54])).
% 3.03/0.99  
% 3.03/0.99  fof(f96,plain,(
% 3.03/0.99    v1_funct_1(sK6)),
% 3.03/0.99    inference(cnf_transformation,[],[f59])).
% 3.03/0.99  
% 3.03/0.99  fof(f8,axiom,(
% 3.03/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f24,plain,(
% 3.03/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.03/0.99    inference(ennf_transformation,[],[f8])).
% 3.03/0.99  
% 3.03/0.99  fof(f74,plain,(
% 3.03/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f24])).
% 3.03/0.99  
% 3.03/0.99  fof(f9,axiom,(
% 3.03/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f75,plain,(
% 3.03/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.03/0.99    inference(cnf_transformation,[],[f9])).
% 3.03/0.99  
% 3.03/0.99  fof(f93,plain,(
% 3.03/0.99    v1_funct_1(sK5)),
% 3.03/0.99    inference(cnf_transformation,[],[f59])).
% 3.03/0.99  
% 3.03/0.99  fof(f16,axiom,(
% 3.03/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f33,plain,(
% 3.03/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.03/0.99    inference(ennf_transformation,[],[f16])).
% 3.03/0.99  
% 3.03/0.99  fof(f34,plain,(
% 3.03/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.99    inference(flattening,[],[f33])).
% 3.03/0.99  
% 3.03/0.99  fof(f55,plain,(
% 3.03/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.99    inference(nnf_transformation,[],[f34])).
% 3.03/0.99  
% 3.03/0.99  fof(f86,plain,(
% 3.03/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.99    inference(cnf_transformation,[],[f55])).
% 3.03/0.99  
% 3.03/0.99  fof(f105,plain,(
% 3.03/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.99    inference(equality_resolution,[],[f86])).
% 3.03/0.99  
% 3.03/0.99  fof(f100,plain,(
% 3.03/0.99    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 3.03/0.99    inference(cnf_transformation,[],[f59])).
% 3.03/0.99  
% 3.03/0.99  fof(f99,plain,(
% 3.03/0.99    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f59])).
% 3.03/0.99  
% 3.03/0.99  fof(f81,plain,(
% 3.03/0.99    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f54])).
% 3.03/0.99  
% 3.03/0.99  fof(f14,axiom,(
% 3.03/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f31,plain,(
% 3.03/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.03/0.99    inference(ennf_transformation,[],[f14])).
% 3.03/0.99  
% 3.03/0.99  fof(f83,plain,(
% 3.03/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f31])).
% 3.03/0.99  
% 3.03/0.99  fof(f2,axiom,(
% 3.03/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f21,plain,(
% 3.03/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.03/0.99    inference(ennf_transformation,[],[f2])).
% 3.03/0.99  
% 3.03/0.99  fof(f43,plain,(
% 3.03/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.03/0.99    inference(nnf_transformation,[],[f21])).
% 3.03/0.99  
% 3.03/0.99  fof(f44,plain,(
% 3.03/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.03/0.99    inference(rectify,[],[f43])).
% 3.03/0.99  
% 3.03/0.99  fof(f45,plain,(
% 3.03/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f46,plain,(
% 3.03/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).
% 3.03/0.99  
% 3.03/0.99  fof(f63,plain,(
% 3.03/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f46])).
% 3.03/0.99  
% 3.03/0.99  fof(f4,axiom,(
% 3.03/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f47,plain,(
% 3.03/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.03/0.99    inference(nnf_transformation,[],[f4])).
% 3.03/0.99  
% 3.03/0.99  fof(f48,plain,(
% 3.03/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.03/0.99    inference(flattening,[],[f47])).
% 3.03/0.99  
% 3.03/0.99  fof(f68,plain,(
% 3.03/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f48])).
% 3.03/0.99  
% 3.03/0.99  fof(f3,axiom,(
% 3.03/0.99    v1_xboole_0(k1_xboole_0)),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f65,plain,(
% 3.03/0.99    v1_xboole_0(k1_xboole_0)),
% 3.03/0.99    inference(cnf_transformation,[],[f3])).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_7304,plain,
% 3.03/0.99      ( ~ r2_hidden(sK1(sK5,X0),sK5) | ~ v1_xboole_0(sK5) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_7306,plain,
% 3.03/0.99      ( ~ r2_hidden(sK1(sK5,k1_xboole_0),sK5) | ~ v1_xboole_0(sK5) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_7304]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_7273,plain,
% 3.03/0.99      ( ~ r2_hidden(sK1(sK6,X0),sK6) | ~ v1_xboole_0(sK6) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_7275,plain,
% 3.03/0.99      ( ~ r2_hidden(sK1(sK6,k1_xboole_0),sK6) | ~ v1_xboole_0(sK6) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_7273]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_32,plain,
% 3.03/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.03/0.99      | k1_xboole_0 = X2 ),
% 3.03/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_36,negated_conjecture,
% 3.03/0.99      ( v1_funct_2(sK6,sK3,sK4) ),
% 3.03/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_515,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.03/0.99      | sK6 != X0
% 3.03/0.99      | sK4 != X2
% 3.03/0.99      | sK3 != X1
% 3.03/0.99      | k1_xboole_0 = X2 ),
% 3.03/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_36]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_516,plain,
% 3.03/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.03/0.99      | k1_relset_1(sK3,sK4,sK6) = sK3
% 3.03/0.99      | k1_xboole_0 = sK4 ),
% 3.03/0.99      inference(unflattening,[status(thm)],[c_515]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_35,negated_conjecture,
% 3.03/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.03/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_518,plain,
% 3.03/0.99      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_516,c_35]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1268,plain,
% 3.03/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_24,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.03/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1270,plain,
% 3.03/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.03/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2126,plain,
% 3.03/0.99      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_1268,c_1270]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2235,plain,
% 3.03/0.99      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_518,c_2126]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_39,negated_conjecture,
% 3.03/0.99      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.03/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_526,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.03/0.99      | sK5 != X0
% 3.03/0.99      | sK4 != X2
% 3.03/0.99      | sK3 != X1
% 3.03/0.99      | k1_xboole_0 = X2 ),
% 3.03/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_39]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_527,plain,
% 3.03/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.03/0.99      | k1_relset_1(sK3,sK4,sK5) = sK3
% 3.03/0.99      | k1_xboole_0 = sK4 ),
% 3.03/0.99      inference(unflattening,[status(thm)],[c_526]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_38,negated_conjecture,
% 3.03/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.03/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_529,plain,
% 3.03/0.99      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_527,c_38]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1266,plain,
% 3.03/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2127,plain,
% 3.03/0.99      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_1266,c_1270]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2335,plain,
% 3.03/0.99      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_529,c_2127]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_21,plain,
% 3.03/0.99      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 3.03/0.99      | ~ v1_funct_1(X1)
% 3.03/0.99      | ~ v1_funct_1(X0)
% 3.03/0.99      | ~ v1_relat_1(X0)
% 3.03/0.99      | ~ v1_relat_1(X1)
% 3.03/0.99      | X1 = X0
% 3.03/0.99      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1272,plain,
% 3.03/0.99      ( X0 = X1
% 3.03/0.99      | k1_relat_1(X1) != k1_relat_1(X0)
% 3.03/0.99      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.03/0.99      | v1_funct_1(X0) != iProver_top
% 3.03/0.99      | v1_funct_1(X1) != iProver_top
% 3.03/0.99      | v1_relat_1(X1) != iProver_top
% 3.03/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3243,plain,
% 3.03/0.99      ( k1_relat_1(X0) != sK3
% 3.03/0.99      | sK6 = X0
% 3.03/0.99      | sK4 = k1_xboole_0
% 3.03/0.99      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 3.03/0.99      | v1_funct_1(X0) != iProver_top
% 3.03/0.99      | v1_funct_1(sK6) != iProver_top
% 3.03/0.99      | v1_relat_1(X0) != iProver_top
% 3.03/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_2235,c_1272]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_37,negated_conjecture,
% 3.03/0.99      ( v1_funct_1(sK6) ),
% 3.03/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_44,plain,
% 3.03/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_46,plain,
% 3.03/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_14,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.03/0.99      | ~ v1_relat_1(X1)
% 3.03/0.99      | v1_relat_1(X0) ),
% 3.03/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1960,plain,
% 3.03/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
% 3.03/0.99      | ~ v1_relat_1(X0)
% 3.03/0.99      | v1_relat_1(sK6) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2438,plain,
% 3.03/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.03/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 3.03/0.99      | v1_relat_1(sK6) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1960]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2439,plain,
% 3.03/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.03/0.99      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.03/0.99      | v1_relat_1(sK6) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_2438]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_15,plain,
% 3.03/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.03/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3185,plain,
% 3.03/0.99      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3186,plain,
% 3.03/0.99      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_3185]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3734,plain,
% 3.03/0.99      ( v1_relat_1(X0) != iProver_top
% 3.03/0.99      | k1_relat_1(X0) != sK3
% 3.03/0.99      | sK6 = X0
% 3.03/0.99      | sK4 = k1_xboole_0
% 3.03/0.99      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 3.03/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_3243,c_44,c_46,c_2439,c_3186]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3735,plain,
% 3.03/0.99      ( k1_relat_1(X0) != sK3
% 3.03/0.99      | sK6 = X0
% 3.03/0.99      | sK4 = k1_xboole_0
% 3.03/0.99      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 3.03/0.99      | v1_funct_1(X0) != iProver_top
% 3.03/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.03/0.99      inference(renaming,[status(thm)],[c_3734]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3747,plain,
% 3.03/0.99      ( sK6 = sK5
% 3.03/0.99      | sK4 = k1_xboole_0
% 3.03/0.99      | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
% 3.03/0.99      | v1_funct_1(sK5) != iProver_top
% 3.03/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_2335,c_3735]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_40,negated_conjecture,
% 3.03/0.99      ( v1_funct_1(sK5) ),
% 3.03/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_41,plain,
% 3.03/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_43,plain,
% 3.03/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_25,plain,
% 3.03/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.03/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.03/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_33,negated_conjecture,
% 3.03/0.99      ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
% 3.03/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_432,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.99      | sK6 != X0
% 3.03/0.99      | sK5 != X0
% 3.03/0.99      | sK4 != X2
% 3.03/0.99      | sK3 != X1 ),
% 3.03/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_433,plain,
% 3.03/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.03/0.99      | sK5 != sK6 ),
% 3.03/0.99      inference(unflattening,[status(thm)],[c_432]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1626,plain,
% 3.03/0.99      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
% 3.03/0.99      | ~ v1_funct_1(sK6)
% 3.03/0.99      | ~ v1_funct_1(sK5)
% 3.03/0.99      | ~ v1_relat_1(sK6)
% 3.03/0.99      | ~ v1_relat_1(sK5)
% 3.03/0.99      | k1_relat_1(sK6) != k1_relat_1(sK5)
% 3.03/0.99      | sK5 = sK6 ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1627,plain,
% 3.03/0.99      ( k1_relat_1(sK6) != k1_relat_1(sK5)
% 3.03/0.99      | sK5 = sK6
% 3.03/0.99      | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
% 3.03/0.99      | v1_funct_1(sK6) != iProver_top
% 3.03/0.99      | v1_funct_1(sK5) != iProver_top
% 3.03/0.99      | v1_relat_1(sK6) != iProver_top
% 3.03/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_1626]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1967,plain,
% 3.03/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 3.03/0.99      | ~ v1_relat_1(X0)
% 3.03/0.99      | v1_relat_1(sK5) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2441,plain,
% 3.03/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.03/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 3.03/0.99      | v1_relat_1(sK5) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1967]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2442,plain,
% 3.03/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.03/0.99      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.03/0.99      | v1_relat_1(sK5) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_2441]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_761,plain,
% 3.03/0.99      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 3.03/0.99      theory(equality) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3561,plain,
% 3.03/0.99      ( k1_relat_1(sK6) = k1_relat_1(sK5) | sK6 != sK5 ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_761]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3801,plain,
% 3.03/0.99      ( sK4 = k1_xboole_0
% 3.03/0.99      | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_3747,c_41,c_43,c_44,c_35,c_46,c_433,c_1627,c_2439,
% 3.03/0.99                 c_2442,c_3186,c_3561]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3807,plain,
% 3.03/0.99      ( sK4 = k1_xboole_0 | r2_hidden(sK2(sK6,sK5),sK3) = iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_2235,c_3801]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_34,negated_conjecture,
% 3.03/0.99      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
% 3.03/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1269,plain,
% 3.03/0.99      ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
% 3.03/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3823,plain,
% 3.03/0.99      ( k1_funct_1(sK6,sK2(sK6,sK5)) = k1_funct_1(sK5,sK2(sK6,sK5))
% 3.03/0.99      | sK4 = k1_xboole_0 ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_3807,c_1269]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_20,plain,
% 3.03/0.99      ( ~ v1_funct_1(X0)
% 3.03/0.99      | ~ v1_funct_1(X1)
% 3.03/0.99      | ~ v1_relat_1(X1)
% 3.03/0.99      | ~ v1_relat_1(X0)
% 3.03/0.99      | X0 = X1
% 3.03/0.99      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 3.03/0.99      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.03/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1273,plain,
% 3.03/0.99      ( X0 = X1
% 3.03/0.99      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 3.03/0.99      | k1_relat_1(X1) != k1_relat_1(X0)
% 3.03/0.99      | v1_funct_1(X1) != iProver_top
% 3.03/0.99      | v1_funct_1(X0) != iProver_top
% 3.03/0.99      | v1_relat_1(X0) != iProver_top
% 3.03/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4253,plain,
% 3.03/0.99      ( k1_relat_1(sK5) != k1_relat_1(sK6)
% 3.03/0.99      | sK6 = sK5
% 3.03/0.99      | sK4 = k1_xboole_0
% 3.03/0.99      | v1_funct_1(sK6) != iProver_top
% 3.03/0.99      | v1_funct_1(sK5) != iProver_top
% 3.03/0.99      | v1_relat_1(sK6) != iProver_top
% 3.03/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_3823,c_1273]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4254,plain,
% 3.03/0.99      ( ~ v1_funct_1(sK6)
% 3.03/0.99      | ~ v1_funct_1(sK5)
% 3.03/0.99      | ~ v1_relat_1(sK6)
% 3.03/0.99      | ~ v1_relat_1(sK5)
% 3.03/0.99      | k1_relat_1(sK5) != k1_relat_1(sK6)
% 3.03/0.99      | sK6 = sK5
% 3.03/0.99      | sK4 = k1_xboole_0 ),
% 3.03/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4253]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4256,plain,
% 3.03/0.99      ( k1_relat_1(sK5) != k1_relat_1(sK6)
% 3.03/0.99      | sK6 = sK5
% 3.03/0.99      | sK4 = k1_xboole_0 ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_4253,c_40,c_38,c_37,c_35,c_2438,c_2441,c_3185,c_4254]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4261,plain,
% 3.03/0.99      ( k1_relat_1(sK5) != sK3 | sK6 = sK5 | sK4 = k1_xboole_0 ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_2235,c_4256]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4336,plain,
% 3.03/0.99      ( sK6 = sK5 | sK4 = k1_xboole_0 ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_4261,c_2335]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_435,plain,
% 3.03/0.99      ( sK5 != sK6 ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_433,c_35]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4353,plain,
% 3.03/0.99      ( sK4 = k1_xboole_0 ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_4336,c_435]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_23,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.99      | ~ v1_xboole_0(X2)
% 3.03/0.99      | v1_xboole_0(X0) ),
% 3.03/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1271,plain,
% 3.03/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.03/0.99      | v1_xboole_0(X2) != iProver_top
% 3.03/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2666,plain,
% 3.03/0.99      ( v1_xboole_0(sK6) = iProver_top
% 3.03/0.99      | v1_xboole_0(sK4) != iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_1268,c_1271]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4364,plain,
% 3.03/0.99      ( v1_xboole_0(sK6) = iProver_top
% 3.03/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.03/0.99      inference(demodulation,[status(thm)],[c_4353,c_2666]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4430,plain,
% 3.03/0.99      ( v1_xboole_0(sK6) | ~ v1_xboole_0(k1_xboole_0) ),
% 3.03/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4364]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2667,plain,
% 3.03/0.99      ( v1_xboole_0(sK5) = iProver_top
% 3.03/0.99      | v1_xboole_0(sK4) != iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_1266,c_1271]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4363,plain,
% 3.03/0.99      ( v1_xboole_0(sK5) = iProver_top
% 3.03/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.03/0.99      inference(demodulation,[status(thm)],[c_4353,c_2667]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4429,plain,
% 3.03/0.99      ( v1_xboole_0(sK5) | ~ v1_xboole_0(k1_xboole_0) ),
% 3.03/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4363]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3856,plain,
% 3.03/0.99      ( ~ r2_hidden(sK1(X0,sK5),X0) | ~ v1_xboole_0(X0) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3858,plain,
% 3.03/0.99      ( ~ r2_hidden(sK1(k1_xboole_0,sK5),k1_xboole_0)
% 3.03/0.99      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_3856]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3608,plain,
% 3.03/0.99      ( ~ r2_hidden(sK1(X0,sK6),X0) | ~ v1_xboole_0(X0) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3610,plain,
% 3.03/0.99      ( ~ r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0)
% 3.03/0.99      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_3608]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3,plain,
% 3.03/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.03/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2425,plain,
% 3.03/0.99      ( r1_tarski(sK5,X0) | r2_hidden(sK1(sK5,X0),sK5) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2432,plain,
% 3.03/0.99      ( r1_tarski(sK5,k1_xboole_0)
% 3.03/0.99      | r2_hidden(sK1(sK5,k1_xboole_0),sK5) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_2425]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2411,plain,
% 3.03/0.99      ( r1_tarski(sK6,X0) | r2_hidden(sK1(sK6,X0),sK6) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2418,plain,
% 3.03/0.99      ( r1_tarski(sK6,k1_xboole_0)
% 3.03/0.99      | r2_hidden(sK1(sK6,k1_xboole_0),sK6) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_2411]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_6,plain,
% 3.03/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.03/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1932,plain,
% 3.03/0.99      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1934,plain,
% 3.03/0.99      ( ~ r1_tarski(sK5,k1_xboole_0)
% 3.03/0.99      | ~ r1_tarski(k1_xboole_0,sK5)
% 3.03/0.99      | sK5 = k1_xboole_0 ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1932]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1913,plain,
% 3.03/0.99      ( r1_tarski(X0,sK5) | r2_hidden(sK1(X0,sK5),X0) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1920,plain,
% 3.03/0.99      ( r1_tarski(k1_xboole_0,sK5)
% 3.03/0.99      | r2_hidden(sK1(k1_xboole_0,sK5),k1_xboole_0) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1913]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1902,plain,
% 3.03/0.99      ( r1_tarski(X0,sK6) | r2_hidden(sK1(X0,sK6),X0) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1909,plain,
% 3.03/0.99      ( r1_tarski(k1_xboole_0,sK6)
% 3.03/0.99      | r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1902]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1792,plain,
% 3.03/0.99      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1794,plain,
% 3.03/0.99      ( ~ r1_tarski(sK6,k1_xboole_0)
% 3.03/0.99      | ~ r1_tarski(k1_xboole_0,sK6)
% 3.03/0.99      | sK6 = k1_xboole_0 ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1792]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_754,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1579,plain,
% 3.03/0.99      ( sK6 != X0 | sK5 != X0 | sK5 = sK6 ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_754]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1580,plain,
% 3.03/0.99      ( sK6 != k1_xboole_0 | sK5 = sK6 | sK5 != k1_xboole_0 ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1579]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_5,plain,
% 3.03/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.03/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(contradiction,plain,
% 3.03/0.99      ( $false ),
% 3.03/0.99      inference(minisat,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_7306,c_7275,c_4430,c_4429,c_3858,c_3610,c_2432,c_2418,
% 3.03/0.99                 c_1934,c_1920,c_1909,c_1794,c_1580,c_433,c_5,c_35]) ).
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.03/0.99  
% 3.03/0.99  ------                               Statistics
% 3.03/0.99  
% 3.03/0.99  ------ General
% 3.03/0.99  
% 3.03/0.99  abstr_ref_over_cycles:                  0
% 3.03/0.99  abstr_ref_under_cycles:                 0
% 3.03/0.99  gc_basic_clause_elim:                   0
% 3.03/0.99  forced_gc_time:                         0
% 3.03/0.99  parsing_time:                           0.013
% 3.03/0.99  unif_index_cands_time:                  0.
% 3.03/0.99  unif_index_add_time:                    0.
% 3.03/0.99  orderings_time:                         0.
% 3.03/0.99  out_proof_time:                         0.014
% 3.03/0.99  total_time:                             0.279
% 3.03/0.99  num_of_symbols:                         54
% 3.03/0.99  num_of_terms:                           7165
% 3.03/0.99  
% 3.03/0.99  ------ Preprocessing
% 3.03/0.99  
% 3.03/0.99  num_of_splits:                          0
% 3.03/0.99  num_of_split_atoms:                     0
% 3.03/0.99  num_of_reused_defs:                     0
% 3.03/0.99  num_eq_ax_congr_red:                    31
% 3.03/0.99  num_of_sem_filtered_clauses:            1
% 3.03/0.99  num_of_subtypes:                        0
% 3.03/0.99  monotx_restored_types:                  0
% 3.03/0.99  sat_num_of_epr_types:                   0
% 3.03/0.99  sat_num_of_non_cyclic_types:            0
% 3.03/0.99  sat_guarded_non_collapsed_types:        0
% 3.03/0.99  num_pure_diseq_elim:                    0
% 3.03/0.99  simp_replaced_by:                       0
% 3.03/0.99  res_preprocessed:                       170
% 3.03/0.99  prep_upred:                             0
% 3.03/0.99  prep_unflattend:                        41
% 3.03/0.99  smt_new_axioms:                         0
% 3.03/0.99  pred_elim_cands:                        6
% 3.03/0.99  pred_elim:                              3
% 3.03/0.99  pred_elim_cl:                           5
% 3.03/0.99  pred_elim_cycles:                       5
% 3.03/0.99  merged_defs:                            0
% 3.03/0.99  merged_defs_ncl:                        0
% 3.03/0.99  bin_hyper_res:                          0
% 3.03/0.99  prep_cycles:                            4
% 3.03/0.99  pred_elim_time:                         0.005
% 3.03/0.99  splitting_time:                         0.
% 3.03/0.99  sem_filter_time:                        0.
% 3.03/0.99  monotx_time:                            0.
% 3.03/0.99  subtype_inf_time:                       0.
% 3.03/0.99  
% 3.03/0.99  ------ Problem properties
% 3.03/0.99  
% 3.03/0.99  clauses:                                35
% 3.03/0.99  conjectures:                            5
% 3.03/0.99  epr:                                    8
% 3.03/0.99  horn:                                   27
% 3.03/0.99  ground:                                 12
% 3.03/0.99  unary:                                  11
% 3.03/0.99  binary:                                 8
% 3.03/0.99  lits:                                   86
% 3.03/0.99  lits_eq:                                29
% 3.03/0.99  fd_pure:                                0
% 3.03/0.99  fd_pseudo:                              0
% 3.03/0.99  fd_cond:                                1
% 3.03/0.99  fd_pseudo_cond:                         3
% 3.03/0.99  ac_symbols:                             0
% 3.03/0.99  
% 3.03/0.99  ------ Propositional Solver
% 3.03/0.99  
% 3.03/0.99  prop_solver_calls:                      29
% 3.03/0.99  prop_fast_solver_calls:                 1219
% 3.03/0.99  smt_solver_calls:                       0
% 3.03/0.99  smt_fast_solver_calls:                  0
% 3.03/0.99  prop_num_of_clauses:                    2583
% 3.03/0.99  prop_preprocess_simplified:             7232
% 3.03/0.99  prop_fo_subsumed:                       56
% 3.03/0.99  prop_solver_time:                       0.
% 3.03/0.99  smt_solver_time:                        0.
% 3.03/0.99  smt_fast_solver_time:                   0.
% 3.03/0.99  prop_fast_solver_time:                  0.
% 3.03/0.99  prop_unsat_core_time:                   0.
% 3.03/0.99  
% 3.03/0.99  ------ QBF
% 3.03/0.99  
% 3.03/0.99  qbf_q_res:                              0
% 3.03/0.99  qbf_num_tautologies:                    0
% 3.03/0.99  qbf_prep_cycles:                        0
% 3.03/0.99  
% 3.03/0.99  ------ BMC1
% 3.03/0.99  
% 3.03/0.99  bmc1_current_bound:                     -1
% 3.03/0.99  bmc1_last_solved_bound:                 -1
% 3.03/0.99  bmc1_unsat_core_size:                   -1
% 3.03/0.99  bmc1_unsat_core_parents_size:           -1
% 3.03/0.99  bmc1_merge_next_fun:                    0
% 3.03/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.03/0.99  
% 3.03/0.99  ------ Instantiation
% 3.03/0.99  
% 3.03/0.99  inst_num_of_clauses:                    909
% 3.03/0.99  inst_num_in_passive:                    371
% 3.03/0.99  inst_num_in_active:                     421
% 3.03/0.99  inst_num_in_unprocessed:                116
% 3.03/0.99  inst_num_of_loops:                      540
% 3.03/0.99  inst_num_of_learning_restarts:          0
% 3.03/0.99  inst_num_moves_active_passive:          114
% 3.03/0.99  inst_lit_activity:                      0
% 3.03/0.99  inst_lit_activity_moves:                0
% 3.03/0.99  inst_num_tautologies:                   0
% 3.03/0.99  inst_num_prop_implied:                  0
% 3.03/0.99  inst_num_existing_simplified:           0
% 3.03/0.99  inst_num_eq_res_simplified:             0
% 3.03/0.99  inst_num_child_elim:                    0
% 3.03/0.99  inst_num_of_dismatching_blockings:      329
% 3.03/0.99  inst_num_of_non_proper_insts:           918
% 3.03/0.99  inst_num_of_duplicates:                 0
% 3.03/0.99  inst_inst_num_from_inst_to_res:         0
% 3.03/0.99  inst_dismatching_checking_time:         0.
% 3.03/0.99  
% 3.03/0.99  ------ Resolution
% 3.03/0.99  
% 3.03/0.99  res_num_of_clauses:                     0
% 3.03/0.99  res_num_in_passive:                     0
% 3.03/0.99  res_num_in_active:                      0
% 3.03/0.99  res_num_of_loops:                       174
% 3.03/0.99  res_forward_subset_subsumed:            75
% 3.03/0.99  res_backward_subset_subsumed:           0
% 3.03/0.99  res_forward_subsumed:                   0
% 3.03/0.99  res_backward_subsumed:                  0
% 3.03/0.99  res_forward_subsumption_resolution:     0
% 3.03/0.99  res_backward_subsumption_resolution:    0
% 3.03/0.99  res_clause_to_clause_subsumption:       355
% 3.03/0.99  res_orphan_elimination:                 0
% 3.03/0.99  res_tautology_del:                      49
% 3.03/0.99  res_num_eq_res_simplified:              0
% 3.03/0.99  res_num_sel_changes:                    0
% 3.03/0.99  res_moves_from_active_to_pass:          0
% 3.03/0.99  
% 3.03/0.99  ------ Superposition
% 3.03/0.99  
% 3.03/0.99  sup_time_total:                         0.
% 3.03/0.99  sup_time_generating:                    0.
% 3.03/0.99  sup_time_sim_full:                      0.
% 3.03/0.99  sup_time_sim_immed:                     0.
% 3.03/0.99  
% 3.03/0.99  sup_num_of_clauses:                     106
% 3.03/0.99  sup_num_in_active:                      67
% 3.03/0.99  sup_num_in_passive:                     39
% 3.03/0.99  sup_num_of_loops:                       106
% 3.03/0.99  sup_fw_superposition:                   93
% 3.03/0.99  sup_bw_superposition:                   87
% 3.03/0.99  sup_immediate_simplified:               44
% 3.03/0.99  sup_given_eliminated:                   1
% 3.03/0.99  comparisons_done:                       0
% 3.03/0.99  comparisons_avoided:                    18
% 3.03/0.99  
% 3.03/0.99  ------ Simplifications
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  sim_fw_subset_subsumed:                 20
% 3.03/0.99  sim_bw_subset_subsumed:                 8
% 3.03/0.99  sim_fw_subsumed:                        12
% 3.03/0.99  sim_bw_subsumed:                        4
% 3.03/0.99  sim_fw_subsumption_res:                 4
% 3.03/0.99  sim_bw_subsumption_res:                 0
% 3.03/0.99  sim_tautology_del:                      20
% 3.03/0.99  sim_eq_tautology_del:                   12
% 3.03/0.99  sim_eq_res_simp:                        2
% 3.03/0.99  sim_fw_demodulated:                     8
% 3.03/0.99  sim_bw_demodulated:                     34
% 3.03/0.99  sim_light_normalised:                   15
% 3.03/0.99  sim_joinable_taut:                      0
% 3.03/0.99  sim_joinable_simp:                      0
% 3.03/0.99  sim_ac_normalised:                      0
% 3.03/0.99  sim_smt_subsumption:                    0
% 3.03/0.99  
%------------------------------------------------------------------------------
