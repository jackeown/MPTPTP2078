%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:45 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  150 (1498 expanded)
%              Number of clauses        :   87 ( 451 expanded)
%              Number of leaves         :   18 ( 373 expanded)
%              Depth                    :   26
%              Number of atoms          :  523 (9597 expanded)
%              Number of equality atoms :  242 (2258 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK5)
        & ! [X4] :
            ( k1_funct_1(sK5,X4) = k1_funct_1(X2,X4)
            | ~ m1_subset_1(X4,X0) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK5,X0,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK2,sK3,sK4,X3)
          & ! [X4] :
              ( k1_funct_1(sK4,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,sK2) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5)
    & ! [X4] :
        ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
        | ~ m1_subset_1(X4,sK2) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f39,f38])).

fof(f69,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
            & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f34])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f72,plain,(
    ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f41,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_556,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_558,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_556,c_26])).

cnf(c_2430,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2432,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3260,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2430,c_2432])).

cnf(c_3332,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_558,c_3260])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_567,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_569,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_567,c_29])).

cnf(c_2428,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3261,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2428,c_2432])).

cnf(c_3431,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_569,c_3261])).

cnf(c_13,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2434,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3552,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3332,c_2434])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_35,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2658,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2659,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2658])).

cnf(c_5018,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3552,c_35,c_37,c_2659])).

cnf(c_5019,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5018])).

cnf(c_5031,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3431,c_5019])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_32,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_16,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_24,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != X0
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_333,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_2661,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2662,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2661])).

cnf(c_2031,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2688,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_3230,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2688])).

cnf(c_2030,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4995,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2030])).

cnf(c_5129,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5031,c_32,c_34,c_26,c_333,c_2662,c_3230,c_4995])).

cnf(c_5135,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3431,c_5129])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_182,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_1])).

cnf(c_183,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_182])).

cnf(c_2426,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_183])).

cnf(c_5157,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK1(sK4,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5135,c_2426])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2431,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6466,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5157,c_2431])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2435,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6476,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6466,c_2435])).

cnf(c_6477,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6476])).

cnf(c_6563,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6476,c_31,c_29,c_28,c_26,c_333,c_2658,c_2661,c_3230,c_4995,c_6477])).

cnf(c_6567,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3332,c_6563])).

cnf(c_6568,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6567,c_3431])).

cnf(c_6589,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6568,c_2430])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_6595,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6589,c_4])).

cnf(c_6590,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6568,c_2428])).

cnf(c_6592,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6590,c_4])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4962,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK0(sK4),sK4)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4963,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(sK0(sK4),sK4) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4962])).

cnf(c_4965,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK0(sK4),sK4) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4963])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2780,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK4)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3229,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ v1_xboole_0(sK4)
    | sK5 = sK4 ),
    inference(instantiation,[status(thm)],[c_2780])).

cnf(c_3231,plain,
    ( sK5 = sK4
    | v1_xboole_0(sK5) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3229])).

cnf(c_3146,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK0(sK5),sK5)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3147,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(sK0(sK5),sK5) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3146])).

cnf(c_3149,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK0(sK5),sK5) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3147])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2981,plain,
    ( r2_hidden(sK0(sK4),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2987,plain,
    ( r2_hidden(sK0(sK4),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2981])).

cnf(c_2811,plain,
    ( r2_hidden(sK0(sK5),sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2817,plain,
    ( r2_hidden(sK0(sK5),sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2811])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_96,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6595,c_6592,c_4995,c_4965,c_3230,c_3231,c_3149,c_2987,c_2817,c_333,c_96,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:46:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.84/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.00  
% 2.84/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.84/1.00  
% 2.84/1.00  ------  iProver source info
% 2.84/1.00  
% 2.84/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.84/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.84/1.00  git: non_committed_changes: false
% 2.84/1.00  git: last_make_outside_of_git: false
% 2.84/1.00  
% 2.84/1.00  ------ 
% 2.84/1.00  
% 2.84/1.00  ------ Input Options
% 2.84/1.00  
% 2.84/1.00  --out_options                           all
% 2.84/1.00  --tptp_safe_out                         true
% 2.84/1.00  --problem_path                          ""
% 2.84/1.00  --include_path                          ""
% 2.84/1.00  --clausifier                            res/vclausify_rel
% 2.84/1.00  --clausifier_options                    --mode clausify
% 2.84/1.00  --stdin                                 false
% 2.84/1.00  --stats_out                             all
% 2.84/1.00  
% 2.84/1.00  ------ General Options
% 2.84/1.00  
% 2.84/1.00  --fof                                   false
% 2.84/1.00  --time_out_real                         305.
% 2.84/1.00  --time_out_virtual                      -1.
% 2.84/1.00  --symbol_type_check                     false
% 2.84/1.00  --clausify_out                          false
% 2.84/1.00  --sig_cnt_out                           false
% 2.84/1.00  --trig_cnt_out                          false
% 2.84/1.00  --trig_cnt_out_tolerance                1.
% 2.84/1.00  --trig_cnt_out_sk_spl                   false
% 2.84/1.00  --abstr_cl_out                          false
% 2.84/1.00  
% 2.84/1.00  ------ Global Options
% 2.84/1.00  
% 2.84/1.00  --schedule                              default
% 2.84/1.00  --add_important_lit                     false
% 2.84/1.00  --prop_solver_per_cl                    1000
% 2.84/1.00  --min_unsat_core                        false
% 2.84/1.00  --soft_assumptions                      false
% 2.84/1.00  --soft_lemma_size                       3
% 2.84/1.00  --prop_impl_unit_size                   0
% 2.84/1.00  --prop_impl_unit                        []
% 2.84/1.00  --share_sel_clauses                     true
% 2.84/1.00  --reset_solvers                         false
% 2.84/1.00  --bc_imp_inh                            [conj_cone]
% 2.84/1.00  --conj_cone_tolerance                   3.
% 2.84/1.00  --extra_neg_conj                        none
% 2.84/1.00  --large_theory_mode                     true
% 2.84/1.00  --prolific_symb_bound                   200
% 2.84/1.00  --lt_threshold                          2000
% 2.84/1.00  --clause_weak_htbl                      true
% 2.84/1.00  --gc_record_bc_elim                     false
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing Options
% 2.84/1.00  
% 2.84/1.00  --preprocessing_flag                    true
% 2.84/1.00  --time_out_prep_mult                    0.1
% 2.84/1.00  --splitting_mode                        input
% 2.84/1.00  --splitting_grd                         true
% 2.84/1.00  --splitting_cvd                         false
% 2.84/1.00  --splitting_cvd_svl                     false
% 2.84/1.00  --splitting_nvd                         32
% 2.84/1.00  --sub_typing                            true
% 2.84/1.00  --prep_gs_sim                           true
% 2.84/1.00  --prep_unflatten                        true
% 2.84/1.00  --prep_res_sim                          true
% 2.84/1.00  --prep_upred                            true
% 2.84/1.00  --prep_sem_filter                       exhaustive
% 2.84/1.00  --prep_sem_filter_out                   false
% 2.84/1.00  --pred_elim                             true
% 2.84/1.00  --res_sim_input                         true
% 2.84/1.00  --eq_ax_congr_red                       true
% 2.84/1.00  --pure_diseq_elim                       true
% 2.84/1.00  --brand_transform                       false
% 2.84/1.00  --non_eq_to_eq                          false
% 2.84/1.00  --prep_def_merge                        true
% 2.84/1.00  --prep_def_merge_prop_impl              false
% 2.84/1.00  --prep_def_merge_mbd                    true
% 2.84/1.00  --prep_def_merge_tr_red                 false
% 2.84/1.00  --prep_def_merge_tr_cl                  false
% 2.84/1.00  --smt_preprocessing                     true
% 2.84/1.00  --smt_ac_axioms                         fast
% 2.84/1.00  --preprocessed_out                      false
% 2.84/1.00  --preprocessed_stats                    false
% 2.84/1.00  
% 2.84/1.00  ------ Abstraction refinement Options
% 2.84/1.00  
% 2.84/1.00  --abstr_ref                             []
% 2.84/1.00  --abstr_ref_prep                        false
% 2.84/1.00  --abstr_ref_until_sat                   false
% 2.84/1.00  --abstr_ref_sig_restrict                funpre
% 2.84/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/1.00  --abstr_ref_under                       []
% 2.84/1.00  
% 2.84/1.00  ------ SAT Options
% 2.84/1.00  
% 2.84/1.00  --sat_mode                              false
% 2.84/1.00  --sat_fm_restart_options                ""
% 2.84/1.00  --sat_gr_def                            false
% 2.84/1.00  --sat_epr_types                         true
% 2.84/1.00  --sat_non_cyclic_types                  false
% 2.84/1.00  --sat_finite_models                     false
% 2.84/1.00  --sat_fm_lemmas                         false
% 2.84/1.00  --sat_fm_prep                           false
% 2.84/1.00  --sat_fm_uc_incr                        true
% 2.84/1.00  --sat_out_model                         small
% 2.84/1.00  --sat_out_clauses                       false
% 2.84/1.00  
% 2.84/1.00  ------ QBF Options
% 2.84/1.00  
% 2.84/1.00  --qbf_mode                              false
% 2.84/1.00  --qbf_elim_univ                         false
% 2.84/1.00  --qbf_dom_inst                          none
% 2.84/1.00  --qbf_dom_pre_inst                      false
% 2.84/1.00  --qbf_sk_in                             false
% 2.84/1.00  --qbf_pred_elim                         true
% 2.84/1.00  --qbf_split                             512
% 2.84/1.00  
% 2.84/1.00  ------ BMC1 Options
% 2.84/1.00  
% 2.84/1.00  --bmc1_incremental                      false
% 2.84/1.00  --bmc1_axioms                           reachable_all
% 2.84/1.00  --bmc1_min_bound                        0
% 2.84/1.00  --bmc1_max_bound                        -1
% 2.84/1.00  --bmc1_max_bound_default                -1
% 2.84/1.00  --bmc1_symbol_reachability              true
% 2.84/1.00  --bmc1_property_lemmas                  false
% 2.84/1.00  --bmc1_k_induction                      false
% 2.84/1.00  --bmc1_non_equiv_states                 false
% 2.84/1.00  --bmc1_deadlock                         false
% 2.84/1.00  --bmc1_ucm                              false
% 2.84/1.00  --bmc1_add_unsat_core                   none
% 2.84/1.00  --bmc1_unsat_core_children              false
% 2.84/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/1.00  --bmc1_out_stat                         full
% 2.84/1.00  --bmc1_ground_init                      false
% 2.84/1.00  --bmc1_pre_inst_next_state              false
% 2.84/1.00  --bmc1_pre_inst_state                   false
% 2.84/1.00  --bmc1_pre_inst_reach_state             false
% 2.84/1.00  --bmc1_out_unsat_core                   false
% 2.84/1.00  --bmc1_aig_witness_out                  false
% 2.84/1.00  --bmc1_verbose                          false
% 2.84/1.00  --bmc1_dump_clauses_tptp                false
% 2.84/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.84/1.00  --bmc1_dump_file                        -
% 2.84/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.84/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.84/1.00  --bmc1_ucm_extend_mode                  1
% 2.84/1.00  --bmc1_ucm_init_mode                    2
% 2.84/1.00  --bmc1_ucm_cone_mode                    none
% 2.84/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.84/1.00  --bmc1_ucm_relax_model                  4
% 2.84/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.84/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/1.00  --bmc1_ucm_layered_model                none
% 2.84/1.00  --bmc1_ucm_max_lemma_size               10
% 2.84/1.00  
% 2.84/1.00  ------ AIG Options
% 2.84/1.00  
% 2.84/1.00  --aig_mode                              false
% 2.84/1.00  
% 2.84/1.00  ------ Instantiation Options
% 2.84/1.00  
% 2.84/1.00  --instantiation_flag                    true
% 2.84/1.00  --inst_sos_flag                         false
% 2.84/1.00  --inst_sos_phase                        true
% 2.84/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/1.00  --inst_lit_sel_side                     num_symb
% 2.84/1.00  --inst_solver_per_active                1400
% 2.84/1.00  --inst_solver_calls_frac                1.
% 2.84/1.00  --inst_passive_queue_type               priority_queues
% 2.84/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/1.00  --inst_passive_queues_freq              [25;2]
% 2.84/1.00  --inst_dismatching                      true
% 2.84/1.00  --inst_eager_unprocessed_to_passive     true
% 2.84/1.00  --inst_prop_sim_given                   true
% 2.84/1.00  --inst_prop_sim_new                     false
% 2.84/1.00  --inst_subs_new                         false
% 2.84/1.00  --inst_eq_res_simp                      false
% 2.84/1.00  --inst_subs_given                       false
% 2.84/1.00  --inst_orphan_elimination               true
% 2.84/1.00  --inst_learning_loop_flag               true
% 2.84/1.00  --inst_learning_start                   3000
% 2.84/1.00  --inst_learning_factor                  2
% 2.84/1.00  --inst_start_prop_sim_after_learn       3
% 2.84/1.00  --inst_sel_renew                        solver
% 2.84/1.00  --inst_lit_activity_flag                true
% 2.84/1.00  --inst_restr_to_given                   false
% 2.84/1.00  --inst_activity_threshold               500
% 2.84/1.00  --inst_out_proof                        true
% 2.84/1.00  
% 2.84/1.00  ------ Resolution Options
% 2.84/1.00  
% 2.84/1.00  --resolution_flag                       true
% 2.84/1.00  --res_lit_sel                           adaptive
% 2.84/1.00  --res_lit_sel_side                      none
% 2.84/1.00  --res_ordering                          kbo
% 2.84/1.00  --res_to_prop_solver                    active
% 2.84/1.00  --res_prop_simpl_new                    false
% 2.84/1.00  --res_prop_simpl_given                  true
% 2.84/1.00  --res_passive_queue_type                priority_queues
% 2.84/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/1.00  --res_passive_queues_freq               [15;5]
% 2.84/1.00  --res_forward_subs                      full
% 2.84/1.00  --res_backward_subs                     full
% 2.84/1.00  --res_forward_subs_resolution           true
% 2.84/1.00  --res_backward_subs_resolution          true
% 2.84/1.00  --res_orphan_elimination                true
% 2.84/1.00  --res_time_limit                        2.
% 2.84/1.00  --res_out_proof                         true
% 2.84/1.00  
% 2.84/1.00  ------ Superposition Options
% 2.84/1.00  
% 2.84/1.00  --superposition_flag                    true
% 2.84/1.00  --sup_passive_queue_type                priority_queues
% 2.84/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.84/1.00  --demod_completeness_check              fast
% 2.84/1.00  --demod_use_ground                      true
% 2.84/1.00  --sup_to_prop_solver                    passive
% 2.84/1.00  --sup_prop_simpl_new                    true
% 2.84/1.00  --sup_prop_simpl_given                  true
% 2.84/1.00  --sup_fun_splitting                     false
% 2.84/1.00  --sup_smt_interval                      50000
% 2.84/1.00  
% 2.84/1.00  ------ Superposition Simplification Setup
% 2.84/1.00  
% 2.84/1.00  --sup_indices_passive                   []
% 2.84/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.00  --sup_full_bw                           [BwDemod]
% 2.84/1.00  --sup_immed_triv                        [TrivRules]
% 2.84/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.00  --sup_immed_bw_main                     []
% 2.84/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.00  
% 2.84/1.00  ------ Combination Options
% 2.84/1.00  
% 2.84/1.00  --comb_res_mult                         3
% 2.84/1.00  --comb_sup_mult                         2
% 2.84/1.00  --comb_inst_mult                        10
% 2.84/1.00  
% 2.84/1.00  ------ Debug Options
% 2.84/1.00  
% 2.84/1.00  --dbg_backtrace                         false
% 2.84/1.00  --dbg_dump_prop_clauses                 false
% 2.84/1.00  --dbg_dump_prop_clauses_file            -
% 2.84/1.00  --dbg_out_stat                          false
% 2.84/1.00  ------ Parsing...
% 2.84/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.84/1.00  ------ Proving...
% 2.84/1.00  ------ Problem Properties 
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  clauses                                 28
% 2.84/1.00  conjectures                             5
% 2.84/1.00  EPR                                     10
% 2.84/1.00  Horn                                    20
% 2.84/1.00  unary                                   8
% 2.84/1.00  binary                                  8
% 2.84/1.00  lits                                    70
% 2.84/1.00  lits eq                                 28
% 2.84/1.00  fd_pure                                 0
% 2.84/1.00  fd_pseudo                               0
% 2.84/1.00  fd_cond                                 1
% 2.84/1.00  fd_pseudo_cond                          3
% 2.84/1.00  AC symbols                              0
% 2.84/1.00  
% 2.84/1.00  ------ Schedule dynamic 5 is on 
% 2.84/1.00  
% 2.84/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.84/1.00  
% 2.84/1.00  
% 2.84/1.00  ------ 
% 2.84/1.00  Current options:
% 2.84/1.00  ------ 
% 2.84/1.00  
% 2.84/1.00  ------ Input Options
% 2.84/1.00  
% 2.84/1.00  --out_options                           all
% 2.84/1.00  --tptp_safe_out                         true
% 2.84/1.00  --problem_path                          ""
% 2.84/1.00  --include_path                          ""
% 2.84/1.00  --clausifier                            res/vclausify_rel
% 2.84/1.00  --clausifier_options                    --mode clausify
% 2.84/1.00  --stdin                                 false
% 2.84/1.00  --stats_out                             all
% 2.84/1.00  
% 2.84/1.00  ------ General Options
% 2.84/1.00  
% 2.84/1.00  --fof                                   false
% 2.84/1.00  --time_out_real                         305.
% 2.84/1.00  --time_out_virtual                      -1.
% 2.84/1.00  --symbol_type_check                     false
% 2.84/1.00  --clausify_out                          false
% 2.84/1.00  --sig_cnt_out                           false
% 2.84/1.00  --trig_cnt_out                          false
% 2.84/1.00  --trig_cnt_out_tolerance                1.
% 2.84/1.00  --trig_cnt_out_sk_spl                   false
% 2.84/1.00  --abstr_cl_out                          false
% 2.84/1.00  
% 2.84/1.00  ------ Global Options
% 2.84/1.00  
% 2.84/1.00  --schedule                              default
% 2.84/1.00  --add_important_lit                     false
% 2.84/1.00  --prop_solver_per_cl                    1000
% 2.84/1.00  --min_unsat_core                        false
% 2.84/1.00  --soft_assumptions                      false
% 2.84/1.00  --soft_lemma_size                       3
% 2.84/1.00  --prop_impl_unit_size                   0
% 2.84/1.00  --prop_impl_unit                        []
% 2.84/1.00  --share_sel_clauses                     true
% 2.84/1.00  --reset_solvers                         false
% 2.84/1.00  --bc_imp_inh                            [conj_cone]
% 2.84/1.00  --conj_cone_tolerance                   3.
% 2.84/1.00  --extra_neg_conj                        none
% 2.84/1.00  --large_theory_mode                     true
% 2.84/1.00  --prolific_symb_bound                   200
% 2.84/1.00  --lt_threshold                          2000
% 2.84/1.00  --clause_weak_htbl                      true
% 2.84/1.00  --gc_record_bc_elim                     false
% 2.84/1.00  
% 2.84/1.00  ------ Preprocessing Options
% 2.84/1.00  
% 2.84/1.00  --preprocessing_flag                    true
% 2.84/1.00  --time_out_prep_mult                    0.1
% 2.84/1.00  --splitting_mode                        input
% 2.84/1.00  --splitting_grd                         true
% 2.84/1.00  --splitting_cvd                         false
% 2.84/1.00  --splitting_cvd_svl                     false
% 2.84/1.00  --splitting_nvd                         32
% 2.84/1.00  --sub_typing                            true
% 2.84/1.00  --prep_gs_sim                           true
% 2.84/1.00  --prep_unflatten                        true
% 2.84/1.00  --prep_res_sim                          true
% 2.84/1.00  --prep_upred                            true
% 2.84/1.00  --prep_sem_filter                       exhaustive
% 2.84/1.00  --prep_sem_filter_out                   false
% 2.84/1.00  --pred_elim                             true
% 2.84/1.00  --res_sim_input                         true
% 2.84/1.01  --eq_ax_congr_red                       true
% 2.84/1.01  --pure_diseq_elim                       true
% 2.84/1.01  --brand_transform                       false
% 2.84/1.01  --non_eq_to_eq                          false
% 2.84/1.01  --prep_def_merge                        true
% 2.84/1.01  --prep_def_merge_prop_impl              false
% 2.84/1.01  --prep_def_merge_mbd                    true
% 2.84/1.01  --prep_def_merge_tr_red                 false
% 2.84/1.01  --prep_def_merge_tr_cl                  false
% 2.84/1.01  --smt_preprocessing                     true
% 2.84/1.01  --smt_ac_axioms                         fast
% 2.84/1.01  --preprocessed_out                      false
% 2.84/1.01  --preprocessed_stats                    false
% 2.84/1.01  
% 2.84/1.01  ------ Abstraction refinement Options
% 2.84/1.01  
% 2.84/1.01  --abstr_ref                             []
% 2.84/1.01  --abstr_ref_prep                        false
% 2.84/1.01  --abstr_ref_until_sat                   false
% 2.84/1.01  --abstr_ref_sig_restrict                funpre
% 2.84/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/1.01  --abstr_ref_under                       []
% 2.84/1.01  
% 2.84/1.01  ------ SAT Options
% 2.84/1.01  
% 2.84/1.01  --sat_mode                              false
% 2.84/1.01  --sat_fm_restart_options                ""
% 2.84/1.01  --sat_gr_def                            false
% 2.84/1.01  --sat_epr_types                         true
% 2.84/1.01  --sat_non_cyclic_types                  false
% 2.84/1.01  --sat_finite_models                     false
% 2.84/1.01  --sat_fm_lemmas                         false
% 2.84/1.01  --sat_fm_prep                           false
% 2.84/1.01  --sat_fm_uc_incr                        true
% 2.84/1.01  --sat_out_model                         small
% 2.84/1.01  --sat_out_clauses                       false
% 2.84/1.01  
% 2.84/1.01  ------ QBF Options
% 2.84/1.01  
% 2.84/1.01  --qbf_mode                              false
% 2.84/1.01  --qbf_elim_univ                         false
% 2.84/1.01  --qbf_dom_inst                          none
% 2.84/1.01  --qbf_dom_pre_inst                      false
% 2.84/1.01  --qbf_sk_in                             false
% 2.84/1.01  --qbf_pred_elim                         true
% 2.84/1.01  --qbf_split                             512
% 2.84/1.01  
% 2.84/1.01  ------ BMC1 Options
% 2.84/1.01  
% 2.84/1.01  --bmc1_incremental                      false
% 2.84/1.01  --bmc1_axioms                           reachable_all
% 2.84/1.01  --bmc1_min_bound                        0
% 2.84/1.01  --bmc1_max_bound                        -1
% 2.84/1.01  --bmc1_max_bound_default                -1
% 2.84/1.01  --bmc1_symbol_reachability              true
% 2.84/1.01  --bmc1_property_lemmas                  false
% 2.84/1.01  --bmc1_k_induction                      false
% 2.84/1.01  --bmc1_non_equiv_states                 false
% 2.84/1.01  --bmc1_deadlock                         false
% 2.84/1.01  --bmc1_ucm                              false
% 2.84/1.01  --bmc1_add_unsat_core                   none
% 2.84/1.01  --bmc1_unsat_core_children              false
% 2.84/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/1.01  --bmc1_out_stat                         full
% 2.84/1.01  --bmc1_ground_init                      false
% 2.84/1.01  --bmc1_pre_inst_next_state              false
% 2.84/1.01  --bmc1_pre_inst_state                   false
% 2.84/1.01  --bmc1_pre_inst_reach_state             false
% 2.84/1.01  --bmc1_out_unsat_core                   false
% 2.84/1.01  --bmc1_aig_witness_out                  false
% 2.84/1.01  --bmc1_verbose                          false
% 2.84/1.01  --bmc1_dump_clauses_tptp                false
% 2.84/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.84/1.01  --bmc1_dump_file                        -
% 2.84/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.84/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.84/1.01  --bmc1_ucm_extend_mode                  1
% 2.84/1.01  --bmc1_ucm_init_mode                    2
% 2.84/1.01  --bmc1_ucm_cone_mode                    none
% 2.84/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.84/1.01  --bmc1_ucm_relax_model                  4
% 2.84/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.84/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/1.01  --bmc1_ucm_layered_model                none
% 2.84/1.01  --bmc1_ucm_max_lemma_size               10
% 2.84/1.01  
% 2.84/1.01  ------ AIG Options
% 2.84/1.01  
% 2.84/1.01  --aig_mode                              false
% 2.84/1.01  
% 2.84/1.01  ------ Instantiation Options
% 2.84/1.01  
% 2.84/1.01  --instantiation_flag                    true
% 2.84/1.01  --inst_sos_flag                         false
% 2.84/1.01  --inst_sos_phase                        true
% 2.84/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/1.01  --inst_lit_sel_side                     none
% 2.84/1.01  --inst_solver_per_active                1400
% 2.84/1.01  --inst_solver_calls_frac                1.
% 2.84/1.01  --inst_passive_queue_type               priority_queues
% 2.84/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/1.01  --inst_passive_queues_freq              [25;2]
% 2.84/1.01  --inst_dismatching                      true
% 2.84/1.01  --inst_eager_unprocessed_to_passive     true
% 2.84/1.01  --inst_prop_sim_given                   true
% 2.84/1.01  --inst_prop_sim_new                     false
% 2.84/1.01  --inst_subs_new                         false
% 2.84/1.01  --inst_eq_res_simp                      false
% 2.84/1.01  --inst_subs_given                       false
% 2.84/1.01  --inst_orphan_elimination               true
% 2.84/1.01  --inst_learning_loop_flag               true
% 2.84/1.01  --inst_learning_start                   3000
% 2.84/1.01  --inst_learning_factor                  2
% 2.84/1.01  --inst_start_prop_sim_after_learn       3
% 2.84/1.01  --inst_sel_renew                        solver
% 2.84/1.01  --inst_lit_activity_flag                true
% 2.84/1.01  --inst_restr_to_given                   false
% 2.84/1.01  --inst_activity_threshold               500
% 2.84/1.01  --inst_out_proof                        true
% 2.84/1.01  
% 2.84/1.01  ------ Resolution Options
% 2.84/1.01  
% 2.84/1.01  --resolution_flag                       false
% 2.84/1.01  --res_lit_sel                           adaptive
% 2.84/1.01  --res_lit_sel_side                      none
% 2.84/1.01  --res_ordering                          kbo
% 2.84/1.01  --res_to_prop_solver                    active
% 2.84/1.01  --res_prop_simpl_new                    false
% 2.84/1.01  --res_prop_simpl_given                  true
% 2.84/1.01  --res_passive_queue_type                priority_queues
% 2.84/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/1.01  --res_passive_queues_freq               [15;5]
% 2.84/1.01  --res_forward_subs                      full
% 2.84/1.01  --res_backward_subs                     full
% 2.84/1.01  --res_forward_subs_resolution           true
% 2.84/1.01  --res_backward_subs_resolution          true
% 2.84/1.01  --res_orphan_elimination                true
% 2.84/1.01  --res_time_limit                        2.
% 2.84/1.01  --res_out_proof                         true
% 2.84/1.01  
% 2.84/1.01  ------ Superposition Options
% 2.84/1.01  
% 2.84/1.01  --superposition_flag                    true
% 2.84/1.01  --sup_passive_queue_type                priority_queues
% 2.84/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.84/1.01  --demod_completeness_check              fast
% 2.84/1.01  --demod_use_ground                      true
% 2.84/1.01  --sup_to_prop_solver                    passive
% 2.84/1.01  --sup_prop_simpl_new                    true
% 2.84/1.01  --sup_prop_simpl_given                  true
% 2.84/1.01  --sup_fun_splitting                     false
% 2.84/1.01  --sup_smt_interval                      50000
% 2.84/1.01  
% 2.84/1.01  ------ Superposition Simplification Setup
% 2.84/1.01  
% 2.84/1.01  --sup_indices_passive                   []
% 2.84/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.01  --sup_full_bw                           [BwDemod]
% 2.84/1.01  --sup_immed_triv                        [TrivRules]
% 2.84/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.01  --sup_immed_bw_main                     []
% 2.84/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.01  
% 2.84/1.01  ------ Combination Options
% 2.84/1.01  
% 2.84/1.01  --comb_res_mult                         3
% 2.84/1.01  --comb_sup_mult                         2
% 2.84/1.01  --comb_inst_mult                        10
% 2.84/1.01  
% 2.84/1.01  ------ Debug Options
% 2.84/1.01  
% 2.84/1.01  --dbg_backtrace                         false
% 2.84/1.01  --dbg_dump_prop_clauses                 false
% 2.84/1.01  --dbg_dump_prop_clauses_file            -
% 2.84/1.01  --dbg_out_stat                          false
% 2.84/1.01  
% 2.84/1.01  
% 2.84/1.01  
% 2.84/1.01  
% 2.84/1.01  ------ Proving...
% 2.84/1.01  
% 2.84/1.01  
% 2.84/1.01  % SZS status Theorem for theBenchmark.p
% 2.84/1.01  
% 2.84/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.84/1.01  
% 2.84/1.01  fof(f11,axiom,(
% 2.84/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.84/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/1.01  
% 2.84/1.01  fof(f23,plain,(
% 2.84/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/1.01    inference(ennf_transformation,[],[f11])).
% 2.84/1.01  
% 2.84/1.01  fof(f24,plain,(
% 2.84/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/1.01    inference(flattening,[],[f23])).
% 2.84/1.01  
% 2.84/1.01  fof(f37,plain,(
% 2.84/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/1.01    inference(nnf_transformation,[],[f24])).
% 2.84/1.01  
% 2.84/1.01  fof(f59,plain,(
% 2.84/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/1.01    inference(cnf_transformation,[],[f37])).
% 2.84/1.01  
% 2.84/1.01  fof(f12,conjecture,(
% 2.84/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.84/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/1.01  
% 2.84/1.01  fof(f13,negated_conjecture,(
% 2.84/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.84/1.01    inference(negated_conjecture,[],[f12])).
% 2.84/1.01  
% 2.84/1.01  fof(f25,plain,(
% 2.84/1.01    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.84/1.01    inference(ennf_transformation,[],[f13])).
% 2.84/1.01  
% 2.84/1.01  fof(f26,plain,(
% 2.84/1.01    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.84/1.01    inference(flattening,[],[f25])).
% 2.84/1.01  
% 2.84/1.01  fof(f39,plain,(
% 2.84/1.01    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK5) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X2,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 2.84/1.01    introduced(choice_axiom,[])).
% 2.84/1.01  
% 2.84/1.01  fof(f38,plain,(
% 2.84/1.01    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.84/1.01    introduced(choice_axiom,[])).
% 2.84/1.01  
% 2.84/1.01  fof(f40,plain,(
% 2.84/1.01    (~r2_relset_1(sK2,sK3,sK4,sK5) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.84/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f39,f38])).
% 2.84/1.01  
% 2.84/1.01  fof(f69,plain,(
% 2.84/1.01    v1_funct_2(sK5,sK2,sK3)),
% 2.84/1.01    inference(cnf_transformation,[],[f40])).
% 2.84/1.01  
% 2.84/1.01  fof(f70,plain,(
% 2.84/1.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.84/1.01    inference(cnf_transformation,[],[f40])).
% 2.84/1.01  
% 2.84/1.01  fof(f9,axiom,(
% 2.84/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.84/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/1.01  
% 2.84/1.01  fof(f20,plain,(
% 2.84/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/1.01    inference(ennf_transformation,[],[f9])).
% 2.84/1.01  
% 2.84/1.01  fof(f56,plain,(
% 2.84/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/1.01    inference(cnf_transformation,[],[f20])).
% 2.84/1.01  
% 2.84/1.01  fof(f66,plain,(
% 2.84/1.01    v1_funct_2(sK4,sK2,sK3)),
% 2.84/1.01    inference(cnf_transformation,[],[f40])).
% 2.84/1.01  
% 2.84/1.01  fof(f67,plain,(
% 2.84/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.84/1.01    inference(cnf_transformation,[],[f40])).
% 2.84/1.01  
% 2.84/1.01  fof(f7,axiom,(
% 2.84/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.84/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/1.01  
% 2.84/1.01  fof(f17,plain,(
% 2.84/1.01    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.84/1.01    inference(ennf_transformation,[],[f7])).
% 2.84/1.01  
% 2.84/1.01  fof(f18,plain,(
% 2.84/1.01    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.84/1.01    inference(flattening,[],[f17])).
% 2.84/1.01  
% 2.84/1.01  fof(f34,plain,(
% 2.84/1.01    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 2.84/1.01    introduced(choice_axiom,[])).
% 2.84/1.01  
% 2.84/1.01  fof(f35,plain,(
% 2.84/1.01    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.84/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f34])).
% 2.84/1.01  
% 2.84/1.01  fof(f53,plain,(
% 2.84/1.01    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.84/1.01    inference(cnf_transformation,[],[f35])).
% 2.84/1.01  
% 2.84/1.01  fof(f68,plain,(
% 2.84/1.01    v1_funct_1(sK5)),
% 2.84/1.01    inference(cnf_transformation,[],[f40])).
% 2.84/1.01  
% 2.84/1.01  fof(f8,axiom,(
% 2.84/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.84/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/1.01  
% 2.84/1.01  fof(f19,plain,(
% 2.84/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/1.01    inference(ennf_transformation,[],[f8])).
% 2.84/1.01  
% 2.84/1.01  fof(f55,plain,(
% 2.84/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/1.01    inference(cnf_transformation,[],[f19])).
% 2.84/1.01  
% 2.84/1.01  fof(f65,plain,(
% 2.84/1.01    v1_funct_1(sK4)),
% 2.84/1.01    inference(cnf_transformation,[],[f40])).
% 2.84/1.01  
% 2.84/1.01  fof(f10,axiom,(
% 2.84/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.84/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/1.01  
% 2.84/1.01  fof(f21,plain,(
% 2.84/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.84/1.01    inference(ennf_transformation,[],[f10])).
% 2.84/1.01  
% 2.84/1.01  fof(f22,plain,(
% 2.84/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/1.01    inference(flattening,[],[f21])).
% 2.84/1.01  
% 2.84/1.01  fof(f36,plain,(
% 2.84/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/1.01    inference(nnf_transformation,[],[f22])).
% 2.84/1.01  
% 2.84/1.01  fof(f58,plain,(
% 2.84/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/1.01    inference(cnf_transformation,[],[f36])).
% 2.84/1.01  
% 2.84/1.01  fof(f75,plain,(
% 2.84/1.01    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/1.01    inference(equality_resolution,[],[f58])).
% 2.84/1.01  
% 2.84/1.01  fof(f72,plain,(
% 2.84/1.01    ~r2_relset_1(sK2,sK3,sK4,sK5)),
% 2.84/1.01    inference(cnf_transformation,[],[f40])).
% 2.84/1.01  
% 2.84/1.01  fof(f5,axiom,(
% 2.84/1.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.84/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/1.01  
% 2.84/1.01  fof(f15,plain,(
% 2.84/1.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.84/1.01    inference(ennf_transformation,[],[f5])).
% 2.84/1.01  
% 2.84/1.01  fof(f33,plain,(
% 2.84/1.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.84/1.01    inference(nnf_transformation,[],[f15])).
% 2.84/1.01  
% 2.84/1.01  fof(f49,plain,(
% 2.84/1.01    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.84/1.01    inference(cnf_transformation,[],[f33])).
% 2.84/1.01  
% 2.84/1.01  fof(f1,axiom,(
% 2.84/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.84/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/1.01  
% 2.84/1.01  fof(f27,plain,(
% 2.84/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.84/1.01    inference(nnf_transformation,[],[f1])).
% 2.84/1.01  
% 2.84/1.01  fof(f28,plain,(
% 2.84/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.84/1.01    inference(rectify,[],[f27])).
% 2.84/1.01  
% 2.84/1.01  fof(f29,plain,(
% 2.84/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.84/1.01    introduced(choice_axiom,[])).
% 2.84/1.01  
% 2.84/1.01  fof(f30,plain,(
% 2.84/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.84/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 2.84/1.01  
% 2.84/1.01  fof(f41,plain,(
% 2.84/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.84/1.01    inference(cnf_transformation,[],[f30])).
% 2.84/1.01  
% 2.84/1.01  fof(f71,plain,(
% 2.84/1.01    ( ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK2)) )),
% 2.84/1.01    inference(cnf_transformation,[],[f40])).
% 2.84/1.01  
% 2.84/1.01  fof(f54,plain,(
% 2.84/1.01    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.84/1.01    inference(cnf_transformation,[],[f35])).
% 2.84/1.01  
% 2.84/1.01  fof(f4,axiom,(
% 2.84/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.84/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/1.01  
% 2.84/1.01  fof(f31,plain,(
% 2.84/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.84/1.01    inference(nnf_transformation,[],[f4])).
% 2.84/1.01  
% 2.84/1.01  fof(f32,plain,(
% 2.84/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.84/1.01    inference(flattening,[],[f31])).
% 2.84/1.01  
% 2.84/1.01  fof(f47,plain,(
% 2.84/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.84/1.01    inference(cnf_transformation,[],[f32])).
% 2.84/1.01  
% 2.84/1.01  fof(f73,plain,(
% 2.84/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.84/1.01    inference(equality_resolution,[],[f47])).
% 2.84/1.01  
% 2.84/1.01  fof(f6,axiom,(
% 2.84/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.84/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/1.01  
% 2.84/1.01  fof(f16,plain,(
% 2.84/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.84/1.01    inference(ennf_transformation,[],[f6])).
% 2.84/1.01  
% 2.84/1.01  fof(f52,plain,(
% 2.84/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.84/1.01    inference(cnf_transformation,[],[f16])).
% 2.84/1.01  
% 2.84/1.01  fof(f3,axiom,(
% 2.84/1.01    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.84/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/1.01  
% 2.84/1.01  fof(f14,plain,(
% 2.84/1.01    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.84/1.01    inference(ennf_transformation,[],[f3])).
% 2.84/1.01  
% 2.84/1.01  fof(f44,plain,(
% 2.84/1.01    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.84/1.01    inference(cnf_transformation,[],[f14])).
% 2.84/1.01  
% 2.84/1.01  fof(f42,plain,(
% 2.84/1.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.84/1.01    inference(cnf_transformation,[],[f30])).
% 2.84/1.01  
% 2.84/1.01  fof(f2,axiom,(
% 2.84/1.01    v1_xboole_0(k1_xboole_0)),
% 2.84/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/1.01  
% 2.84/1.01  fof(f43,plain,(
% 2.84/1.01    v1_xboole_0(k1_xboole_0)),
% 2.84/1.01    inference(cnf_transformation,[],[f2])).
% 2.84/1.01  
% 2.84/1.01  cnf(c_23,plain,
% 2.84/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.84/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.84/1.01      | k1_xboole_0 = X2 ),
% 2.84/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_27,negated_conjecture,
% 2.84/1.01      ( v1_funct_2(sK5,sK2,sK3) ),
% 2.84/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_555,plain,
% 2.84/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.84/1.01      | sK5 != X0
% 2.84/1.01      | sK3 != X2
% 2.84/1.01      | sK2 != X1
% 2.84/1.01      | k1_xboole_0 = X2 ),
% 2.84/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_556,plain,
% 2.84/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.84/1.01      | k1_relset_1(sK2,sK3,sK5) = sK2
% 2.84/1.01      | k1_xboole_0 = sK3 ),
% 2.84/1.01      inference(unflattening,[status(thm)],[c_555]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_26,negated_conjecture,
% 2.84/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.84/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_558,plain,
% 2.84/1.01      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 2.84/1.01      inference(global_propositional_subsumption,
% 2.84/1.01                [status(thm)],
% 2.84/1.01                [c_556,c_26]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2430,plain,
% 2.84/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_15,plain,
% 2.84/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.84/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2432,plain,
% 2.84/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.84/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_3260,plain,
% 2.84/1.01      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 2.84/1.01      inference(superposition,[status(thm)],[c_2430,c_2432]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_3332,plain,
% 2.84/1.01      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 2.84/1.01      inference(superposition,[status(thm)],[c_558,c_3260]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_30,negated_conjecture,
% 2.84/1.01      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.84/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_566,plain,
% 2.84/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.84/1.01      | sK4 != X0
% 2.84/1.01      | sK3 != X2
% 2.84/1.01      | sK2 != X1
% 2.84/1.01      | k1_xboole_0 = X2 ),
% 2.84/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_567,plain,
% 2.84/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.84/1.01      | k1_relset_1(sK2,sK3,sK4) = sK2
% 2.84/1.01      | k1_xboole_0 = sK3 ),
% 2.84/1.01      inference(unflattening,[status(thm)],[c_566]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_29,negated_conjecture,
% 2.84/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.84/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_569,plain,
% 2.84/1.01      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.84/1.01      inference(global_propositional_subsumption,
% 2.84/1.01                [status(thm)],
% 2.84/1.01                [c_567,c_29]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2428,plain,
% 2.84/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_3261,plain,
% 2.84/1.01      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.84/1.01      inference(superposition,[status(thm)],[c_2428,c_2432]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_3431,plain,
% 2.84/1.01      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.84/1.01      inference(superposition,[status(thm)],[c_569,c_3261]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_13,plain,
% 2.84/1.01      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 2.84/1.01      | ~ v1_relat_1(X1)
% 2.84/1.01      | ~ v1_relat_1(X0)
% 2.84/1.01      | ~ v1_funct_1(X1)
% 2.84/1.01      | ~ v1_funct_1(X0)
% 2.84/1.01      | X1 = X0
% 2.84/1.01      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.84/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2434,plain,
% 2.84/1.01      ( X0 = X1
% 2.84/1.01      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.84/1.01      | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
% 2.84/1.01      | v1_relat_1(X1) != iProver_top
% 2.84/1.01      | v1_relat_1(X0) != iProver_top
% 2.84/1.01      | v1_funct_1(X0) != iProver_top
% 2.84/1.01      | v1_funct_1(X1) != iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_3552,plain,
% 2.84/1.01      ( k1_relat_1(X0) != sK2
% 2.84/1.01      | sK5 = X0
% 2.84/1.01      | sK3 = k1_xboole_0
% 2.84/1.01      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.84/1.01      | v1_relat_1(X0) != iProver_top
% 2.84/1.01      | v1_relat_1(sK5) != iProver_top
% 2.84/1.01      | v1_funct_1(X0) != iProver_top
% 2.84/1.01      | v1_funct_1(sK5) != iProver_top ),
% 2.84/1.01      inference(superposition,[status(thm)],[c_3332,c_2434]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_28,negated_conjecture,
% 2.84/1.01      ( v1_funct_1(sK5) ),
% 2.84/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_35,plain,
% 2.84/1.01      ( v1_funct_1(sK5) = iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_37,plain,
% 2.84/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_14,plain,
% 2.84/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/1.01      | v1_relat_1(X0) ),
% 2.84/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2658,plain,
% 2.84/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.84/1.01      | v1_relat_1(sK5) ),
% 2.84/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2659,plain,
% 2.84/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.84/1.01      | v1_relat_1(sK5) = iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_2658]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_5018,plain,
% 2.84/1.01      ( v1_funct_1(X0) != iProver_top
% 2.84/1.01      | k1_relat_1(X0) != sK2
% 2.84/1.01      | sK5 = X0
% 2.84/1.01      | sK3 = k1_xboole_0
% 2.84/1.01      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.84/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.84/1.01      inference(global_propositional_subsumption,
% 2.84/1.01                [status(thm)],
% 2.84/1.01                [c_3552,c_35,c_37,c_2659]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_5019,plain,
% 2.84/1.01      ( k1_relat_1(X0) != sK2
% 2.84/1.01      | sK5 = X0
% 2.84/1.01      | sK3 = k1_xboole_0
% 2.84/1.01      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.84/1.01      | v1_relat_1(X0) != iProver_top
% 2.84/1.01      | v1_funct_1(X0) != iProver_top ),
% 2.84/1.01      inference(renaming,[status(thm)],[c_5018]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_5031,plain,
% 2.84/1.01      ( sK5 = sK4
% 2.84/1.01      | sK3 = k1_xboole_0
% 2.84/1.01      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
% 2.84/1.01      | v1_relat_1(sK4) != iProver_top
% 2.84/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.84/1.01      inference(superposition,[status(thm)],[c_3431,c_5019]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_31,negated_conjecture,
% 2.84/1.01      ( v1_funct_1(sK4) ),
% 2.84/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_32,plain,
% 2.84/1.01      ( v1_funct_1(sK4) = iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_34,plain,
% 2.84/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_16,plain,
% 2.84/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 2.84/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.84/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_24,negated_conjecture,
% 2.84/1.01      ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
% 2.84/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_332,plain,
% 2.84/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/1.01      | sK5 != X0
% 2.84/1.01      | sK4 != X0
% 2.84/1.01      | sK3 != X2
% 2.84/1.01      | sK2 != X1 ),
% 2.84/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_333,plain,
% 2.84/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.84/1.01      | sK4 != sK5 ),
% 2.84/1.01      inference(unflattening,[status(thm)],[c_332]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2661,plain,
% 2.84/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.84/1.01      | v1_relat_1(sK4) ),
% 2.84/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2662,plain,
% 2.84/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.84/1.01      | v1_relat_1(sK4) = iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_2661]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2031,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2688,plain,
% 2.84/1.01      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 2.84/1.01      inference(instantiation,[status(thm)],[c_2031]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_3230,plain,
% 2.84/1.01      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 2.84/1.01      inference(instantiation,[status(thm)],[c_2688]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2030,plain,( X0 = X0 ),theory(equality) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_4995,plain,
% 2.84/1.01      ( sK4 = sK4 ),
% 2.84/1.01      inference(instantiation,[status(thm)],[c_2030]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_5129,plain,
% 2.84/1.01      ( sK3 = k1_xboole_0
% 2.84/1.01      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
% 2.84/1.01      inference(global_propositional_subsumption,
% 2.84/1.01                [status(thm)],
% 2.84/1.01                [c_5031,c_32,c_34,c_26,c_333,c_2662,c_3230,c_4995]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_5135,plain,
% 2.84/1.01      ( sK3 = k1_xboole_0 | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
% 2.84/1.01      inference(superposition,[status(thm)],[c_3431,c_5129]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_9,plain,
% 2.84/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.84/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_1,plain,
% 2.84/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.84/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_182,plain,
% 2.84/1.01      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.84/1.01      inference(global_propositional_subsumption,[status(thm)],[c_9,c_1]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_183,plain,
% 2.84/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.84/1.01      inference(renaming,[status(thm)],[c_182]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2426,plain,
% 2.84/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 2.84/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_183]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_5157,plain,
% 2.84/1.01      ( sK3 = k1_xboole_0 | m1_subset_1(sK1(sK4,sK5),sK2) = iProver_top ),
% 2.84/1.01      inference(superposition,[status(thm)],[c_5135,c_2426]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_25,negated_conjecture,
% 2.84/1.01      ( ~ m1_subset_1(X0,sK2) | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
% 2.84/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2431,plain,
% 2.84/1.01      ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
% 2.84/1.01      | m1_subset_1(X0,sK2) != iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_6466,plain,
% 2.84/1.01      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 2.84/1.01      | sK3 = k1_xboole_0 ),
% 2.84/1.01      inference(superposition,[status(thm)],[c_5157,c_2431]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_12,plain,
% 2.84/1.01      ( ~ v1_relat_1(X0)
% 2.84/1.01      | ~ v1_relat_1(X1)
% 2.84/1.01      | ~ v1_funct_1(X0)
% 2.84/1.01      | ~ v1_funct_1(X1)
% 2.84/1.01      | X0 = X1
% 2.84/1.01      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 2.84/1.01      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.84/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2435,plain,
% 2.84/1.01      ( X0 = X1
% 2.84/1.01      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 2.84/1.01      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.84/1.01      | v1_relat_1(X0) != iProver_top
% 2.84/1.01      | v1_relat_1(X1) != iProver_top
% 2.84/1.01      | v1_funct_1(X1) != iProver_top
% 2.84/1.01      | v1_funct_1(X0) != iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_6476,plain,
% 2.84/1.01      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.84/1.01      | sK5 = sK4
% 2.84/1.01      | sK3 = k1_xboole_0
% 2.84/1.01      | v1_relat_1(sK5) != iProver_top
% 2.84/1.01      | v1_relat_1(sK4) != iProver_top
% 2.84/1.01      | v1_funct_1(sK5) != iProver_top
% 2.84/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.84/1.01      inference(superposition,[status(thm)],[c_6466,c_2435]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_6477,plain,
% 2.84/1.01      ( ~ v1_relat_1(sK5)
% 2.84/1.01      | ~ v1_relat_1(sK4)
% 2.84/1.01      | ~ v1_funct_1(sK5)
% 2.84/1.01      | ~ v1_funct_1(sK4)
% 2.84/1.01      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.84/1.01      | sK5 = sK4
% 2.84/1.01      | sK3 = k1_xboole_0 ),
% 2.84/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_6476]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_6563,plain,
% 2.84/1.01      ( k1_relat_1(sK4) != k1_relat_1(sK5) | sK3 = k1_xboole_0 ),
% 2.84/1.01      inference(global_propositional_subsumption,
% 2.84/1.01                [status(thm)],
% 2.84/1.01                [c_6476,c_31,c_29,c_28,c_26,c_333,c_2658,c_2661,c_3230,
% 2.84/1.01                 c_4995,c_6477]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_6567,plain,
% 2.84/1.01      ( k1_relat_1(sK4) != sK2 | sK3 = k1_xboole_0 ),
% 2.84/1.01      inference(superposition,[status(thm)],[c_3332,c_6563]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_6568,plain,
% 2.84/1.01      ( sK3 = k1_xboole_0 ),
% 2.84/1.01      inference(global_propositional_subsumption,
% 2.84/1.01                [status(thm)],
% 2.84/1.01                [c_6567,c_3431]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_6589,plain,
% 2.84/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 2.84/1.01      inference(demodulation,[status(thm)],[c_6568,c_2430]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_4,plain,
% 2.84/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.84/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_6595,plain,
% 2.84/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.84/1.01      inference(demodulation,[status(thm)],[c_6589,c_4]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_6590,plain,
% 2.84/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 2.84/1.01      inference(demodulation,[status(thm)],[c_6568,c_2428]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_6592,plain,
% 2.84/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.84/1.01      inference(demodulation,[status(thm)],[c_6590,c_4]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_11,plain,
% 2.84/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.84/1.01      | ~ r2_hidden(X2,X0)
% 2.84/1.01      | ~ v1_xboole_0(X1) ),
% 2.84/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_4962,plain,
% 2.84/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 2.84/1.01      | ~ r2_hidden(sK0(sK4),sK4)
% 2.84/1.01      | ~ v1_xboole_0(X0) ),
% 2.84/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_4963,plain,
% 2.84/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 2.84/1.01      | r2_hidden(sK0(sK4),sK4) != iProver_top
% 2.84/1.01      | v1_xboole_0(X0) != iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_4962]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_4965,plain,
% 2.84/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.84/1.01      | r2_hidden(sK0(sK4),sK4) != iProver_top
% 2.84/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.84/1.01      inference(instantiation,[status(thm)],[c_4963]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_3,plain,
% 2.84/1.01      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.84/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2780,plain,
% 2.84/1.01      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK4) | X0 = sK4 ),
% 2.84/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_3229,plain,
% 2.84/1.01      ( ~ v1_xboole_0(sK5) | ~ v1_xboole_0(sK4) | sK5 = sK4 ),
% 2.84/1.01      inference(instantiation,[status(thm)],[c_2780]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_3231,plain,
% 2.84/1.01      ( sK5 = sK4
% 2.84/1.01      | v1_xboole_0(sK5) != iProver_top
% 2.84/1.01      | v1_xboole_0(sK4) != iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_3229]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_3146,plain,
% 2.84/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 2.84/1.01      | ~ r2_hidden(sK0(sK5),sK5)
% 2.84/1.01      | ~ v1_xboole_0(X0) ),
% 2.84/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_3147,plain,
% 2.84/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 2.84/1.01      | r2_hidden(sK0(sK5),sK5) != iProver_top
% 2.84/1.01      | v1_xboole_0(X0) != iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_3146]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_3149,plain,
% 2.84/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.84/1.01      | r2_hidden(sK0(sK5),sK5) != iProver_top
% 2.84/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.84/1.01      inference(instantiation,[status(thm)],[c_3147]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_0,plain,
% 2.84/1.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.84/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2981,plain,
% 2.84/1.01      ( r2_hidden(sK0(sK4),sK4) | v1_xboole_0(sK4) ),
% 2.84/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2987,plain,
% 2.84/1.01      ( r2_hidden(sK0(sK4),sK4) = iProver_top
% 2.84/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_2981]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2811,plain,
% 2.84/1.01      ( r2_hidden(sK0(sK5),sK5) | v1_xboole_0(sK5) ),
% 2.84/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2817,plain,
% 2.84/1.01      ( r2_hidden(sK0(sK5),sK5) = iProver_top
% 2.84/1.01      | v1_xboole_0(sK5) = iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_2811]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_2,plain,
% 2.84/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.84/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(c_96,plain,
% 2.84/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.84/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.84/1.01  
% 2.84/1.01  cnf(contradiction,plain,
% 2.84/1.01      ( $false ),
% 2.84/1.01      inference(minisat,
% 2.84/1.01                [status(thm)],
% 2.84/1.01                [c_6595,c_6592,c_4995,c_4965,c_3230,c_3231,c_3149,c_2987,
% 2.84/1.01                 c_2817,c_333,c_96,c_26]) ).
% 2.84/1.01  
% 2.84/1.01  
% 2.84/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.84/1.01  
% 2.84/1.01  ------                               Statistics
% 2.84/1.01  
% 2.84/1.01  ------ General
% 2.84/1.01  
% 2.84/1.01  abstr_ref_over_cycles:                  0
% 2.84/1.01  abstr_ref_under_cycles:                 0
% 2.84/1.01  gc_basic_clause_elim:                   0
% 2.84/1.01  forced_gc_time:                         0
% 2.84/1.01  parsing_time:                           0.011
% 2.84/1.01  unif_index_cands_time:                  0.
% 2.84/1.01  unif_index_add_time:                    0.
% 2.84/1.01  orderings_time:                         0.
% 2.84/1.01  out_proof_time:                         0.008
% 2.84/1.01  total_time:                             0.212
% 2.84/1.01  num_of_symbols:                         50
% 2.84/1.01  num_of_terms:                           3590
% 2.84/1.01  
% 2.84/1.01  ------ Preprocessing
% 2.84/1.01  
% 2.84/1.01  num_of_splits:                          0
% 2.84/1.01  num_of_split_atoms:                     0
% 2.84/1.01  num_of_reused_defs:                     0
% 2.84/1.01  num_eq_ax_congr_red:                    17
% 2.84/1.01  num_of_sem_filtered_clauses:            1
% 2.84/1.01  num_of_subtypes:                        0
% 2.84/1.01  monotx_restored_types:                  0
% 2.84/1.01  sat_num_of_epr_types:                   0
% 2.84/1.01  sat_num_of_non_cyclic_types:            0
% 2.84/1.01  sat_guarded_non_collapsed_types:        0
% 2.84/1.01  num_pure_diseq_elim:                    0
% 2.84/1.01  simp_replaced_by:                       0
% 2.84/1.01  res_preprocessed:                       137
% 2.84/1.01  prep_upred:                             0
% 2.84/1.01  prep_unflattend:                        165
% 2.84/1.01  smt_new_axioms:                         0
% 2.84/1.01  pred_elim_cands:                        5
% 2.84/1.01  pred_elim:                              2
% 2.84/1.01  pred_elim_cl:                           4
% 2.84/1.01  pred_elim_cycles:                       6
% 2.84/1.01  merged_defs:                            0
% 2.84/1.01  merged_defs_ncl:                        0
% 2.84/1.01  bin_hyper_res:                          0
% 2.84/1.01  prep_cycles:                            4
% 2.84/1.01  pred_elim_time:                         0.035
% 2.84/1.01  splitting_time:                         0.
% 2.84/1.01  sem_filter_time:                        0.
% 2.84/1.01  monotx_time:                            0.
% 2.84/1.01  subtype_inf_time:                       0.
% 2.84/1.01  
% 2.84/1.01  ------ Problem properties
% 2.84/1.01  
% 2.84/1.01  clauses:                                28
% 2.84/1.01  conjectures:                            5
% 2.84/1.01  epr:                                    10
% 2.84/1.01  horn:                                   20
% 2.84/1.01  ground:                                 12
% 2.84/1.01  unary:                                  8
% 2.84/1.01  binary:                                 8
% 2.84/1.01  lits:                                   70
% 2.84/1.01  lits_eq:                                28
% 2.84/1.01  fd_pure:                                0
% 2.84/1.01  fd_pseudo:                              0
% 2.84/1.01  fd_cond:                                1
% 2.84/1.01  fd_pseudo_cond:                         3
% 2.84/1.01  ac_symbols:                             0
% 2.84/1.01  
% 2.84/1.01  ------ Propositional Solver
% 2.84/1.01  
% 2.84/1.01  prop_solver_calls:                      29
% 2.84/1.01  prop_fast_solver_calls:                 1278
% 2.84/1.01  smt_solver_calls:                       0
% 2.84/1.01  smt_fast_solver_calls:                  0
% 2.84/1.01  prop_num_of_clauses:                    1852
% 2.84/1.01  prop_preprocess_simplified:             5686
% 2.84/1.01  prop_fo_subsumed:                       31
% 2.84/1.01  prop_solver_time:                       0.
% 2.84/1.01  smt_solver_time:                        0.
% 2.84/1.01  smt_fast_solver_time:                   0.
% 2.84/1.01  prop_fast_solver_time:                  0.
% 2.84/1.01  prop_unsat_core_time:                   0.
% 2.84/1.01  
% 2.84/1.01  ------ QBF
% 2.84/1.01  
% 2.84/1.01  qbf_q_res:                              0
% 2.84/1.01  qbf_num_tautologies:                    0
% 2.84/1.01  qbf_prep_cycles:                        0
% 2.84/1.01  
% 2.84/1.01  ------ BMC1
% 2.84/1.01  
% 2.84/1.01  bmc1_current_bound:                     -1
% 2.84/1.01  bmc1_last_solved_bound:                 -1
% 2.84/1.01  bmc1_unsat_core_size:                   -1
% 2.84/1.01  bmc1_unsat_core_parents_size:           -1
% 2.84/1.01  bmc1_merge_next_fun:                    0
% 2.84/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.84/1.01  
% 2.84/1.01  ------ Instantiation
% 2.84/1.01  
% 2.84/1.01  inst_num_of_clauses:                    555
% 2.84/1.01  inst_num_in_passive:                    200
% 2.84/1.01  inst_num_in_active:                     325
% 2.84/1.01  inst_num_in_unprocessed:                30
% 2.84/1.01  inst_num_of_loops:                      400
% 2.84/1.01  inst_num_of_learning_restarts:          0
% 2.84/1.01  inst_num_moves_active_passive:          71
% 2.84/1.01  inst_lit_activity:                      0
% 2.84/1.01  inst_lit_activity_moves:                0
% 2.84/1.01  inst_num_tautologies:                   0
% 2.84/1.01  inst_num_prop_implied:                  0
% 2.84/1.01  inst_num_existing_simplified:           0
% 2.84/1.01  inst_num_eq_res_simplified:             0
% 2.84/1.01  inst_num_child_elim:                    0
% 2.84/1.01  inst_num_of_dismatching_blockings:      134
% 2.84/1.01  inst_num_of_non_proper_insts:           691
% 2.84/1.01  inst_num_of_duplicates:                 0
% 2.84/1.01  inst_inst_num_from_inst_to_res:         0
% 2.84/1.01  inst_dismatching_checking_time:         0.
% 2.84/1.01  
% 2.84/1.01  ------ Resolution
% 2.84/1.01  
% 2.84/1.01  res_num_of_clauses:                     0
% 2.84/1.01  res_num_in_passive:                     0
% 2.84/1.01  res_num_in_active:                      0
% 2.84/1.01  res_num_of_loops:                       141
% 2.84/1.01  res_forward_subset_subsumed:            32
% 2.84/1.01  res_backward_subset_subsumed:           0
% 2.84/1.01  res_forward_subsumed:                   2
% 2.84/1.01  res_backward_subsumed:                  0
% 2.84/1.01  res_forward_subsumption_resolution:     0
% 2.84/1.01  res_backward_subsumption_resolution:    0
% 2.84/1.01  res_clause_to_clause_subsumption:       276
% 2.84/1.01  res_orphan_elimination:                 0
% 2.84/1.01  res_tautology_del:                      70
% 2.84/1.01  res_num_eq_res_simplified:              0
% 2.84/1.01  res_num_sel_changes:                    0
% 2.84/1.01  res_moves_from_active_to_pass:          0
% 2.84/1.01  
% 2.84/1.01  ------ Superposition
% 2.84/1.01  
% 2.84/1.01  sup_time_total:                         0.
% 2.84/1.01  sup_time_generating:                    0.
% 2.84/1.01  sup_time_sim_full:                      0.
% 2.84/1.01  sup_time_sim_immed:                     0.
% 2.84/1.01  
% 2.84/1.01  sup_num_of_clauses:                     73
% 2.84/1.01  sup_num_in_active:                      51
% 2.84/1.01  sup_num_in_passive:                     22
% 2.84/1.01  sup_num_of_loops:                       79
% 2.84/1.01  sup_fw_superposition:                   53
% 2.84/1.01  sup_bw_superposition:                   51
% 2.84/1.01  sup_immediate_simplified:               16
% 2.84/1.01  sup_given_eliminated:                   0
% 2.84/1.01  comparisons_done:                       0
% 2.84/1.01  comparisons_avoided:                    27
% 2.84/1.01  
% 2.84/1.01  ------ Simplifications
% 2.84/1.01  
% 2.84/1.01  
% 2.84/1.01  sim_fw_subset_subsumed:                 3
% 2.84/1.01  sim_bw_subset_subsumed:                 13
% 2.84/1.01  sim_fw_subsumed:                        1
% 2.84/1.01  sim_bw_subsumed:                        0
% 2.84/1.01  sim_fw_subsumption_res:                 5
% 2.84/1.01  sim_bw_subsumption_res:                 0
% 2.84/1.01  sim_tautology_del:                      4
% 2.84/1.01  sim_eq_tautology_del:                   15
% 2.84/1.01  sim_eq_res_simp:                        2
% 2.84/1.01  sim_fw_demodulated:                     11
% 2.84/1.01  sim_bw_demodulated:                     20
% 2.84/1.01  sim_light_normalised:                   2
% 2.84/1.01  sim_joinable_taut:                      0
% 2.84/1.01  sim_joinable_simp:                      0
% 2.84/1.01  sim_ac_normalised:                      0
% 2.84/1.01  sim_smt_subsumption:                    0
% 2.84/1.01  
%------------------------------------------------------------------------------
