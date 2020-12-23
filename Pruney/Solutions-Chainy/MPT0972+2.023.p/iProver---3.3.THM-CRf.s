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
% DateTime   : Thu Dec  3 12:01:12 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  175 (1061 expanded)
%              Number of clauses        :  110 ( 349 expanded)
%              Number of leaves         :   18 ( 251 expanded)
%              Depth                    :   28
%              Number of atoms          :  614 (6581 expanded)
%              Number of equality atoms :  338 (1704 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f25,f43,f42])).

fof(f74,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f38])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f77,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f70,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_423,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_27])).

cnf(c_424,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_853,plain,
    ( k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != sK6
    | sK4 != X1
    | sK3 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_424])).

cnf(c_854,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_853])).

cnf(c_1627,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_854])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_459,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_460,plain,
    ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_1791,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_460])).

cnf(c_2716,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1627,c_1791])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_480,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_481,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | k1_relset_1(X0,X1,sK5) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_938,plain,
    ( k1_relset_1(X0,X1,sK5) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK5 != sK5
    | sK4 != X1
    | sK3 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_481])).

cnf(c_939,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_938])).

cnf(c_1622,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_939])).

cnf(c_516,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_30])).

cnf(c_517,plain,
    ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_1794,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(equality_resolution,[status(thm)],[c_517])).

cnf(c_2713,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1622,c_1794])).

cnf(c_14,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1522,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2838,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2716,c_1522])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_36,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1124,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1784,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_468,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_469,plain,
    ( v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_1965,plain,
    ( v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_469])).

cnf(c_1966,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1965])).

cnf(c_3816,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2838,c_36,c_1784,c_1966])).

cnf(c_3817,plain,
    ( k1_relat_1(X0) != sK3
    | sK6 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3816])).

cnf(c_3829,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2713,c_3817])).

cnf(c_17,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_25,negated_conjecture,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK6 != X0
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_329,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | sK5 != sK6 ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1916,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2180,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1916])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2181,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1125,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1833,plain,
    ( sK6 != X0
    | sK5 != X0
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_1125])).

cnf(c_3651,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1833])).

cnf(c_2841,plain,
    ( k1_relat_1(X0) != sK3
    | sK5 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2713,c_1522])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_33,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_525,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_30])).

cnf(c_526,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_1964,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_1968,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1964])).

cnf(c_6131,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK3
    | sK5 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2841,c_33,c_1784,c_1968])).

cnf(c_6132,plain,
    ( k1_relat_1(X0) != sK3
    | sK5 = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6131])).

cnf(c_6143,plain,
    ( sK6 = sK5
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2716,c_6132])).

cnf(c_6382,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3829,c_33,c_27,c_329,c_1784,c_1968,c_2180,c_2181,c_3651])).

cnf(c_6388,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2713,c_6382])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1521,plain,
    ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6501,plain,
    ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6388,c_1521])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1523,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6522,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6501,c_1523])).

cnf(c_6523,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK5)
    | k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK6 = sK5
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6522])).

cnf(c_6604,plain,
    ( k1_relat_1(sK5) != k1_relat_1(sK6)
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6522,c_32,c_29,c_27,c_329,c_1784,c_1965,c_1964,c_2180,c_2181,c_3651,c_6523])).

cnf(c_6608,plain,
    ( k1_relat_1(sK5) != sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2716,c_6604])).

cnf(c_6609,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6608,c_2713])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_408,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_30])).

cnf(c_409,plain,
    ( ~ r2_hidden(X0,sK5)
    | ~ v1_xboole_0(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_1118,plain,
    ( ~ v1_xboole_0(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_409])).

cnf(c_1515,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0)
    | v1_xboole_0(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1118])).

cnf(c_6623,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)) != k1_zfmisc_1(X0)
    | v1_xboole_0(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_6609,c_1515])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_6693,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_6623,c_9])).

cnf(c_6756,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_6693])).

cnf(c_393,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_394,plain,
    ( ~ r2_hidden(X0,sK6)
    | ~ v1_xboole_0(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_1122,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_394])).

cnf(c_1516,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1122])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1528,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1119,plain,
    ( ~ r2_hidden(X0,sK5)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_409])).

cnf(c_1514,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1119])).

cnf(c_3008,plain,
    ( r1_tarski(sK5,X0) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1528,c_1514])).

cnf(c_1121,plain,
    ( ~ r2_hidden(X0,sK6)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_394])).

cnf(c_1517,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1121])).

cnf(c_3007,plain,
    ( r1_tarski(sK6,X0) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1528,c_1517])).

cnf(c_1525,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3351,plain,
    ( sK6 = X0
    | r1_tarski(X0,sK6) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3007,c_1525])).

cnf(c_3620,plain,
    ( sK6 = sK5
    | sP2_iProver_split != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3008,c_3351])).

cnf(c_3638,plain,
    ( sK6 = sK5
    | sP1_iProver_split != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_3620])).

cnf(c_1120,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_409])).

cnf(c_1148,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1120])).

cnf(c_3641,plain,
    ( sK6 = sK5
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3638,c_1148])).

cnf(c_1129,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1138,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_91,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_83,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_82,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6756,c_3651,c_3641,c_2181,c_2180,c_1138,c_329,c_91,c_83,c_82,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n007.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 18:08:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.67/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/0.99  
% 2.67/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/0.99  
% 2.67/0.99  ------  iProver source info
% 2.67/0.99  
% 2.67/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.67/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/0.99  git: non_committed_changes: false
% 2.67/0.99  git: last_make_outside_of_git: false
% 2.67/0.99  
% 2.67/0.99  ------ 
% 2.67/0.99  
% 2.67/0.99  ------ Input Options
% 2.67/0.99  
% 2.67/0.99  --out_options                           all
% 2.67/0.99  --tptp_safe_out                         true
% 2.67/0.99  --problem_path                          ""
% 2.67/0.99  --include_path                          ""
% 2.67/0.99  --clausifier                            res/vclausify_rel
% 2.67/0.99  --clausifier_options                    --mode clausify
% 2.67/0.99  --stdin                                 false
% 2.67/0.99  --stats_out                             all
% 2.67/0.99  
% 2.67/0.99  ------ General Options
% 2.67/0.99  
% 2.67/0.99  --fof                                   false
% 2.67/0.99  --time_out_real                         305.
% 2.67/0.99  --time_out_virtual                      -1.
% 2.67/0.99  --symbol_type_check                     false
% 2.67/0.99  --clausify_out                          false
% 2.67/0.99  --sig_cnt_out                           false
% 2.67/0.99  --trig_cnt_out                          false
% 2.67/0.99  --trig_cnt_out_tolerance                1.
% 2.67/0.99  --trig_cnt_out_sk_spl                   false
% 2.67/0.99  --abstr_cl_out                          false
% 2.67/0.99  
% 2.67/0.99  ------ Global Options
% 2.67/0.99  
% 2.67/0.99  --schedule                              default
% 2.67/0.99  --add_important_lit                     false
% 2.67/0.99  --prop_solver_per_cl                    1000
% 2.67/0.99  --min_unsat_core                        false
% 2.67/0.99  --soft_assumptions                      false
% 2.67/0.99  --soft_lemma_size                       3
% 2.67/0.99  --prop_impl_unit_size                   0
% 2.67/0.99  --prop_impl_unit                        []
% 2.67/0.99  --share_sel_clauses                     true
% 2.67/0.99  --reset_solvers                         false
% 2.67/0.99  --bc_imp_inh                            [conj_cone]
% 2.67/0.99  --conj_cone_tolerance                   3.
% 2.67/0.99  --extra_neg_conj                        none
% 2.67/0.99  --large_theory_mode                     true
% 2.67/0.99  --prolific_symb_bound                   200
% 2.67/0.99  --lt_threshold                          2000
% 2.67/0.99  --clause_weak_htbl                      true
% 2.67/0.99  --gc_record_bc_elim                     false
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing Options
% 2.67/0.99  
% 2.67/0.99  --preprocessing_flag                    true
% 2.67/0.99  --time_out_prep_mult                    0.1
% 2.67/0.99  --splitting_mode                        input
% 2.67/0.99  --splitting_grd                         true
% 2.67/0.99  --splitting_cvd                         false
% 2.67/0.99  --splitting_cvd_svl                     false
% 2.67/0.99  --splitting_nvd                         32
% 2.67/0.99  --sub_typing                            true
% 2.67/0.99  --prep_gs_sim                           true
% 2.67/0.99  --prep_unflatten                        true
% 2.67/0.99  --prep_res_sim                          true
% 2.67/0.99  --prep_upred                            true
% 2.67/0.99  --prep_sem_filter                       exhaustive
% 2.67/0.99  --prep_sem_filter_out                   false
% 2.67/0.99  --pred_elim                             true
% 2.67/0.99  --res_sim_input                         true
% 2.67/0.99  --eq_ax_congr_red                       true
% 2.67/0.99  --pure_diseq_elim                       true
% 2.67/0.99  --brand_transform                       false
% 2.67/0.99  --non_eq_to_eq                          false
% 2.67/0.99  --prep_def_merge                        true
% 2.67/0.99  --prep_def_merge_prop_impl              false
% 2.67/0.99  --prep_def_merge_mbd                    true
% 2.67/0.99  --prep_def_merge_tr_red                 false
% 2.67/0.99  --prep_def_merge_tr_cl                  false
% 2.67/0.99  --smt_preprocessing                     true
% 2.67/0.99  --smt_ac_axioms                         fast
% 2.67/0.99  --preprocessed_out                      false
% 2.67/0.99  --preprocessed_stats                    false
% 2.67/0.99  
% 2.67/0.99  ------ Abstraction refinement Options
% 2.67/0.99  
% 2.67/0.99  --abstr_ref                             []
% 2.67/0.99  --abstr_ref_prep                        false
% 2.67/0.99  --abstr_ref_until_sat                   false
% 2.67/0.99  --abstr_ref_sig_restrict                funpre
% 2.67/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/0.99  --abstr_ref_under                       []
% 2.67/0.99  
% 2.67/0.99  ------ SAT Options
% 2.67/0.99  
% 2.67/0.99  --sat_mode                              false
% 2.67/0.99  --sat_fm_restart_options                ""
% 2.67/0.99  --sat_gr_def                            false
% 2.67/0.99  --sat_epr_types                         true
% 2.67/0.99  --sat_non_cyclic_types                  false
% 2.67/0.99  --sat_finite_models                     false
% 2.67/0.99  --sat_fm_lemmas                         false
% 2.67/0.99  --sat_fm_prep                           false
% 2.67/0.99  --sat_fm_uc_incr                        true
% 2.67/0.99  --sat_out_model                         small
% 2.67/0.99  --sat_out_clauses                       false
% 2.67/0.99  
% 2.67/0.99  ------ QBF Options
% 2.67/0.99  
% 2.67/0.99  --qbf_mode                              false
% 2.67/0.99  --qbf_elim_univ                         false
% 2.67/0.99  --qbf_dom_inst                          none
% 2.67/0.99  --qbf_dom_pre_inst                      false
% 2.67/0.99  --qbf_sk_in                             false
% 2.67/0.99  --qbf_pred_elim                         true
% 2.67/0.99  --qbf_split                             512
% 2.67/0.99  
% 2.67/0.99  ------ BMC1 Options
% 2.67/0.99  
% 2.67/0.99  --bmc1_incremental                      false
% 2.67/0.99  --bmc1_axioms                           reachable_all
% 2.67/0.99  --bmc1_min_bound                        0
% 2.67/0.99  --bmc1_max_bound                        -1
% 2.67/0.99  --bmc1_max_bound_default                -1
% 2.67/0.99  --bmc1_symbol_reachability              true
% 2.67/0.99  --bmc1_property_lemmas                  false
% 2.67/0.99  --bmc1_k_induction                      false
% 2.67/0.99  --bmc1_non_equiv_states                 false
% 2.67/0.99  --bmc1_deadlock                         false
% 2.67/0.99  --bmc1_ucm                              false
% 2.67/0.99  --bmc1_add_unsat_core                   none
% 2.67/0.99  --bmc1_unsat_core_children              false
% 2.67/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/0.99  --bmc1_out_stat                         full
% 2.67/0.99  --bmc1_ground_init                      false
% 2.67/0.99  --bmc1_pre_inst_next_state              false
% 2.67/0.99  --bmc1_pre_inst_state                   false
% 2.67/0.99  --bmc1_pre_inst_reach_state             false
% 2.67/0.99  --bmc1_out_unsat_core                   false
% 2.67/0.99  --bmc1_aig_witness_out                  false
% 2.67/0.99  --bmc1_verbose                          false
% 2.67/0.99  --bmc1_dump_clauses_tptp                false
% 2.67/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.67/0.99  --bmc1_dump_file                        -
% 2.67/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.67/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.67/0.99  --bmc1_ucm_extend_mode                  1
% 2.67/0.99  --bmc1_ucm_init_mode                    2
% 2.67/0.99  --bmc1_ucm_cone_mode                    none
% 2.67/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.67/0.99  --bmc1_ucm_relax_model                  4
% 2.67/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.67/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/0.99  --bmc1_ucm_layered_model                none
% 2.67/0.99  --bmc1_ucm_max_lemma_size               10
% 2.67/0.99  
% 2.67/0.99  ------ AIG Options
% 2.67/0.99  
% 2.67/0.99  --aig_mode                              false
% 2.67/0.99  
% 2.67/0.99  ------ Instantiation Options
% 2.67/0.99  
% 2.67/0.99  --instantiation_flag                    true
% 2.67/0.99  --inst_sos_flag                         false
% 2.67/0.99  --inst_sos_phase                        true
% 2.67/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/0.99  --inst_lit_sel_side                     num_symb
% 2.67/0.99  --inst_solver_per_active                1400
% 2.67/0.99  --inst_solver_calls_frac                1.
% 2.67/0.99  --inst_passive_queue_type               priority_queues
% 2.67/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/0.99  --inst_passive_queues_freq              [25;2]
% 2.67/0.99  --inst_dismatching                      true
% 2.67/0.99  --inst_eager_unprocessed_to_passive     true
% 2.67/0.99  --inst_prop_sim_given                   true
% 2.67/0.99  --inst_prop_sim_new                     false
% 2.67/0.99  --inst_subs_new                         false
% 2.67/1.00  --inst_eq_res_simp                      false
% 2.67/1.00  --inst_subs_given                       false
% 2.67/1.00  --inst_orphan_elimination               true
% 2.67/1.00  --inst_learning_loop_flag               true
% 2.67/1.00  --inst_learning_start                   3000
% 2.67/1.00  --inst_learning_factor                  2
% 2.67/1.00  --inst_start_prop_sim_after_learn       3
% 2.67/1.00  --inst_sel_renew                        solver
% 2.67/1.00  --inst_lit_activity_flag                true
% 2.67/1.00  --inst_restr_to_given                   false
% 2.67/1.00  --inst_activity_threshold               500
% 2.67/1.00  --inst_out_proof                        true
% 2.67/1.00  
% 2.67/1.00  ------ Resolution Options
% 2.67/1.00  
% 2.67/1.00  --resolution_flag                       true
% 2.67/1.00  --res_lit_sel                           adaptive
% 2.67/1.00  --res_lit_sel_side                      none
% 2.67/1.00  --res_ordering                          kbo
% 2.67/1.00  --res_to_prop_solver                    active
% 2.67/1.00  --res_prop_simpl_new                    false
% 2.67/1.00  --res_prop_simpl_given                  true
% 2.67/1.00  --res_passive_queue_type                priority_queues
% 2.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.00  --res_passive_queues_freq               [15;5]
% 2.67/1.00  --res_forward_subs                      full
% 2.67/1.00  --res_backward_subs                     full
% 2.67/1.00  --res_forward_subs_resolution           true
% 2.67/1.00  --res_backward_subs_resolution          true
% 2.67/1.00  --res_orphan_elimination                true
% 2.67/1.00  --res_time_limit                        2.
% 2.67/1.00  --res_out_proof                         true
% 2.67/1.00  
% 2.67/1.00  ------ Superposition Options
% 2.67/1.00  
% 2.67/1.00  --superposition_flag                    true
% 2.67/1.00  --sup_passive_queue_type                priority_queues
% 2.67/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.00  --demod_completeness_check              fast
% 2.67/1.00  --demod_use_ground                      true
% 2.67/1.00  --sup_to_prop_solver                    passive
% 2.67/1.00  --sup_prop_simpl_new                    true
% 2.67/1.00  --sup_prop_simpl_given                  true
% 2.67/1.00  --sup_fun_splitting                     false
% 2.67/1.00  --sup_smt_interval                      50000
% 2.67/1.00  
% 2.67/1.00  ------ Superposition Simplification Setup
% 2.67/1.00  
% 2.67/1.00  --sup_indices_passive                   []
% 2.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_full_bw                           [BwDemod]
% 2.67/1.00  --sup_immed_triv                        [TrivRules]
% 2.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_immed_bw_main                     []
% 2.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.00  
% 2.67/1.00  ------ Combination Options
% 2.67/1.00  
% 2.67/1.00  --comb_res_mult                         3
% 2.67/1.00  --comb_sup_mult                         2
% 2.67/1.00  --comb_inst_mult                        10
% 2.67/1.00  
% 2.67/1.00  ------ Debug Options
% 2.67/1.00  
% 2.67/1.00  --dbg_backtrace                         false
% 2.67/1.00  --dbg_dump_prop_clauses                 false
% 2.67/1.00  --dbg_dump_prop_clauses_file            -
% 2.67/1.00  --dbg_out_stat                          false
% 2.67/1.00  ------ Parsing...
% 2.67/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.67/1.00  ------ Proving...
% 2.67/1.00  ------ Problem Properties 
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  clauses                                 37
% 2.67/1.00  conjectures                             3
% 2.67/1.00  EPR                                     12
% 2.67/1.00  Horn                                    25
% 2.67/1.00  unary                                   7
% 2.67/1.00  binary                                  13
% 2.67/1.00  lits                                    100
% 2.67/1.00  lits eq                                 59
% 2.67/1.00  fd_pure                                 0
% 2.67/1.00  fd_pseudo                               0
% 2.67/1.00  fd_cond                                 1
% 2.67/1.00  fd_pseudo_cond                          3
% 2.67/1.00  AC symbols                              0
% 2.67/1.00  
% 2.67/1.00  ------ Schedule dynamic 5 is on 
% 2.67/1.00  
% 2.67/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  ------ 
% 2.67/1.00  Current options:
% 2.67/1.00  ------ 
% 2.67/1.00  
% 2.67/1.00  ------ Input Options
% 2.67/1.00  
% 2.67/1.00  --out_options                           all
% 2.67/1.00  --tptp_safe_out                         true
% 2.67/1.00  --problem_path                          ""
% 2.67/1.00  --include_path                          ""
% 2.67/1.00  --clausifier                            res/vclausify_rel
% 2.67/1.00  --clausifier_options                    --mode clausify
% 2.67/1.00  --stdin                                 false
% 2.67/1.00  --stats_out                             all
% 2.67/1.00  
% 2.67/1.00  ------ General Options
% 2.67/1.00  
% 2.67/1.00  --fof                                   false
% 2.67/1.00  --time_out_real                         305.
% 2.67/1.00  --time_out_virtual                      -1.
% 2.67/1.00  --symbol_type_check                     false
% 2.67/1.00  --clausify_out                          false
% 2.67/1.00  --sig_cnt_out                           false
% 2.67/1.00  --trig_cnt_out                          false
% 2.67/1.00  --trig_cnt_out_tolerance                1.
% 2.67/1.00  --trig_cnt_out_sk_spl                   false
% 2.67/1.00  --abstr_cl_out                          false
% 2.67/1.00  
% 2.67/1.00  ------ Global Options
% 2.67/1.00  
% 2.67/1.00  --schedule                              default
% 2.67/1.00  --add_important_lit                     false
% 2.67/1.00  --prop_solver_per_cl                    1000
% 2.67/1.00  --min_unsat_core                        false
% 2.67/1.00  --soft_assumptions                      false
% 2.67/1.00  --soft_lemma_size                       3
% 2.67/1.00  --prop_impl_unit_size                   0
% 2.67/1.00  --prop_impl_unit                        []
% 2.67/1.00  --share_sel_clauses                     true
% 2.67/1.00  --reset_solvers                         false
% 2.67/1.00  --bc_imp_inh                            [conj_cone]
% 2.67/1.00  --conj_cone_tolerance                   3.
% 2.67/1.00  --extra_neg_conj                        none
% 2.67/1.00  --large_theory_mode                     true
% 2.67/1.00  --prolific_symb_bound                   200
% 2.67/1.00  --lt_threshold                          2000
% 2.67/1.00  --clause_weak_htbl                      true
% 2.67/1.00  --gc_record_bc_elim                     false
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing Options
% 2.67/1.00  
% 2.67/1.00  --preprocessing_flag                    true
% 2.67/1.00  --time_out_prep_mult                    0.1
% 2.67/1.00  --splitting_mode                        input
% 2.67/1.00  --splitting_grd                         true
% 2.67/1.00  --splitting_cvd                         false
% 2.67/1.00  --splitting_cvd_svl                     false
% 2.67/1.00  --splitting_nvd                         32
% 2.67/1.00  --sub_typing                            true
% 2.67/1.00  --prep_gs_sim                           true
% 2.67/1.00  --prep_unflatten                        true
% 2.67/1.00  --prep_res_sim                          true
% 2.67/1.00  --prep_upred                            true
% 2.67/1.00  --prep_sem_filter                       exhaustive
% 2.67/1.00  --prep_sem_filter_out                   false
% 2.67/1.00  --pred_elim                             true
% 2.67/1.00  --res_sim_input                         true
% 2.67/1.00  --eq_ax_congr_red                       true
% 2.67/1.00  --pure_diseq_elim                       true
% 2.67/1.00  --brand_transform                       false
% 2.67/1.00  --non_eq_to_eq                          false
% 2.67/1.00  --prep_def_merge                        true
% 2.67/1.00  --prep_def_merge_prop_impl              false
% 2.67/1.00  --prep_def_merge_mbd                    true
% 2.67/1.00  --prep_def_merge_tr_red                 false
% 2.67/1.00  --prep_def_merge_tr_cl                  false
% 2.67/1.00  --smt_preprocessing                     true
% 2.67/1.00  --smt_ac_axioms                         fast
% 2.67/1.00  --preprocessed_out                      false
% 2.67/1.00  --preprocessed_stats                    false
% 2.67/1.00  
% 2.67/1.00  ------ Abstraction refinement Options
% 2.67/1.00  
% 2.67/1.00  --abstr_ref                             []
% 2.67/1.00  --abstr_ref_prep                        false
% 2.67/1.00  --abstr_ref_until_sat                   false
% 2.67/1.00  --abstr_ref_sig_restrict                funpre
% 2.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/1.00  --abstr_ref_under                       []
% 2.67/1.00  
% 2.67/1.00  ------ SAT Options
% 2.67/1.00  
% 2.67/1.00  --sat_mode                              false
% 2.67/1.00  --sat_fm_restart_options                ""
% 2.67/1.00  --sat_gr_def                            false
% 2.67/1.00  --sat_epr_types                         true
% 2.67/1.00  --sat_non_cyclic_types                  false
% 2.67/1.00  --sat_finite_models                     false
% 2.67/1.00  --sat_fm_lemmas                         false
% 2.67/1.00  --sat_fm_prep                           false
% 2.67/1.00  --sat_fm_uc_incr                        true
% 2.67/1.00  --sat_out_model                         small
% 2.67/1.00  --sat_out_clauses                       false
% 2.67/1.00  
% 2.67/1.00  ------ QBF Options
% 2.67/1.00  
% 2.67/1.00  --qbf_mode                              false
% 2.67/1.00  --qbf_elim_univ                         false
% 2.67/1.00  --qbf_dom_inst                          none
% 2.67/1.00  --qbf_dom_pre_inst                      false
% 2.67/1.00  --qbf_sk_in                             false
% 2.67/1.00  --qbf_pred_elim                         true
% 2.67/1.00  --qbf_split                             512
% 2.67/1.00  
% 2.67/1.00  ------ BMC1 Options
% 2.67/1.00  
% 2.67/1.00  --bmc1_incremental                      false
% 2.67/1.00  --bmc1_axioms                           reachable_all
% 2.67/1.00  --bmc1_min_bound                        0
% 2.67/1.00  --bmc1_max_bound                        -1
% 2.67/1.00  --bmc1_max_bound_default                -1
% 2.67/1.00  --bmc1_symbol_reachability              true
% 2.67/1.00  --bmc1_property_lemmas                  false
% 2.67/1.00  --bmc1_k_induction                      false
% 2.67/1.00  --bmc1_non_equiv_states                 false
% 2.67/1.00  --bmc1_deadlock                         false
% 2.67/1.00  --bmc1_ucm                              false
% 2.67/1.00  --bmc1_add_unsat_core                   none
% 2.67/1.00  --bmc1_unsat_core_children              false
% 2.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/1.00  --bmc1_out_stat                         full
% 2.67/1.00  --bmc1_ground_init                      false
% 2.67/1.00  --bmc1_pre_inst_next_state              false
% 2.67/1.00  --bmc1_pre_inst_state                   false
% 2.67/1.00  --bmc1_pre_inst_reach_state             false
% 2.67/1.00  --bmc1_out_unsat_core                   false
% 2.67/1.00  --bmc1_aig_witness_out                  false
% 2.67/1.00  --bmc1_verbose                          false
% 2.67/1.00  --bmc1_dump_clauses_tptp                false
% 2.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.67/1.00  --bmc1_dump_file                        -
% 2.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.67/1.00  --bmc1_ucm_extend_mode                  1
% 2.67/1.00  --bmc1_ucm_init_mode                    2
% 2.67/1.00  --bmc1_ucm_cone_mode                    none
% 2.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.67/1.00  --bmc1_ucm_relax_model                  4
% 2.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/1.00  --bmc1_ucm_layered_model                none
% 2.67/1.00  --bmc1_ucm_max_lemma_size               10
% 2.67/1.00  
% 2.67/1.00  ------ AIG Options
% 2.67/1.00  
% 2.67/1.00  --aig_mode                              false
% 2.67/1.00  
% 2.67/1.00  ------ Instantiation Options
% 2.67/1.00  
% 2.67/1.00  --instantiation_flag                    true
% 2.67/1.00  --inst_sos_flag                         false
% 2.67/1.00  --inst_sos_phase                        true
% 2.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/1.00  --inst_lit_sel_side                     none
% 2.67/1.00  --inst_solver_per_active                1400
% 2.67/1.00  --inst_solver_calls_frac                1.
% 2.67/1.00  --inst_passive_queue_type               priority_queues
% 2.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/1.00  --inst_passive_queues_freq              [25;2]
% 2.67/1.00  --inst_dismatching                      true
% 2.67/1.00  --inst_eager_unprocessed_to_passive     true
% 2.67/1.00  --inst_prop_sim_given                   true
% 2.67/1.00  --inst_prop_sim_new                     false
% 2.67/1.00  --inst_subs_new                         false
% 2.67/1.00  --inst_eq_res_simp                      false
% 2.67/1.00  --inst_subs_given                       false
% 2.67/1.00  --inst_orphan_elimination               true
% 2.67/1.00  --inst_learning_loop_flag               true
% 2.67/1.00  --inst_learning_start                   3000
% 2.67/1.00  --inst_learning_factor                  2
% 2.67/1.00  --inst_start_prop_sim_after_learn       3
% 2.67/1.00  --inst_sel_renew                        solver
% 2.67/1.00  --inst_lit_activity_flag                true
% 2.67/1.00  --inst_restr_to_given                   false
% 2.67/1.00  --inst_activity_threshold               500
% 2.67/1.00  --inst_out_proof                        true
% 2.67/1.00  
% 2.67/1.00  ------ Resolution Options
% 2.67/1.00  
% 2.67/1.00  --resolution_flag                       false
% 2.67/1.00  --res_lit_sel                           adaptive
% 2.67/1.00  --res_lit_sel_side                      none
% 2.67/1.00  --res_ordering                          kbo
% 2.67/1.00  --res_to_prop_solver                    active
% 2.67/1.00  --res_prop_simpl_new                    false
% 2.67/1.00  --res_prop_simpl_given                  true
% 2.67/1.00  --res_passive_queue_type                priority_queues
% 2.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.00  --res_passive_queues_freq               [15;5]
% 2.67/1.00  --res_forward_subs                      full
% 2.67/1.00  --res_backward_subs                     full
% 2.67/1.00  --res_forward_subs_resolution           true
% 2.67/1.00  --res_backward_subs_resolution          true
% 2.67/1.00  --res_orphan_elimination                true
% 2.67/1.00  --res_time_limit                        2.
% 2.67/1.00  --res_out_proof                         true
% 2.67/1.00  
% 2.67/1.00  ------ Superposition Options
% 2.67/1.00  
% 2.67/1.00  --superposition_flag                    true
% 2.67/1.00  --sup_passive_queue_type                priority_queues
% 2.67/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.00  --demod_completeness_check              fast
% 2.67/1.00  --demod_use_ground                      true
% 2.67/1.00  --sup_to_prop_solver                    passive
% 2.67/1.00  --sup_prop_simpl_new                    true
% 2.67/1.00  --sup_prop_simpl_given                  true
% 2.67/1.00  --sup_fun_splitting                     false
% 2.67/1.00  --sup_smt_interval                      50000
% 2.67/1.00  
% 2.67/1.00  ------ Superposition Simplification Setup
% 2.67/1.00  
% 2.67/1.00  --sup_indices_passive                   []
% 2.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_full_bw                           [BwDemod]
% 2.67/1.00  --sup_immed_triv                        [TrivRules]
% 2.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_immed_bw_main                     []
% 2.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.00  
% 2.67/1.00  ------ Combination Options
% 2.67/1.00  
% 2.67/1.00  --comb_res_mult                         3
% 2.67/1.00  --comb_sup_mult                         2
% 2.67/1.00  --comb_inst_mult                        10
% 2.67/1.00  
% 2.67/1.00  ------ Debug Options
% 2.67/1.00  
% 2.67/1.00  --dbg_backtrace                         false
% 2.67/1.00  --dbg_dump_prop_clauses                 false
% 2.67/1.00  --dbg_dump_prop_clauses_file            -
% 2.67/1.00  --dbg_out_stat                          false
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  ------ Proving...
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  % SZS status Theorem for theBenchmark.p
% 2.67/1.00  
% 2.67/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/1.00  
% 2.67/1.00  fof(f12,conjecture,(
% 2.67/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f13,negated_conjecture,(
% 2.67/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.67/1.00    inference(negated_conjecture,[],[f12])).
% 2.67/1.00  
% 2.67/1.00  fof(f24,plain,(
% 2.67/1.00    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.67/1.00    inference(ennf_transformation,[],[f13])).
% 2.67/1.00  
% 2.67/1.00  fof(f25,plain,(
% 2.67/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.67/1.00    inference(flattening,[],[f24])).
% 2.67/1.00  
% 2.67/1.00  fof(f43,plain,(
% 2.67/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK6) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK6,X0,X1) & v1_funct_1(sK6))) )),
% 2.67/1.00    introduced(choice_axiom,[])).
% 2.67/1.00  
% 2.67/1.00  fof(f42,plain,(
% 2.67/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 2.67/1.00    introduced(choice_axiom,[])).
% 2.67/1.00  
% 2.67/1.00  fof(f44,plain,(
% 2.67/1.00    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 2.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f25,f43,f42])).
% 2.67/1.00  
% 2.67/1.00  fof(f74,plain,(
% 2.67/1.00    v1_funct_2(sK6,sK3,sK4)),
% 2.67/1.00    inference(cnf_transformation,[],[f44])).
% 2.67/1.00  
% 2.67/1.00  fof(f11,axiom,(
% 2.67/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f22,plain,(
% 2.67/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.00    inference(ennf_transformation,[],[f11])).
% 2.67/1.00  
% 2.67/1.00  fof(f23,plain,(
% 2.67/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.00    inference(flattening,[],[f22])).
% 2.67/1.00  
% 2.67/1.00  fof(f41,plain,(
% 2.67/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.00    inference(nnf_transformation,[],[f23])).
% 2.67/1.00  
% 2.67/1.00  fof(f64,plain,(
% 2.67/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.00    inference(cnf_transformation,[],[f41])).
% 2.67/1.00  
% 2.67/1.00  fof(f75,plain,(
% 2.67/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.67/1.00    inference(cnf_transformation,[],[f44])).
% 2.67/1.00  
% 2.67/1.00  fof(f9,axiom,(
% 2.67/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f19,plain,(
% 2.67/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.00    inference(ennf_transformation,[],[f9])).
% 2.67/1.00  
% 2.67/1.00  fof(f61,plain,(
% 2.67/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.00    inference(cnf_transformation,[],[f19])).
% 2.67/1.00  
% 2.67/1.00  fof(f71,plain,(
% 2.67/1.00    v1_funct_2(sK5,sK3,sK4)),
% 2.67/1.00    inference(cnf_transformation,[],[f44])).
% 2.67/1.00  
% 2.67/1.00  fof(f72,plain,(
% 2.67/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.67/1.00    inference(cnf_transformation,[],[f44])).
% 2.67/1.00  
% 2.67/1.00  fof(f7,axiom,(
% 2.67/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f16,plain,(
% 2.67/1.00    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.67/1.00    inference(ennf_transformation,[],[f7])).
% 2.67/1.00  
% 2.67/1.00  fof(f17,plain,(
% 2.67/1.00    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.67/1.00    inference(flattening,[],[f16])).
% 2.67/1.00  
% 2.67/1.00  fof(f38,plain,(
% 2.67/1.00    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 2.67/1.00    introduced(choice_axiom,[])).
% 2.67/1.00  
% 2.67/1.00  fof(f39,plain,(
% 2.67/1.00    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f38])).
% 2.67/1.00  
% 2.67/1.00  fof(f58,plain,(
% 2.67/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f39])).
% 2.67/1.00  
% 2.67/1.00  fof(f73,plain,(
% 2.67/1.00    v1_funct_1(sK6)),
% 2.67/1.00    inference(cnf_transformation,[],[f44])).
% 2.67/1.00  
% 2.67/1.00  fof(f8,axiom,(
% 2.67/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f18,plain,(
% 2.67/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.00    inference(ennf_transformation,[],[f8])).
% 2.67/1.00  
% 2.67/1.00  fof(f60,plain,(
% 2.67/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.00    inference(cnf_transformation,[],[f18])).
% 2.67/1.00  
% 2.67/1.00  fof(f10,axiom,(
% 2.67/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f20,plain,(
% 2.67/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.67/1.00    inference(ennf_transformation,[],[f10])).
% 2.67/1.00  
% 2.67/1.00  fof(f21,plain,(
% 2.67/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.00    inference(flattening,[],[f20])).
% 2.67/1.00  
% 2.67/1.00  fof(f40,plain,(
% 2.67/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.00    inference(nnf_transformation,[],[f21])).
% 2.67/1.00  
% 2.67/1.00  fof(f63,plain,(
% 2.67/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.00    inference(cnf_transformation,[],[f40])).
% 2.67/1.00  
% 2.67/1.00  fof(f82,plain,(
% 2.67/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.00    inference(equality_resolution,[],[f63])).
% 2.67/1.00  
% 2.67/1.00  fof(f77,plain,(
% 2.67/1.00    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 2.67/1.00    inference(cnf_transformation,[],[f44])).
% 2.67/1.00  
% 2.67/1.00  fof(f4,axiom,(
% 2.67/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f34,plain,(
% 2.67/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.67/1.00    inference(nnf_transformation,[],[f4])).
% 2.67/1.00  
% 2.67/1.00  fof(f35,plain,(
% 2.67/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.67/1.00    inference(flattening,[],[f34])).
% 2.67/1.00  
% 2.67/1.00  fof(f53,plain,(
% 2.67/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f35])).
% 2.67/1.00  
% 2.67/1.00  fof(f51,plain,(
% 2.67/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.67/1.00    inference(cnf_transformation,[],[f35])).
% 2.67/1.00  
% 2.67/1.00  fof(f79,plain,(
% 2.67/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.67/1.00    inference(equality_resolution,[],[f51])).
% 2.67/1.00  
% 2.67/1.00  fof(f70,plain,(
% 2.67/1.00    v1_funct_1(sK5)),
% 2.67/1.00    inference(cnf_transformation,[],[f44])).
% 2.67/1.00  
% 2.67/1.00  fof(f76,plain,(
% 2.67/1.00    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f44])).
% 2.67/1.00  
% 2.67/1.00  fof(f59,plain,(
% 2.67/1.00    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f39])).
% 2.67/1.00  
% 2.67/1.00  fof(f6,axiom,(
% 2.67/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f15,plain,(
% 2.67/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.67/1.00    inference(ennf_transformation,[],[f6])).
% 2.67/1.00  
% 2.67/1.00  fof(f57,plain,(
% 2.67/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f15])).
% 2.67/1.00  
% 2.67/1.00  fof(f5,axiom,(
% 2.67/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f36,plain,(
% 2.67/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.67/1.00    inference(nnf_transformation,[],[f5])).
% 2.67/1.00  
% 2.67/1.00  fof(f37,plain,(
% 2.67/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.67/1.00    inference(flattening,[],[f36])).
% 2.67/1.00  
% 2.67/1.00  fof(f56,plain,(
% 2.67/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.67/1.00    inference(cnf_transformation,[],[f37])).
% 2.67/1.00  
% 2.67/1.00  fof(f80,plain,(
% 2.67/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.67/1.00    inference(equality_resolution,[],[f56])).
% 2.67/1.00  
% 2.67/1.00  fof(f2,axiom,(
% 2.67/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f14,plain,(
% 2.67/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.67/1.00    inference(ennf_transformation,[],[f2])).
% 2.67/1.00  
% 2.67/1.00  fof(f30,plain,(
% 2.67/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.67/1.00    inference(nnf_transformation,[],[f14])).
% 2.67/1.00  
% 2.67/1.00  fof(f31,plain,(
% 2.67/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.67/1.00    inference(rectify,[],[f30])).
% 2.67/1.00  
% 2.67/1.00  fof(f32,plain,(
% 2.67/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.67/1.00    introduced(choice_axiom,[])).
% 2.67/1.00  
% 2.67/1.00  fof(f33,plain,(
% 2.67/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 2.67/1.00  
% 2.67/1.00  fof(f48,plain,(
% 2.67/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f33])).
% 2.67/1.00  
% 2.67/1.00  fof(f3,axiom,(
% 2.67/1.00    v1_xboole_0(k1_xboole_0)),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f50,plain,(
% 2.67/1.00    v1_xboole_0(k1_xboole_0)),
% 2.67/1.00    inference(cnf_transformation,[],[f3])).
% 2.67/1.00  
% 2.67/1.00  fof(f55,plain,(
% 2.67/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.67/1.00    inference(cnf_transformation,[],[f37])).
% 2.67/1.00  
% 2.67/1.00  fof(f81,plain,(
% 2.67/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.67/1.00    inference(equality_resolution,[],[f55])).
% 2.67/1.00  
% 2.67/1.00  fof(f54,plain,(
% 2.67/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f37])).
% 2.67/1.00  
% 2.67/1.00  cnf(c_28,negated_conjecture,
% 2.67/1.00      ( v1_funct_2(sK6,sK3,sK4) ),
% 2.67/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_24,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.67/1.00      | k1_xboole_0 = X2 ),
% 2.67/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_27,negated_conjecture,
% 2.67/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.67/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_423,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.67/1.00      | sK6 != X0
% 2.67/1.00      | k1_xboole_0 = X2 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_27]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_424,plain,
% 2.67/1.00      ( ~ v1_funct_2(sK6,X0,X1)
% 2.67/1.00      | k1_relset_1(X0,X1,sK6) = X0
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.67/1.00      | k1_xboole_0 = X1 ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_423]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_853,plain,
% 2.67/1.00      ( k1_relset_1(X0,X1,sK6) = X0
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.67/1.00      | sK6 != sK6
% 2.67/1.00      | sK4 != X1
% 2.67/1.00      | sK3 != X0
% 2.67/1.00      | k1_xboole_0 = X1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_424]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_854,plain,
% 2.67/1.00      ( k1_relset_1(sK3,sK4,sK6) = sK3
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.67/1.00      | k1_xboole_0 = sK4 ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_853]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1627,plain,
% 2.67/1.00      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 2.67/1.00      inference(equality_resolution_simp,[status(thm)],[c_854]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_16,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_459,plain,
% 2.67/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.67/1.00      | sK6 != X2 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_460,plain,
% 2.67/1.00      ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_459]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1791,plain,
% 2.67/1.00      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 2.67/1.00      inference(equality_resolution,[status(thm)],[c_460]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2716,plain,
% 2.67/1.00      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 2.67/1.00      inference(demodulation,[status(thm)],[c_1627,c_1791]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_31,negated_conjecture,
% 2.67/1.00      ( v1_funct_2(sK5,sK3,sK4) ),
% 2.67/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_30,negated_conjecture,
% 2.67/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.67/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_480,plain,
% 2.67/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.67/1.00      | sK5 != X0
% 2.67/1.00      | k1_xboole_0 = X2 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_481,plain,
% 2.67/1.00      ( ~ v1_funct_2(sK5,X0,X1)
% 2.67/1.00      | k1_relset_1(X0,X1,sK5) = X0
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.67/1.00      | k1_xboole_0 = X1 ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_480]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_938,plain,
% 2.67/1.00      ( k1_relset_1(X0,X1,sK5) = X0
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.67/1.00      | sK5 != sK5
% 2.67/1.00      | sK4 != X1
% 2.67/1.00      | sK3 != X0
% 2.67/1.00      | k1_xboole_0 = X1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_31,c_481]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_939,plain,
% 2.67/1.00      ( k1_relset_1(sK3,sK4,sK5) = sK3
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.67/1.00      | k1_xboole_0 = sK4 ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_938]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1622,plain,
% 2.67/1.00      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 2.67/1.00      inference(equality_resolution_simp,[status(thm)],[c_939]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_516,plain,
% 2.67/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.67/1.00      | sK5 != X2 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_30]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_517,plain,
% 2.67/1.00      ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_516]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1794,plain,
% 2.67/1.00      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 2.67/1.00      inference(equality_resolution,[status(thm)],[c_517]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2713,plain,
% 2.67/1.00      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 2.67/1.00      inference(demodulation,[status(thm)],[c_1622,c_1794]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_14,plain,
% 2.67/1.00      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 2.67/1.00      | ~ v1_relat_1(X1)
% 2.67/1.00      | ~ v1_relat_1(X0)
% 2.67/1.00      | ~ v1_funct_1(X1)
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | X1 = X0
% 2.67/1.00      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1522,plain,
% 2.67/1.00      ( X0 = X1
% 2.67/1.00      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.67/1.00      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 2.67/1.00      | v1_relat_1(X1) != iProver_top
% 2.67/1.00      | v1_relat_1(X0) != iProver_top
% 2.67/1.00      | v1_funct_1(X0) != iProver_top
% 2.67/1.00      | v1_funct_1(X1) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2838,plain,
% 2.67/1.00      ( k1_relat_1(X0) != sK3
% 2.67/1.00      | sK6 = X0
% 2.67/1.00      | sK4 = k1_xboole_0
% 2.67/1.00      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.67/1.00      | v1_relat_1(X0) != iProver_top
% 2.67/1.00      | v1_relat_1(sK6) != iProver_top
% 2.67/1.00      | v1_funct_1(X0) != iProver_top
% 2.67/1.00      | v1_funct_1(sK6) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_2716,c_1522]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_29,negated_conjecture,
% 2.67/1.00      ( v1_funct_1(sK6) ),
% 2.67/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_36,plain,
% 2.67/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1124,plain,( X0 = X0 ),theory(equality) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1784,plain,
% 2.67/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1124]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_15,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.00      | v1_relat_1(X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_468,plain,
% 2.67/1.00      ( v1_relat_1(X0)
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.67/1.00      | sK6 != X0 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_469,plain,
% 2.67/1.00      ( v1_relat_1(sK6)
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_468]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1965,plain,
% 2.67/1.00      ( v1_relat_1(sK6)
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_469]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1966,plain,
% 2.67/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.67/1.00      | v1_relat_1(sK6) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1965]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3816,plain,
% 2.67/1.00      ( v1_funct_1(X0) != iProver_top
% 2.67/1.00      | k1_relat_1(X0) != sK3
% 2.67/1.00      | sK6 = X0
% 2.67/1.00      | sK4 = k1_xboole_0
% 2.67/1.00      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_2838,c_36,c_1784,c_1966]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3817,plain,
% 2.67/1.00      ( k1_relat_1(X0) != sK3
% 2.67/1.00      | sK6 = X0
% 2.67/1.00      | sK4 = k1_xboole_0
% 2.67/1.00      | r2_hidden(sK2(X0,sK6),k1_relat_1(X0)) = iProver_top
% 2.67/1.00      | v1_relat_1(X0) != iProver_top
% 2.67/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.67/1.00      inference(renaming,[status(thm)],[c_3816]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3829,plain,
% 2.67/1.00      ( sK6 = sK5
% 2.67/1.00      | sK4 = k1_xboole_0
% 2.67/1.00      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
% 2.67/1.00      | v1_relat_1(sK5) != iProver_top
% 2.67/1.00      | v1_funct_1(sK5) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_2713,c_3817]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_17,plain,
% 2.67/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 2.67/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.67/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_25,negated_conjecture,
% 2.67/1.00      ( ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
% 2.67/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_328,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.00      | sK6 != X0
% 2.67/1.00      | sK5 != X0
% 2.67/1.00      | sK4 != X2
% 2.67/1.00      | sK3 != X1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_329,plain,
% 2.67/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.67/1.00      | sK5 != sK6 ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_328]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6,plain,
% 2.67/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.67/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1916,plain,
% 2.67/1.00      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | X0 = sK5 ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2180,plain,
% 2.67/1.00      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1916]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_8,plain,
% 2.67/1.00      ( r1_tarski(X0,X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2181,plain,
% 2.67/1.00      ( r1_tarski(sK5,sK5) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1125,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1833,plain,
% 2.67/1.00      ( sK6 != X0 | sK5 != X0 | sK5 = sK6 ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1125]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3651,plain,
% 2.67/1.00      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1833]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2841,plain,
% 2.67/1.00      ( k1_relat_1(X0) != sK3
% 2.67/1.00      | sK5 = X0
% 2.67/1.00      | sK4 = k1_xboole_0
% 2.67/1.00      | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 2.67/1.00      | v1_relat_1(X0) != iProver_top
% 2.67/1.00      | v1_relat_1(sK5) != iProver_top
% 2.67/1.00      | v1_funct_1(X0) != iProver_top
% 2.67/1.00      | v1_funct_1(sK5) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_2713,c_1522]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_32,negated_conjecture,
% 2.67/1.00      ( v1_funct_1(sK5) ),
% 2.67/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_33,plain,
% 2.67/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_525,plain,
% 2.67/1.00      ( v1_relat_1(X0)
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.67/1.00      | sK5 != X0 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_30]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_526,plain,
% 2.67/1.00      ( v1_relat_1(sK5)
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_525]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1964,plain,
% 2.67/1.00      ( v1_relat_1(sK5)
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_526]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1968,plain,
% 2.67/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.67/1.00      | v1_relat_1(sK5) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1964]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6131,plain,
% 2.67/1.00      ( v1_funct_1(X0) != iProver_top
% 2.67/1.00      | k1_relat_1(X0) != sK3
% 2.67/1.00      | sK5 = X0
% 2.67/1.00      | sK4 = k1_xboole_0
% 2.67/1.00      | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 2.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_2841,c_33,c_1784,c_1968]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6132,plain,
% 2.67/1.00      ( k1_relat_1(X0) != sK3
% 2.67/1.00      | sK5 = X0
% 2.67/1.00      | sK4 = k1_xboole_0
% 2.67/1.00      | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 2.67/1.00      | v1_relat_1(X0) != iProver_top
% 2.67/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.67/1.00      inference(renaming,[status(thm)],[c_6131]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6143,plain,
% 2.67/1.00      ( sK6 = sK5
% 2.67/1.00      | sK4 = k1_xboole_0
% 2.67/1.00      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top
% 2.67/1.00      | v1_relat_1(sK6) != iProver_top
% 2.67/1.00      | v1_funct_1(sK6) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_2716,c_6132]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6382,plain,
% 2.67/1.00      ( sK4 = k1_xboole_0
% 2.67/1.00      | r2_hidden(sK2(sK5,sK6),k1_relat_1(sK5)) = iProver_top ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_3829,c_33,c_27,c_329,c_1784,c_1968,c_2180,c_2181,
% 2.67/1.00                 c_3651]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6388,plain,
% 2.67/1.00      ( sK4 = k1_xboole_0 | r2_hidden(sK2(sK5,sK6),sK3) = iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_2713,c_6382]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_26,negated_conjecture,
% 2.67/1.00      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1521,plain,
% 2.67/1.00      ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,X0)
% 2.67/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6501,plain,
% 2.67/1.00      ( k1_funct_1(sK5,sK2(sK5,sK6)) = k1_funct_1(sK6,sK2(sK5,sK6))
% 2.67/1.00      | sK4 = k1_xboole_0 ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_6388,c_1521]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_13,plain,
% 2.67/1.00      ( ~ v1_relat_1(X0)
% 2.67/1.00      | ~ v1_relat_1(X1)
% 2.67/1.00      | ~ v1_funct_1(X0)
% 2.67/1.00      | ~ v1_funct_1(X1)
% 2.67/1.00      | X0 = X1
% 2.67/1.00      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 2.67/1.00      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.67/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1523,plain,
% 2.67/1.00      ( X0 = X1
% 2.67/1.00      | k1_funct_1(X0,sK2(X1,X0)) != k1_funct_1(X1,sK2(X1,X0))
% 2.67/1.00      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.67/1.00      | v1_relat_1(X0) != iProver_top
% 2.67/1.00      | v1_relat_1(X1) != iProver_top
% 2.67/1.00      | v1_funct_1(X1) != iProver_top
% 2.67/1.00      | v1_funct_1(X0) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6522,plain,
% 2.67/1.00      ( k1_relat_1(sK5) != k1_relat_1(sK6)
% 2.67/1.00      | sK6 = sK5
% 2.67/1.00      | sK4 = k1_xboole_0
% 2.67/1.00      | v1_relat_1(sK6) != iProver_top
% 2.67/1.00      | v1_relat_1(sK5) != iProver_top
% 2.67/1.00      | v1_funct_1(sK6) != iProver_top
% 2.67/1.00      | v1_funct_1(sK5) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_6501,c_1523]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6523,plain,
% 2.67/1.00      ( ~ v1_relat_1(sK6)
% 2.67/1.00      | ~ v1_relat_1(sK5)
% 2.67/1.00      | ~ v1_funct_1(sK6)
% 2.67/1.00      | ~ v1_funct_1(sK5)
% 2.67/1.00      | k1_relat_1(sK5) != k1_relat_1(sK6)
% 2.67/1.00      | sK6 = sK5
% 2.67/1.00      | sK4 = k1_xboole_0 ),
% 2.67/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6522]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6604,plain,
% 2.67/1.00      ( k1_relat_1(sK5) != k1_relat_1(sK6) | sK4 = k1_xboole_0 ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_6522,c_32,c_29,c_27,c_329,c_1784,c_1965,c_1964,c_2180,
% 2.67/1.00                 c_2181,c_3651,c_6523]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6608,plain,
% 2.67/1.00      ( k1_relat_1(sK5) != sK3 | sK4 = k1_xboole_0 ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_2716,c_6604]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6609,plain,
% 2.67/1.00      ( sK4 = k1_xboole_0 ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_6608,c_2713]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_12,plain,
% 2.67/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.67/1.00      | ~ r2_hidden(X2,X0)
% 2.67/1.00      | ~ v1_xboole_0(X1) ),
% 2.67/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_408,plain,
% 2.67/1.00      ( ~ r2_hidden(X0,X1)
% 2.67/1.00      | ~ v1_xboole_0(X2)
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X2)
% 2.67/1.00      | sK5 != X1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_30]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_409,plain,
% 2.67/1.00      ( ~ r2_hidden(X0,sK5)
% 2.67/1.00      | ~ v1_xboole_0(X1)
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X1) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_408]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1118,plain,
% 2.67/1.00      ( ~ v1_xboole_0(X0)
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0)
% 2.67/1.00      | ~ sP0_iProver_split ),
% 2.67/1.00      inference(splitting,
% 2.67/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.67/1.00                [c_409]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1515,plain,
% 2.67/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0)
% 2.67/1.00      | v1_xboole_0(X0) != iProver_top
% 2.67/1.00      | sP0_iProver_split != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1118]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6623,plain,
% 2.67/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)) != k1_zfmisc_1(X0)
% 2.67/1.00      | v1_xboole_0(X0) != iProver_top
% 2.67/1.00      | sP0_iProver_split != iProver_top ),
% 2.67/1.00      inference(demodulation,[status(thm)],[c_6609,c_1515]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_9,plain,
% 2.67/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.67/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6693,plain,
% 2.67/1.00      ( k1_zfmisc_1(X0) != k1_zfmisc_1(k1_xboole_0)
% 2.67/1.00      | v1_xboole_0(X0) != iProver_top
% 2.67/1.00      | sP0_iProver_split != iProver_top ),
% 2.67/1.00      inference(demodulation,[status(thm)],[c_6623,c_9]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6756,plain,
% 2.67/1.00      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 2.67/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top
% 2.67/1.00      | sP0_iProver_split != iProver_top ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_6693]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_393,plain,
% 2.67/1.00      ( ~ r2_hidden(X0,X1)
% 2.67/1.00      | ~ v1_xboole_0(X2)
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X2)
% 2.67/1.00      | sK6 != X1 ),
% 2.67/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_394,plain,
% 2.67/1.00      ( ~ r2_hidden(X0,sK6)
% 2.67/1.00      | ~ v1_xboole_0(X1)
% 2.67/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X1) ),
% 2.67/1.00      inference(unflattening,[status(thm)],[c_393]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1122,plain,
% 2.67/1.00      ( sP2_iProver_split | sP0_iProver_split ),
% 2.67/1.00      inference(splitting,
% 2.67/1.00                [splitting(split),new_symbols(definition,[])],
% 2.67/1.00                [c_394]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1516,plain,
% 2.67/1.00      ( sP2_iProver_split = iProver_top
% 2.67/1.00      | sP0_iProver_split = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1122]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3,plain,
% 2.67/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1528,plain,
% 2.67/1.00      ( r1_tarski(X0,X1) = iProver_top
% 2.67/1.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1119,plain,
% 2.67/1.00      ( ~ r2_hidden(X0,sK5) | ~ sP1_iProver_split ),
% 2.67/1.00      inference(splitting,
% 2.67/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.67/1.00                [c_409]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1514,plain,
% 2.67/1.00      ( r2_hidden(X0,sK5) != iProver_top
% 2.67/1.00      | sP1_iProver_split != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1119]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3008,plain,
% 2.67/1.00      ( r1_tarski(sK5,X0) = iProver_top
% 2.67/1.00      | sP1_iProver_split != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1528,c_1514]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1121,plain,
% 2.67/1.00      ( ~ r2_hidden(X0,sK6) | ~ sP2_iProver_split ),
% 2.67/1.00      inference(splitting,
% 2.67/1.00                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.67/1.00                [c_394]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1517,plain,
% 2.67/1.00      ( r2_hidden(X0,sK6) != iProver_top
% 2.67/1.00      | sP2_iProver_split != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1121]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3007,plain,
% 2.67/1.00      ( r1_tarski(sK6,X0) = iProver_top
% 2.67/1.00      | sP2_iProver_split != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1528,c_1517]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1525,plain,
% 2.67/1.00      ( X0 = X1
% 2.67/1.00      | r1_tarski(X1,X0) != iProver_top
% 2.67/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3351,plain,
% 2.67/1.00      ( sK6 = X0
% 2.67/1.00      | r1_tarski(X0,sK6) != iProver_top
% 2.67/1.00      | sP2_iProver_split != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_3007,c_1525]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3620,plain,
% 2.67/1.00      ( sK6 = sK5
% 2.67/1.00      | sP2_iProver_split != iProver_top
% 2.67/1.00      | sP1_iProver_split != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_3008,c_3351]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3638,plain,
% 2.67/1.00      ( sK6 = sK5
% 2.67/1.00      | sP1_iProver_split != iProver_top
% 2.67/1.00      | sP0_iProver_split = iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1516,c_3620]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1120,plain,
% 2.67/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 2.67/1.00      inference(splitting,
% 2.67/1.00                [splitting(split),new_symbols(definition,[])],
% 2.67/1.00                [c_409]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1148,plain,
% 2.67/1.00      ( sP1_iProver_split = iProver_top
% 2.67/1.00      | sP0_iProver_split = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1120]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3641,plain,
% 2.67/1.00      ( sK6 = sK5 | sP0_iProver_split = iProver_top ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_3638,c_1148]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1129,plain,
% 2.67/1.00      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.67/1.00      theory(equality) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1138,plain,
% 2.67/1.00      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 2.67/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_1129]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_5,plain,
% 2.67/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_91,plain,
% 2.67/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_10,plain,
% 2.67/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.67/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_83,plain,
% 2.67/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_11,plain,
% 2.67/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.67/1.00      | k1_xboole_0 = X1
% 2.67/1.00      | k1_xboole_0 = X0 ),
% 2.67/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_82,plain,
% 2.67/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.67/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 2.67/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(contradiction,plain,
% 2.67/1.00      ( $false ),
% 2.67/1.00      inference(minisat,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_6756,c_3651,c_3641,c_2181,c_2180,c_1138,c_329,c_91,
% 2.67/1.00                 c_83,c_82,c_27]) ).
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/1.00  
% 2.67/1.00  ------                               Statistics
% 2.67/1.00  
% 2.67/1.00  ------ General
% 2.67/1.00  
% 2.67/1.00  abstr_ref_over_cycles:                  0
% 2.67/1.00  abstr_ref_under_cycles:                 0
% 2.67/1.00  gc_basic_clause_elim:                   0
% 2.67/1.00  forced_gc_time:                         0
% 2.67/1.00  parsing_time:                           0.008
% 2.67/1.00  unif_index_cands_time:                  0.
% 2.67/1.00  unif_index_add_time:                    0.
% 2.67/1.00  orderings_time:                         0.
% 2.67/1.00  out_proof_time:                         0.017
% 2.67/1.00  total_time:                             0.214
% 2.67/1.00  num_of_symbols:                         55
% 2.67/1.00  num_of_terms:                           4655
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing
% 2.67/1.00  
% 2.67/1.00  num_of_splits:                          4
% 2.67/1.00  num_of_split_atoms:                     3
% 2.67/1.00  num_of_reused_defs:                     1
% 2.67/1.00  num_eq_ax_congr_red:                    18
% 2.67/1.00  num_of_sem_filtered_clauses:            1
% 2.67/1.00  num_of_subtypes:                        0
% 2.67/1.00  monotx_restored_types:                  0
% 2.67/1.00  sat_num_of_epr_types:                   0
% 2.67/1.00  sat_num_of_non_cyclic_types:            0
% 2.67/1.00  sat_guarded_non_collapsed_types:        0
% 2.67/1.00  num_pure_diseq_elim:                    0
% 2.67/1.00  simp_replaced_by:                       0
% 2.67/1.00  res_preprocessed:                       127
% 2.67/1.00  prep_upred:                             0
% 2.67/1.00  prep_unflattend:                        107
% 2.67/1.00  smt_new_axioms:                         0
% 2.67/1.00  pred_elim_cands:                        8
% 2.67/1.00  pred_elim:                              3
% 2.67/1.00  pred_elim_cl:                           -1
% 2.67/1.00  pred_elim_cycles:                       6
% 2.67/1.00  merged_defs:                            0
% 2.67/1.00  merged_defs_ncl:                        0
% 2.67/1.00  bin_hyper_res:                          0
% 2.67/1.00  prep_cycles:                            3
% 2.67/1.00  pred_elim_time:                         0.015
% 2.67/1.00  splitting_time:                         0.
% 2.67/1.00  sem_filter_time:                        0.
% 2.67/1.00  monotx_time:                            0.
% 2.67/1.00  subtype_inf_time:                       0.
% 2.67/1.00  
% 2.67/1.00  ------ Problem properties
% 2.67/1.00  
% 2.67/1.00  clauses:                                37
% 2.67/1.00  conjectures:                            3
% 2.67/1.00  epr:                                    12
% 2.67/1.00  horn:                                   25
% 2.67/1.00  ground:                                 12
% 2.67/1.00  unary:                                  7
% 2.67/1.00  binary:                                 13
% 2.67/1.00  lits:                                   100
% 2.67/1.00  lits_eq:                                59
% 2.67/1.00  fd_pure:                                0
% 2.67/1.00  fd_pseudo:                              0
% 2.67/1.00  fd_cond:                                1
% 2.67/1.00  fd_pseudo_cond:                         3
% 2.67/1.00  ac_symbols:                             0
% 2.67/1.00  
% 2.67/1.00  ------ Propositional Solver
% 2.67/1.00  
% 2.67/1.00  prop_solver_calls:                      24
% 2.67/1.00  prop_fast_solver_calls:                 1216
% 2.67/1.00  smt_solver_calls:                       0
% 2.67/1.00  smt_fast_solver_calls:                  0
% 2.67/1.00  prop_num_of_clauses:                    1984
% 2.67/1.00  prop_preprocess_simplified:             5418
% 2.67/1.00  prop_fo_subsumed:                       36
% 2.67/1.00  prop_solver_time:                       0.
% 2.67/1.00  smt_solver_time:                        0.
% 2.67/1.00  smt_fast_solver_time:                   0.
% 2.67/1.00  prop_fast_solver_time:                  0.
% 2.67/1.00  prop_unsat_core_time:                   0.
% 2.67/1.00  
% 2.67/1.00  ------ QBF
% 2.67/1.00  
% 2.67/1.00  qbf_q_res:                              0
% 2.67/1.00  qbf_num_tautologies:                    0
% 2.67/1.00  qbf_prep_cycles:                        0
% 2.67/1.00  
% 2.67/1.00  ------ BMC1
% 2.67/1.00  
% 2.67/1.00  bmc1_current_bound:                     -1
% 2.67/1.00  bmc1_last_solved_bound:                 -1
% 2.67/1.00  bmc1_unsat_core_size:                   -1
% 2.67/1.00  bmc1_unsat_core_parents_size:           -1
% 2.67/1.00  bmc1_merge_next_fun:                    0
% 2.67/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.67/1.00  
% 2.67/1.00  ------ Instantiation
% 2.67/1.00  
% 2.67/1.00  inst_num_of_clauses:                    654
% 2.67/1.00  inst_num_in_passive:                    49
% 2.67/1.00  inst_num_in_active:                     361
% 2.67/1.00  inst_num_in_unprocessed:                244
% 2.67/1.00  inst_num_of_loops:                      510
% 2.67/1.00  inst_num_of_learning_restarts:          0
% 2.67/1.00  inst_num_moves_active_passive:          146
% 2.67/1.00  inst_lit_activity:                      0
% 2.67/1.00  inst_lit_activity_moves:                0
% 2.67/1.00  inst_num_tautologies:                   0
% 2.67/1.00  inst_num_prop_implied:                  0
% 2.67/1.00  inst_num_existing_simplified:           0
% 2.67/1.00  inst_num_eq_res_simplified:             0
% 2.67/1.00  inst_num_child_elim:                    0
% 2.67/1.00  inst_num_of_dismatching_blockings:      103
% 2.67/1.00  inst_num_of_non_proper_insts:           830
% 2.67/1.00  inst_num_of_duplicates:                 0
% 2.67/1.00  inst_inst_num_from_inst_to_res:         0
% 2.67/1.00  inst_dismatching_checking_time:         0.
% 2.67/1.00  
% 2.67/1.00  ------ Resolution
% 2.67/1.00  
% 2.67/1.00  res_num_of_clauses:                     0
% 2.67/1.00  res_num_in_passive:                     0
% 2.67/1.00  res_num_in_active:                      0
% 2.67/1.00  res_num_of_loops:                       130
% 2.67/1.00  res_forward_subset_subsumed:            109
% 2.67/1.00  res_backward_subset_subsumed:           0
% 2.67/1.00  res_forward_subsumed:                   7
% 2.67/1.00  res_backward_subsumed:                  3
% 2.67/1.00  res_forward_subsumption_resolution:     0
% 2.67/1.00  res_backward_subsumption_resolution:    0
% 2.67/1.00  res_clause_to_clause_subsumption:       660
% 2.67/1.00  res_orphan_elimination:                 0
% 2.67/1.00  res_tautology_del:                      90
% 2.67/1.00  res_num_eq_res_simplified:              2
% 2.67/1.00  res_num_sel_changes:                    0
% 2.67/1.00  res_moves_from_active_to_pass:          0
% 2.67/1.00  
% 2.67/1.00  ------ Superposition
% 2.67/1.00  
% 2.67/1.00  sup_time_total:                         0.
% 2.67/1.00  sup_time_generating:                    0.
% 2.67/1.00  sup_time_sim_full:                      0.
% 2.67/1.00  sup_time_sim_immed:                     0.
% 2.67/1.00  
% 2.67/1.00  sup_num_of_clauses:                     98
% 2.67/1.00  sup_num_in_active:                      77
% 2.67/1.00  sup_num_in_passive:                     21
% 2.67/1.00  sup_num_of_loops:                       101
% 2.67/1.00  sup_fw_superposition:                   191
% 2.67/1.00  sup_bw_superposition:                   101
% 2.67/1.00  sup_immediate_simplified:               109
% 2.67/1.00  sup_given_eliminated:                   0
% 2.67/1.00  comparisons_done:                       0
% 2.67/1.00  comparisons_avoided:                    41
% 2.67/1.00  
% 2.67/1.00  ------ Simplifications
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  sim_fw_subset_subsumed:                 41
% 2.67/1.00  sim_bw_subset_subsumed:                 6
% 2.67/1.00  sim_fw_subsumed:                        43
% 2.67/1.00  sim_bw_subsumed:                        5
% 2.67/1.00  sim_fw_subsumption_res:                 0
% 2.67/1.00  sim_bw_subsumption_res:                 0
% 2.67/1.00  sim_tautology_del:                      7
% 2.67/1.00  sim_eq_tautology_del:                   61
% 2.67/1.00  sim_eq_res_simp:                        12
% 2.67/1.00  sim_fw_demodulated:                     23
% 2.67/1.00  sim_bw_demodulated:                     30
% 2.67/1.00  sim_light_normalised:                   5
% 2.67/1.00  sim_joinable_taut:                      0
% 2.67/1.00  sim_joinable_simp:                      0
% 2.67/1.00  sim_ac_normalised:                      0
% 2.67/1.00  sim_smt_subsumption:                    0
% 2.67/1.00  
%------------------------------------------------------------------------------
