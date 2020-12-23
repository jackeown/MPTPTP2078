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
% DateTime   : Thu Dec  3 12:07:43 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  162 (1579 expanded)
%              Number of clauses        :   97 ( 477 expanded)
%              Number of leaves         :   17 ( 378 expanded)
%              Depth                    :   26
%              Number of atoms          :  547 (9878 expanded)
%              Number of equality atoms :  259 (2354 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(nnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

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
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f43,f42])).

fof(f77,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f74,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f38])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f80,plain,(
    ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
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

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_688,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_689,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_691,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_689,c_30])).

cnf(c_1706,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1708,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2484,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1706,c_1708])).

cnf(c_2932,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_691,c_2484])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_699,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_34])).

cnf(c_700,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_699])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_702,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_700,c_33])).

cnf(c_1704,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2485,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1704,c_1708])).

cnf(c_2935,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_702,c_2485])).

cnf(c_17,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1710,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3033,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2932,c_1710])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_39,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_41,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1958,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1959,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1958])).

cnf(c_3540,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3033,c_39,c_41,c_1959])).

cnf(c_3541,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3540])).

cnf(c_3553,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2935,c_3541])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_36,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_20,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_28,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != X0
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_446,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_1961,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1962,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1961])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2088,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2249,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2088])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2250,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1117,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2004,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1117])).

cnf(c_2316,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(c_3566,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3553,c_36,c_38,c_30,c_446,c_1962,c_2249,c_2250,c_2316])).

cnf(c_3572,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2935,c_3566])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_211,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_1])).

cnf(c_212,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_211])).

cnf(c_1702,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_3625,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK1(sK4,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3572,c_1702])).

cnf(c_29,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1707,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5113,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3625,c_1707])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1711,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5192,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5113,c_1711])).

cnf(c_5193,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5192])).

cnf(c_5195,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5192,c_35,c_33,c_32,c_30,c_446,c_1958,c_1961,c_2249,c_2250,c_2316,c_5193])).

cnf(c_5199,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2932,c_5195])).

cnf(c_5270,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5199,c_2935])).

cnf(c_5300,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5270,c_1706])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_5306,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5300,c_5])).

cnf(c_5301,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5270,c_1704])).

cnf(c_5303,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5301,c_5])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_4221,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4222,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4221])).

cnf(c_4224,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4222])).

cnf(c_3613,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3614,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3613])).

cnf(c_3616,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3614])).

cnf(c_12,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2826,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2829,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2826])).

cnf(c_2799,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2802,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2799])).

cnf(c_2262,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2263,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2262])).

cnf(c_2265,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2263])).

cnf(c_2244,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2245,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2244])).

cnf(c_2247,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2245])).

cnf(c_2233,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5))
    | r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2234,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(X0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2233])).

cnf(c_2236,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2234])).

cnf(c_2176,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2177,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2176])).

cnf(c_2179,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2177])).

cnf(c_2005,plain,
    ( sK5 != k1_xboole_0
    | sK4 = sK5
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5306,c_5303,c_4224,c_3616,c_2829,c_2802,c_2265,c_2247,c_2236,c_2179,c_2005,c_446,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.79/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/0.99  
% 2.79/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.79/0.99  
% 2.79/0.99  ------  iProver source info
% 2.79/0.99  
% 2.79/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.79/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.79/0.99  git: non_committed_changes: false
% 2.79/0.99  git: last_make_outside_of_git: false
% 2.79/0.99  
% 2.79/0.99  ------ 
% 2.79/0.99  
% 2.79/0.99  ------ Input Options
% 2.79/0.99  
% 2.79/0.99  --out_options                           all
% 2.79/0.99  --tptp_safe_out                         true
% 2.79/0.99  --problem_path                          ""
% 2.79/0.99  --include_path                          ""
% 2.79/0.99  --clausifier                            res/vclausify_rel
% 2.79/0.99  --clausifier_options                    --mode clausify
% 2.79/0.99  --stdin                                 false
% 2.79/0.99  --stats_out                             all
% 2.79/0.99  
% 2.79/0.99  ------ General Options
% 2.79/0.99  
% 2.79/0.99  --fof                                   false
% 2.79/0.99  --time_out_real                         305.
% 2.79/0.99  --time_out_virtual                      -1.
% 2.79/0.99  --symbol_type_check                     false
% 2.79/0.99  --clausify_out                          false
% 2.79/0.99  --sig_cnt_out                           false
% 2.79/0.99  --trig_cnt_out                          false
% 2.79/0.99  --trig_cnt_out_tolerance                1.
% 2.79/0.99  --trig_cnt_out_sk_spl                   false
% 2.79/0.99  --abstr_cl_out                          false
% 2.79/0.99  
% 2.79/0.99  ------ Global Options
% 2.79/0.99  
% 2.79/0.99  --schedule                              default
% 2.79/0.99  --add_important_lit                     false
% 2.79/0.99  --prop_solver_per_cl                    1000
% 2.79/0.99  --min_unsat_core                        false
% 2.79/0.99  --soft_assumptions                      false
% 2.79/0.99  --soft_lemma_size                       3
% 2.79/0.99  --prop_impl_unit_size                   0
% 2.79/0.99  --prop_impl_unit                        []
% 2.79/0.99  --share_sel_clauses                     true
% 2.79/0.99  --reset_solvers                         false
% 2.79/0.99  --bc_imp_inh                            [conj_cone]
% 2.79/0.99  --conj_cone_tolerance                   3.
% 2.79/0.99  --extra_neg_conj                        none
% 2.79/0.99  --large_theory_mode                     true
% 2.79/0.99  --prolific_symb_bound                   200
% 2.79/0.99  --lt_threshold                          2000
% 2.79/0.99  --clause_weak_htbl                      true
% 2.79/0.99  --gc_record_bc_elim                     false
% 2.79/0.99  
% 2.79/0.99  ------ Preprocessing Options
% 2.79/0.99  
% 2.79/0.99  --preprocessing_flag                    true
% 2.79/0.99  --time_out_prep_mult                    0.1
% 2.79/0.99  --splitting_mode                        input
% 2.79/0.99  --splitting_grd                         true
% 2.79/0.99  --splitting_cvd                         false
% 2.79/0.99  --splitting_cvd_svl                     false
% 2.79/0.99  --splitting_nvd                         32
% 2.79/0.99  --sub_typing                            true
% 2.79/0.99  --prep_gs_sim                           true
% 2.79/0.99  --prep_unflatten                        true
% 2.79/0.99  --prep_res_sim                          true
% 2.79/0.99  --prep_upred                            true
% 2.79/0.99  --prep_sem_filter                       exhaustive
% 2.79/0.99  --prep_sem_filter_out                   false
% 2.79/0.99  --pred_elim                             true
% 2.79/0.99  --res_sim_input                         true
% 2.79/0.99  --eq_ax_congr_red                       true
% 2.79/0.99  --pure_diseq_elim                       true
% 2.79/0.99  --brand_transform                       false
% 2.79/0.99  --non_eq_to_eq                          false
% 2.79/0.99  --prep_def_merge                        true
% 2.79/0.99  --prep_def_merge_prop_impl              false
% 2.79/0.99  --prep_def_merge_mbd                    true
% 2.79/0.99  --prep_def_merge_tr_red                 false
% 2.79/0.99  --prep_def_merge_tr_cl                  false
% 2.79/0.99  --smt_preprocessing                     true
% 2.79/0.99  --smt_ac_axioms                         fast
% 2.79/0.99  --preprocessed_out                      false
% 2.79/0.99  --preprocessed_stats                    false
% 2.79/0.99  
% 2.79/0.99  ------ Abstraction refinement Options
% 2.79/0.99  
% 2.79/0.99  --abstr_ref                             []
% 2.79/0.99  --abstr_ref_prep                        false
% 2.79/0.99  --abstr_ref_until_sat                   false
% 2.79/0.99  --abstr_ref_sig_restrict                funpre
% 2.79/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/0.99  --abstr_ref_under                       []
% 2.79/0.99  
% 2.79/0.99  ------ SAT Options
% 2.79/0.99  
% 2.79/0.99  --sat_mode                              false
% 2.79/0.99  --sat_fm_restart_options                ""
% 2.79/0.99  --sat_gr_def                            false
% 2.79/0.99  --sat_epr_types                         true
% 2.79/0.99  --sat_non_cyclic_types                  false
% 2.79/0.99  --sat_finite_models                     false
% 2.79/0.99  --sat_fm_lemmas                         false
% 2.79/0.99  --sat_fm_prep                           false
% 2.79/0.99  --sat_fm_uc_incr                        true
% 2.79/0.99  --sat_out_model                         small
% 2.79/0.99  --sat_out_clauses                       false
% 2.79/0.99  
% 2.79/0.99  ------ QBF Options
% 2.79/0.99  
% 2.79/0.99  --qbf_mode                              false
% 2.79/0.99  --qbf_elim_univ                         false
% 2.79/0.99  --qbf_dom_inst                          none
% 2.79/0.99  --qbf_dom_pre_inst                      false
% 2.79/0.99  --qbf_sk_in                             false
% 2.79/0.99  --qbf_pred_elim                         true
% 2.79/0.99  --qbf_split                             512
% 2.79/0.99  
% 2.79/0.99  ------ BMC1 Options
% 2.79/0.99  
% 2.79/0.99  --bmc1_incremental                      false
% 2.79/0.99  --bmc1_axioms                           reachable_all
% 2.79/0.99  --bmc1_min_bound                        0
% 2.79/0.99  --bmc1_max_bound                        -1
% 2.79/0.99  --bmc1_max_bound_default                -1
% 2.79/0.99  --bmc1_symbol_reachability              true
% 2.79/0.99  --bmc1_property_lemmas                  false
% 2.79/0.99  --bmc1_k_induction                      false
% 2.79/0.99  --bmc1_non_equiv_states                 false
% 2.79/0.99  --bmc1_deadlock                         false
% 2.79/0.99  --bmc1_ucm                              false
% 2.79/0.99  --bmc1_add_unsat_core                   none
% 2.79/0.99  --bmc1_unsat_core_children              false
% 2.79/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/0.99  --bmc1_out_stat                         full
% 2.79/0.99  --bmc1_ground_init                      false
% 2.79/0.99  --bmc1_pre_inst_next_state              false
% 2.79/0.99  --bmc1_pre_inst_state                   false
% 2.79/0.99  --bmc1_pre_inst_reach_state             false
% 2.79/0.99  --bmc1_out_unsat_core                   false
% 2.79/0.99  --bmc1_aig_witness_out                  false
% 2.79/0.99  --bmc1_verbose                          false
% 2.79/0.99  --bmc1_dump_clauses_tptp                false
% 2.79/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.79/0.99  --bmc1_dump_file                        -
% 2.79/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.79/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.79/0.99  --bmc1_ucm_extend_mode                  1
% 2.79/0.99  --bmc1_ucm_init_mode                    2
% 2.79/0.99  --bmc1_ucm_cone_mode                    none
% 2.79/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.79/0.99  --bmc1_ucm_relax_model                  4
% 2.79/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.79/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/0.99  --bmc1_ucm_layered_model                none
% 2.79/0.99  --bmc1_ucm_max_lemma_size               10
% 2.79/0.99  
% 2.79/0.99  ------ AIG Options
% 2.79/0.99  
% 2.79/0.99  --aig_mode                              false
% 2.79/0.99  
% 2.79/0.99  ------ Instantiation Options
% 2.79/0.99  
% 2.79/0.99  --instantiation_flag                    true
% 2.79/0.99  --inst_sos_flag                         false
% 2.79/0.99  --inst_sos_phase                        true
% 2.79/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/0.99  --inst_lit_sel_side                     num_symb
% 2.79/0.99  --inst_solver_per_active                1400
% 2.79/0.99  --inst_solver_calls_frac                1.
% 2.79/0.99  --inst_passive_queue_type               priority_queues
% 2.79/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/0.99  --inst_passive_queues_freq              [25;2]
% 2.79/0.99  --inst_dismatching                      true
% 2.79/0.99  --inst_eager_unprocessed_to_passive     true
% 2.79/0.99  --inst_prop_sim_given                   true
% 2.79/0.99  --inst_prop_sim_new                     false
% 2.79/0.99  --inst_subs_new                         false
% 2.79/0.99  --inst_eq_res_simp                      false
% 2.79/0.99  --inst_subs_given                       false
% 2.79/0.99  --inst_orphan_elimination               true
% 2.79/0.99  --inst_learning_loop_flag               true
% 2.79/0.99  --inst_learning_start                   3000
% 2.79/0.99  --inst_learning_factor                  2
% 2.79/0.99  --inst_start_prop_sim_after_learn       3
% 2.79/0.99  --inst_sel_renew                        solver
% 2.79/0.99  --inst_lit_activity_flag                true
% 2.79/0.99  --inst_restr_to_given                   false
% 2.79/0.99  --inst_activity_threshold               500
% 2.79/0.99  --inst_out_proof                        true
% 2.79/0.99  
% 2.79/0.99  ------ Resolution Options
% 2.79/0.99  
% 2.79/0.99  --resolution_flag                       true
% 2.79/0.99  --res_lit_sel                           adaptive
% 2.79/0.99  --res_lit_sel_side                      none
% 2.79/0.99  --res_ordering                          kbo
% 2.79/0.99  --res_to_prop_solver                    active
% 2.79/0.99  --res_prop_simpl_new                    false
% 2.79/0.99  --res_prop_simpl_given                  true
% 2.79/0.99  --res_passive_queue_type                priority_queues
% 2.79/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/0.99  --res_passive_queues_freq               [15;5]
% 2.79/0.99  --res_forward_subs                      full
% 2.79/0.99  --res_backward_subs                     full
% 2.79/0.99  --res_forward_subs_resolution           true
% 2.79/0.99  --res_backward_subs_resolution          true
% 2.79/0.99  --res_orphan_elimination                true
% 2.79/0.99  --res_time_limit                        2.
% 2.79/0.99  --res_out_proof                         true
% 2.79/0.99  
% 2.79/0.99  ------ Superposition Options
% 2.79/0.99  
% 2.79/0.99  --superposition_flag                    true
% 2.79/0.99  --sup_passive_queue_type                priority_queues
% 2.79/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.79/0.99  --demod_completeness_check              fast
% 2.79/0.99  --demod_use_ground                      true
% 2.79/0.99  --sup_to_prop_solver                    passive
% 2.79/0.99  --sup_prop_simpl_new                    true
% 2.79/0.99  --sup_prop_simpl_given                  true
% 2.79/0.99  --sup_fun_splitting                     false
% 2.79/0.99  --sup_smt_interval                      50000
% 2.79/0.99  
% 2.79/0.99  ------ Superposition Simplification Setup
% 2.79/0.99  
% 2.79/0.99  --sup_indices_passive                   []
% 2.79/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.99  --sup_full_bw                           [BwDemod]
% 2.79/0.99  --sup_immed_triv                        [TrivRules]
% 2.79/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.99  --sup_immed_bw_main                     []
% 2.79/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.99  
% 2.79/0.99  ------ Combination Options
% 2.79/0.99  
% 2.79/0.99  --comb_res_mult                         3
% 2.79/0.99  --comb_sup_mult                         2
% 2.79/0.99  --comb_inst_mult                        10
% 2.79/0.99  
% 2.79/0.99  ------ Debug Options
% 2.79/0.99  
% 2.79/0.99  --dbg_backtrace                         false
% 2.79/0.99  --dbg_dump_prop_clauses                 false
% 2.79/0.99  --dbg_dump_prop_clauses_file            -
% 2.79/0.99  --dbg_out_stat                          false
% 2.79/0.99  ------ Parsing...
% 2.79/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.79/0.99  
% 2.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.79/0.99  
% 2.79/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.79/0.99  
% 2.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.79/0.99  ------ Proving...
% 2.79/0.99  ------ Problem Properties 
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  clauses                                 31
% 2.79/0.99  conjectures                             5
% 2.79/0.99  EPR                                     10
% 2.79/0.99  Horn                                    23
% 2.79/0.99  unary                                   9
% 2.79/0.99  binary                                  10
% 2.79/0.99  lits                                    75
% 2.79/0.99  lits eq                                 28
% 2.79/0.99  fd_pure                                 0
% 2.79/0.99  fd_pseudo                               0
% 2.79/0.99  fd_cond                                 1
% 2.79/0.99  fd_pseudo_cond                          3
% 2.79/0.99  AC symbols                              0
% 2.79/0.99  
% 2.79/0.99  ------ Schedule dynamic 5 is on 
% 2.79/0.99  
% 2.79/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  ------ 
% 2.79/0.99  Current options:
% 2.79/0.99  ------ 
% 2.79/0.99  
% 2.79/0.99  ------ Input Options
% 2.79/0.99  
% 2.79/0.99  --out_options                           all
% 2.79/0.99  --tptp_safe_out                         true
% 2.79/0.99  --problem_path                          ""
% 2.79/0.99  --include_path                          ""
% 2.79/0.99  --clausifier                            res/vclausify_rel
% 2.79/0.99  --clausifier_options                    --mode clausify
% 2.79/0.99  --stdin                                 false
% 2.79/0.99  --stats_out                             all
% 2.79/0.99  
% 2.79/0.99  ------ General Options
% 2.79/0.99  
% 2.79/0.99  --fof                                   false
% 2.79/0.99  --time_out_real                         305.
% 2.79/0.99  --time_out_virtual                      -1.
% 2.79/0.99  --symbol_type_check                     false
% 2.79/0.99  --clausify_out                          false
% 2.79/0.99  --sig_cnt_out                           false
% 2.79/0.99  --trig_cnt_out                          false
% 2.79/0.99  --trig_cnt_out_tolerance                1.
% 2.79/0.99  --trig_cnt_out_sk_spl                   false
% 2.79/0.99  --abstr_cl_out                          false
% 2.79/0.99  
% 2.79/0.99  ------ Global Options
% 2.79/0.99  
% 2.79/0.99  --schedule                              default
% 2.79/0.99  --add_important_lit                     false
% 2.79/0.99  --prop_solver_per_cl                    1000
% 2.79/0.99  --min_unsat_core                        false
% 2.79/0.99  --soft_assumptions                      false
% 2.79/0.99  --soft_lemma_size                       3
% 2.79/0.99  --prop_impl_unit_size                   0
% 2.79/0.99  --prop_impl_unit                        []
% 2.79/0.99  --share_sel_clauses                     true
% 2.79/0.99  --reset_solvers                         false
% 2.79/0.99  --bc_imp_inh                            [conj_cone]
% 2.79/0.99  --conj_cone_tolerance                   3.
% 2.79/0.99  --extra_neg_conj                        none
% 2.79/0.99  --large_theory_mode                     true
% 2.79/0.99  --prolific_symb_bound                   200
% 2.79/0.99  --lt_threshold                          2000
% 2.79/0.99  --clause_weak_htbl                      true
% 2.79/0.99  --gc_record_bc_elim                     false
% 2.79/0.99  
% 2.79/0.99  ------ Preprocessing Options
% 2.79/0.99  
% 2.79/0.99  --preprocessing_flag                    true
% 2.79/0.99  --time_out_prep_mult                    0.1
% 2.79/0.99  --splitting_mode                        input
% 2.79/0.99  --splitting_grd                         true
% 2.79/0.99  --splitting_cvd                         false
% 2.79/0.99  --splitting_cvd_svl                     false
% 2.79/0.99  --splitting_nvd                         32
% 2.79/0.99  --sub_typing                            true
% 2.79/0.99  --prep_gs_sim                           true
% 2.79/0.99  --prep_unflatten                        true
% 2.79/0.99  --prep_res_sim                          true
% 2.79/0.99  --prep_upred                            true
% 2.79/0.99  --prep_sem_filter                       exhaustive
% 2.79/0.99  --prep_sem_filter_out                   false
% 2.79/0.99  --pred_elim                             true
% 2.79/0.99  --res_sim_input                         true
% 2.79/0.99  --eq_ax_congr_red                       true
% 2.79/0.99  --pure_diseq_elim                       true
% 2.79/0.99  --brand_transform                       false
% 2.79/0.99  --non_eq_to_eq                          false
% 2.79/0.99  --prep_def_merge                        true
% 2.79/0.99  --prep_def_merge_prop_impl              false
% 2.79/0.99  --prep_def_merge_mbd                    true
% 2.79/0.99  --prep_def_merge_tr_red                 false
% 2.79/0.99  --prep_def_merge_tr_cl                  false
% 2.79/0.99  --smt_preprocessing                     true
% 2.79/0.99  --smt_ac_axioms                         fast
% 2.79/0.99  --preprocessed_out                      false
% 2.79/0.99  --preprocessed_stats                    false
% 2.79/0.99  
% 2.79/0.99  ------ Abstraction refinement Options
% 2.79/0.99  
% 2.79/0.99  --abstr_ref                             []
% 2.79/0.99  --abstr_ref_prep                        false
% 2.79/0.99  --abstr_ref_until_sat                   false
% 2.79/0.99  --abstr_ref_sig_restrict                funpre
% 2.79/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/0.99  --abstr_ref_under                       []
% 2.79/0.99  
% 2.79/0.99  ------ SAT Options
% 2.79/0.99  
% 2.79/0.99  --sat_mode                              false
% 2.79/0.99  --sat_fm_restart_options                ""
% 2.79/0.99  --sat_gr_def                            false
% 2.79/0.99  --sat_epr_types                         true
% 2.79/0.99  --sat_non_cyclic_types                  false
% 2.79/0.99  --sat_finite_models                     false
% 2.79/0.99  --sat_fm_lemmas                         false
% 2.79/0.99  --sat_fm_prep                           false
% 2.79/0.99  --sat_fm_uc_incr                        true
% 2.79/0.99  --sat_out_model                         small
% 2.79/0.99  --sat_out_clauses                       false
% 2.79/0.99  
% 2.79/0.99  ------ QBF Options
% 2.79/0.99  
% 2.79/0.99  --qbf_mode                              false
% 2.79/0.99  --qbf_elim_univ                         false
% 2.79/0.99  --qbf_dom_inst                          none
% 2.79/0.99  --qbf_dom_pre_inst                      false
% 2.79/0.99  --qbf_sk_in                             false
% 2.79/0.99  --qbf_pred_elim                         true
% 2.79/0.99  --qbf_split                             512
% 2.79/0.99  
% 2.79/0.99  ------ BMC1 Options
% 2.79/0.99  
% 2.79/0.99  --bmc1_incremental                      false
% 2.79/0.99  --bmc1_axioms                           reachable_all
% 2.79/0.99  --bmc1_min_bound                        0
% 2.79/0.99  --bmc1_max_bound                        -1
% 2.79/0.99  --bmc1_max_bound_default                -1
% 2.79/0.99  --bmc1_symbol_reachability              true
% 2.79/0.99  --bmc1_property_lemmas                  false
% 2.79/0.99  --bmc1_k_induction                      false
% 2.79/0.99  --bmc1_non_equiv_states                 false
% 2.79/0.99  --bmc1_deadlock                         false
% 2.79/0.99  --bmc1_ucm                              false
% 2.79/0.99  --bmc1_add_unsat_core                   none
% 2.79/0.99  --bmc1_unsat_core_children              false
% 2.79/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/0.99  --bmc1_out_stat                         full
% 2.79/0.99  --bmc1_ground_init                      false
% 2.79/0.99  --bmc1_pre_inst_next_state              false
% 2.79/0.99  --bmc1_pre_inst_state                   false
% 2.79/0.99  --bmc1_pre_inst_reach_state             false
% 2.79/0.99  --bmc1_out_unsat_core                   false
% 2.79/0.99  --bmc1_aig_witness_out                  false
% 2.79/0.99  --bmc1_verbose                          false
% 2.79/0.99  --bmc1_dump_clauses_tptp                false
% 2.79/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.79/0.99  --bmc1_dump_file                        -
% 2.79/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.79/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.79/0.99  --bmc1_ucm_extend_mode                  1
% 2.79/0.99  --bmc1_ucm_init_mode                    2
% 2.79/0.99  --bmc1_ucm_cone_mode                    none
% 2.79/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.79/0.99  --bmc1_ucm_relax_model                  4
% 2.79/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.79/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/0.99  --bmc1_ucm_layered_model                none
% 2.79/0.99  --bmc1_ucm_max_lemma_size               10
% 2.79/0.99  
% 2.79/0.99  ------ AIG Options
% 2.79/0.99  
% 2.79/0.99  --aig_mode                              false
% 2.79/0.99  
% 2.79/0.99  ------ Instantiation Options
% 2.79/0.99  
% 2.79/0.99  --instantiation_flag                    true
% 2.79/0.99  --inst_sos_flag                         false
% 2.79/0.99  --inst_sos_phase                        true
% 2.79/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/0.99  --inst_lit_sel_side                     none
% 2.79/0.99  --inst_solver_per_active                1400
% 2.79/0.99  --inst_solver_calls_frac                1.
% 2.79/0.99  --inst_passive_queue_type               priority_queues
% 2.79/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/0.99  --inst_passive_queues_freq              [25;2]
% 2.79/0.99  --inst_dismatching                      true
% 2.79/0.99  --inst_eager_unprocessed_to_passive     true
% 2.79/0.99  --inst_prop_sim_given                   true
% 2.79/0.99  --inst_prop_sim_new                     false
% 2.79/0.99  --inst_subs_new                         false
% 2.79/0.99  --inst_eq_res_simp                      false
% 2.79/0.99  --inst_subs_given                       false
% 2.79/0.99  --inst_orphan_elimination               true
% 2.79/0.99  --inst_learning_loop_flag               true
% 2.79/0.99  --inst_learning_start                   3000
% 2.79/0.99  --inst_learning_factor                  2
% 2.79/0.99  --inst_start_prop_sim_after_learn       3
% 2.79/0.99  --inst_sel_renew                        solver
% 2.79/0.99  --inst_lit_activity_flag                true
% 2.79/0.99  --inst_restr_to_given                   false
% 2.79/0.99  --inst_activity_threshold               500
% 2.79/0.99  --inst_out_proof                        true
% 2.79/0.99  
% 2.79/0.99  ------ Resolution Options
% 2.79/0.99  
% 2.79/0.99  --resolution_flag                       false
% 2.79/0.99  --res_lit_sel                           adaptive
% 2.79/0.99  --res_lit_sel_side                      none
% 2.79/0.99  --res_ordering                          kbo
% 2.79/0.99  --res_to_prop_solver                    active
% 2.79/0.99  --res_prop_simpl_new                    false
% 2.79/0.99  --res_prop_simpl_given                  true
% 2.79/0.99  --res_passive_queue_type                priority_queues
% 2.79/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/0.99  --res_passive_queues_freq               [15;5]
% 2.79/0.99  --res_forward_subs                      full
% 2.79/0.99  --res_backward_subs                     full
% 2.79/0.99  --res_forward_subs_resolution           true
% 2.79/0.99  --res_backward_subs_resolution          true
% 2.79/0.99  --res_orphan_elimination                true
% 2.79/0.99  --res_time_limit                        2.
% 2.79/0.99  --res_out_proof                         true
% 2.79/0.99  
% 2.79/0.99  ------ Superposition Options
% 2.79/0.99  
% 2.79/0.99  --superposition_flag                    true
% 2.79/0.99  --sup_passive_queue_type                priority_queues
% 2.79/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.79/0.99  --demod_completeness_check              fast
% 2.79/0.99  --demod_use_ground                      true
% 2.79/0.99  --sup_to_prop_solver                    passive
% 2.79/0.99  --sup_prop_simpl_new                    true
% 2.79/0.99  --sup_prop_simpl_given                  true
% 2.79/0.99  --sup_fun_splitting                     false
% 2.79/0.99  --sup_smt_interval                      50000
% 2.79/0.99  
% 2.79/0.99  ------ Superposition Simplification Setup
% 2.79/0.99  
% 2.79/0.99  --sup_indices_passive                   []
% 2.79/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.99  --sup_full_bw                           [BwDemod]
% 2.79/0.99  --sup_immed_triv                        [TrivRules]
% 2.79/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.99  --sup_immed_bw_main                     []
% 2.79/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.99  
% 2.79/0.99  ------ Combination Options
% 2.79/0.99  
% 2.79/0.99  --comb_res_mult                         3
% 2.79/0.99  --comb_sup_mult                         2
% 2.79/0.99  --comb_inst_mult                        10
% 2.79/0.99  
% 2.79/0.99  ------ Debug Options
% 2.79/0.99  
% 2.79/0.99  --dbg_backtrace                         false
% 2.79/0.99  --dbg_dump_prop_clauses                 false
% 2.79/0.99  --dbg_dump_prop_clauses_file            -
% 2.79/0.99  --dbg_out_stat                          false
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  ------ Proving...
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  % SZS status Theorem for theBenchmark.p
% 2.79/0.99  
% 2.79/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.79/0.99  
% 2.79/0.99  fof(f12,axiom,(
% 2.79/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f24,plain,(
% 2.79/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.79/0.99    inference(ennf_transformation,[],[f12])).
% 2.79/0.99  
% 2.79/0.99  fof(f25,plain,(
% 2.79/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.79/0.99    inference(flattening,[],[f24])).
% 2.79/0.99  
% 2.79/0.99  fof(f41,plain,(
% 2.79/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.79/0.99    inference(nnf_transformation,[],[f25])).
% 2.79/0.99  
% 2.79/0.99  fof(f67,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.79/0.99    inference(cnf_transformation,[],[f41])).
% 2.79/0.99  
% 2.79/0.99  fof(f13,conjecture,(
% 2.79/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f14,negated_conjecture,(
% 2.79/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.79/0.99    inference(negated_conjecture,[],[f13])).
% 2.79/0.99  
% 2.79/0.99  fof(f26,plain,(
% 2.79/0.99    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.79/0.99    inference(ennf_transformation,[],[f14])).
% 2.79/0.99  
% 2.79/0.99  fof(f27,plain,(
% 2.79/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.79/0.99    inference(flattening,[],[f26])).
% 2.79/0.99  
% 2.79/0.99  fof(f43,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK5) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X2,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 2.79/0.99    introduced(choice_axiom,[])).
% 2.79/0.99  
% 2.79/0.99  fof(f42,plain,(
% 2.79/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.79/0.99    introduced(choice_axiom,[])).
% 2.79/0.99  
% 2.79/0.99  fof(f44,plain,(
% 2.79/0.99    (~r2_relset_1(sK2,sK3,sK4,sK5) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f43,f42])).
% 2.79/0.99  
% 2.79/0.99  fof(f77,plain,(
% 2.79/0.99    v1_funct_2(sK5,sK2,sK3)),
% 2.79/0.99    inference(cnf_transformation,[],[f44])).
% 2.79/0.99  
% 2.79/0.99  fof(f78,plain,(
% 2.79/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.79/0.99    inference(cnf_transformation,[],[f44])).
% 2.79/0.99  
% 2.79/0.99  fof(f10,axiom,(
% 2.79/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f21,plain,(
% 2.79/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.79/0.99    inference(ennf_transformation,[],[f10])).
% 2.79/0.99  
% 2.79/0.99  fof(f64,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.79/0.99    inference(cnf_transformation,[],[f21])).
% 2.79/0.99  
% 2.79/0.99  fof(f74,plain,(
% 2.79/0.99    v1_funct_2(sK4,sK2,sK3)),
% 2.79/0.99    inference(cnf_transformation,[],[f44])).
% 2.79/0.99  
% 2.79/0.99  fof(f75,plain,(
% 2.79/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.79/0.99    inference(cnf_transformation,[],[f44])).
% 2.79/0.99  
% 2.79/0.99  fof(f8,axiom,(
% 2.79/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f18,plain,(
% 2.79/0.99    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.79/0.99    inference(ennf_transformation,[],[f8])).
% 2.79/0.99  
% 2.79/0.99  fof(f19,plain,(
% 2.79/0.99    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.79/0.99    inference(flattening,[],[f18])).
% 2.79/0.99  
% 2.79/0.99  fof(f38,plain,(
% 2.79/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 2.79/0.99    introduced(choice_axiom,[])).
% 2.79/0.99  
% 2.79/0.99  fof(f39,plain,(
% 2.79/0.99    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f38])).
% 2.79/0.99  
% 2.79/0.99  fof(f61,plain,(
% 2.79/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f39])).
% 2.79/0.99  
% 2.79/0.99  fof(f76,plain,(
% 2.79/0.99    v1_funct_1(sK5)),
% 2.79/0.99    inference(cnf_transformation,[],[f44])).
% 2.79/0.99  
% 2.79/0.99  fof(f9,axiom,(
% 2.79/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f20,plain,(
% 2.79/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.79/0.99    inference(ennf_transformation,[],[f9])).
% 2.79/0.99  
% 2.79/0.99  fof(f63,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.79/0.99    inference(cnf_transformation,[],[f20])).
% 2.79/0.99  
% 2.79/0.99  fof(f73,plain,(
% 2.79/0.99    v1_funct_1(sK4)),
% 2.79/0.99    inference(cnf_transformation,[],[f44])).
% 2.79/0.99  
% 2.79/0.99  fof(f11,axiom,(
% 2.79/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f22,plain,(
% 2.79/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.79/0.99    inference(ennf_transformation,[],[f11])).
% 2.79/0.99  
% 2.79/0.99  fof(f23,plain,(
% 2.79/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.79/0.99    inference(flattening,[],[f22])).
% 2.79/0.99  
% 2.79/0.99  fof(f40,plain,(
% 2.79/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.79/0.99    inference(nnf_transformation,[],[f23])).
% 2.79/0.99  
% 2.79/0.99  fof(f66,plain,(
% 2.79/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.79/0.99    inference(cnf_transformation,[],[f40])).
% 2.79/0.99  
% 2.79/0.99  fof(f85,plain,(
% 2.79/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.79/0.99    inference(equality_resolution,[],[f66])).
% 2.79/0.99  
% 2.79/0.99  fof(f80,plain,(
% 2.79/0.99    ~r2_relset_1(sK2,sK3,sK4,sK5)),
% 2.79/0.99    inference(cnf_transformation,[],[f44])).
% 2.79/0.99  
% 2.79/0.99  fof(f2,axiom,(
% 2.79/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f32,plain,(
% 2.79/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.79/0.99    inference(nnf_transformation,[],[f2])).
% 2.79/0.99  
% 2.79/0.99  fof(f33,plain,(
% 2.79/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.79/0.99    inference(flattening,[],[f32])).
% 2.79/0.99  
% 2.79/0.99  fof(f49,plain,(
% 2.79/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f33])).
% 2.79/0.99  
% 2.79/0.99  fof(f47,plain,(
% 2.79/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.79/0.99    inference(cnf_transformation,[],[f33])).
% 2.79/0.99  
% 2.79/0.99  fof(f82,plain,(
% 2.79/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.79/0.99    inference(equality_resolution,[],[f47])).
% 2.79/0.99  
% 2.79/0.99  fof(f4,axiom,(
% 2.79/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f15,plain,(
% 2.79/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.79/0.99    inference(ennf_transformation,[],[f4])).
% 2.79/0.99  
% 2.79/0.99  fof(f36,plain,(
% 2.79/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.79/0.99    inference(nnf_transformation,[],[f15])).
% 2.79/0.99  
% 2.79/0.99  fof(f54,plain,(
% 2.79/0.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f36])).
% 2.79/0.99  
% 2.79/0.99  fof(f1,axiom,(
% 2.79/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f28,plain,(
% 2.79/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.79/0.99    inference(nnf_transformation,[],[f1])).
% 2.79/0.99  
% 2.79/0.99  fof(f29,plain,(
% 2.79/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.79/0.99    inference(rectify,[],[f28])).
% 2.79/0.99  
% 2.79/0.99  fof(f30,plain,(
% 2.79/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.79/0.99    introduced(choice_axiom,[])).
% 2.79/0.99  
% 2.79/0.99  fof(f31,plain,(
% 2.79/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 2.79/0.99  
% 2.79/0.99  fof(f45,plain,(
% 2.79/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f31])).
% 2.79/0.99  
% 2.79/0.99  fof(f79,plain,(
% 2.79/0.99    ( ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK2)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f44])).
% 2.79/0.99  
% 2.79/0.99  fof(f62,plain,(
% 2.79/0.99    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f39])).
% 2.79/0.99  
% 2.79/0.99  fof(f3,axiom,(
% 2.79/0.99    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f34,plain,(
% 2.79/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.79/0.99    inference(nnf_transformation,[],[f3])).
% 2.79/0.99  
% 2.79/0.99  fof(f35,plain,(
% 2.79/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.79/0.99    inference(flattening,[],[f34])).
% 2.79/0.99  
% 2.79/0.99  fof(f52,plain,(
% 2.79/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.79/0.99    inference(cnf_transformation,[],[f35])).
% 2.79/0.99  
% 2.79/0.99  fof(f83,plain,(
% 2.79/0.99    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.79/0.99    inference(equality_resolution,[],[f52])).
% 2.79/0.99  
% 2.79/0.99  fof(f6,axiom,(
% 2.79/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f37,plain,(
% 2.79/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.79/0.99    inference(nnf_transformation,[],[f6])).
% 2.79/0.99  
% 2.79/0.99  fof(f58,plain,(
% 2.79/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.79/0.99    inference(cnf_transformation,[],[f37])).
% 2.79/0.99  
% 2.79/0.99  fof(f5,axiom,(
% 2.79/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f57,plain,(
% 2.79/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.79/0.99    inference(cnf_transformation,[],[f5])).
% 2.79/0.99  
% 2.79/0.99  cnf(c_27,plain,
% 2.79/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.79/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.79/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.79/0.99      | k1_xboole_0 = X2 ),
% 2.79/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_31,negated_conjecture,
% 2.79/0.99      ( v1_funct_2(sK5,sK2,sK3) ),
% 2.79/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_688,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.79/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.79/0.99      | sK5 != X0
% 2.79/0.99      | sK3 != X2
% 2.79/0.99      | sK2 != X1
% 2.79/0.99      | k1_xboole_0 = X2 ),
% 2.79/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_689,plain,
% 2.79/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.79/0.99      | k1_relset_1(sK2,sK3,sK5) = sK2
% 2.79/0.99      | k1_xboole_0 = sK3 ),
% 2.79/0.99      inference(unflattening,[status(thm)],[c_688]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_30,negated_conjecture,
% 2.79/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.79/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_691,plain,
% 2.79/0.99      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_689,c_30]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1706,plain,
% 2.79/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_19,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.79/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1708,plain,
% 2.79/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.79/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2484,plain,
% 2.79/0.99      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_1706,c_1708]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2932,plain,
% 2.79/0.99      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_691,c_2484]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_34,negated_conjecture,
% 2.79/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.79/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_699,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.79/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.79/0.99      | sK4 != X0
% 2.79/0.99      | sK3 != X2
% 2.79/0.99      | sK2 != X1
% 2.79/0.99      | k1_xboole_0 = X2 ),
% 2.79/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_34]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_700,plain,
% 2.79/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.79/0.99      | k1_relset_1(sK2,sK3,sK4) = sK2
% 2.79/0.99      | k1_xboole_0 = sK3 ),
% 2.79/0.99      inference(unflattening,[status(thm)],[c_699]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_33,negated_conjecture,
% 2.79/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.79/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_702,plain,
% 2.79/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_700,c_33]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1704,plain,
% 2.79/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2485,plain,
% 2.79/0.99      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_1704,c_1708]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2935,plain,
% 2.79/0.99      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_702,c_2485]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_17,plain,
% 2.79/0.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 2.79/0.99      | ~ v1_relat_1(X1)
% 2.79/0.99      | ~ v1_relat_1(X0)
% 2.79/0.99      | ~ v1_funct_1(X1)
% 2.79/0.99      | ~ v1_funct_1(X0)
% 2.79/0.99      | X1 = X0
% 2.79/0.99      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1710,plain,
% 2.79/0.99      ( X0 = X1
% 2.79/0.99      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.79/0.99      | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
% 2.79/0.99      | v1_relat_1(X1) != iProver_top
% 2.79/0.99      | v1_relat_1(X0) != iProver_top
% 2.79/0.99      | v1_funct_1(X0) != iProver_top
% 2.79/0.99      | v1_funct_1(X1) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3033,plain,
% 2.79/0.99      ( k1_relat_1(X0) != sK2
% 2.79/0.99      | sK5 = X0
% 2.79/0.99      | sK3 = k1_xboole_0
% 2.79/0.99      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.79/0.99      | v1_relat_1(X0) != iProver_top
% 2.79/0.99      | v1_relat_1(sK5) != iProver_top
% 2.79/0.99      | v1_funct_1(X0) != iProver_top
% 2.79/0.99      | v1_funct_1(sK5) != iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_2932,c_1710]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_32,negated_conjecture,
% 2.79/0.99      ( v1_funct_1(sK5) ),
% 2.79/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_39,plain,
% 2.79/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_41,plain,
% 2.79/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_18,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.79/0.99      | v1_relat_1(X0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1958,plain,
% 2.79/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.79/0.99      | v1_relat_1(sK5) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1959,plain,
% 2.79/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.79/0.99      | v1_relat_1(sK5) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_1958]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3540,plain,
% 2.79/0.99      ( v1_funct_1(X0) != iProver_top
% 2.79/0.99      | k1_relat_1(X0) != sK2
% 2.79/0.99      | sK5 = X0
% 2.79/0.99      | sK3 = k1_xboole_0
% 2.79/0.99      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_3033,c_39,c_41,c_1959]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3541,plain,
% 2.79/0.99      ( k1_relat_1(X0) != sK2
% 2.79/0.99      | sK5 = X0
% 2.79/0.99      | sK3 = k1_xboole_0
% 2.79/0.99      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 2.79/0.99      | v1_relat_1(X0) != iProver_top
% 2.79/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.79/0.99      inference(renaming,[status(thm)],[c_3540]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3553,plain,
% 2.79/0.99      ( sK5 = sK4
% 2.79/0.99      | sK3 = k1_xboole_0
% 2.79/0.99      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
% 2.79/0.99      | v1_relat_1(sK4) != iProver_top
% 2.79/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_2935,c_3541]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_35,negated_conjecture,
% 2.79/0.99      ( v1_funct_1(sK4) ),
% 2.79/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_36,plain,
% 2.79/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_38,plain,
% 2.79/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_20,plain,
% 2.79/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.79/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.79/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_28,negated_conjecture,
% 2.79/0.99      ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
% 2.79/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_445,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.79/0.99      | sK5 != X0
% 2.79/0.99      | sK4 != X0
% 2.79/0.99      | sK3 != X2
% 2.79/0.99      | sK2 != X1 ),
% 2.79/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_446,plain,
% 2.79/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.79/0.99      | sK4 != sK5 ),
% 2.79/0.99      inference(unflattening,[status(thm)],[c_445]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1961,plain,
% 2.79/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.79/0.99      | v1_relat_1(sK4) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1962,plain,
% 2.79/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.79/0.99      | v1_relat_1(sK4) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_1961]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2,plain,
% 2.79/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.79/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2088,plain,
% 2.79/0.99      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2249,plain,
% 2.79/0.99      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_2088]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4,plain,
% 2.79/0.99      ( r1_tarski(X0,X0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2250,plain,
% 2.79/0.99      ( r1_tarski(sK4,sK4) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1117,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2004,plain,
% 2.79/0.99      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_1117]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2316,plain,
% 2.79/0.99      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_2004]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3566,plain,
% 2.79/0.99      ( sK3 = k1_xboole_0
% 2.79/0.99      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_3553,c_36,c_38,c_30,c_446,c_1962,c_2249,c_2250,c_2316]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3572,plain,
% 2.79/0.99      ( sK3 = k1_xboole_0 | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_2935,c_3566]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_10,plain,
% 2.79/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1,plain,
% 2.79/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_211,plain,
% 2.79/0.99      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_10,c_1]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_212,plain,
% 2.79/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.79/0.99      inference(renaming,[status(thm)],[c_211]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1702,plain,
% 2.79/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 2.79/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_212]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3625,plain,
% 2.79/0.99      ( sK3 = k1_xboole_0 | m1_subset_1(sK1(sK4,sK5),sK2) = iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_3572,c_1702]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_29,negated_conjecture,
% 2.79/0.99      ( ~ m1_subset_1(X0,sK2) | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1707,plain,
% 2.79/0.99      ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
% 2.79/0.99      | m1_subset_1(X0,sK2) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_5113,plain,
% 2.79/0.99      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 2.79/0.99      | sK3 = k1_xboole_0 ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_3625,c_1707]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_16,plain,
% 2.79/0.99      ( ~ v1_relat_1(X0)
% 2.79/0.99      | ~ v1_relat_1(X1)
% 2.79/0.99      | ~ v1_funct_1(X0)
% 2.79/0.99      | ~ v1_funct_1(X1)
% 2.79/0.99      | X0 = X1
% 2.79/0.99      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 2.79/0.99      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1711,plain,
% 2.79/0.99      ( X0 = X1
% 2.79/0.99      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 2.79/0.99      | k1_relat_1(X0) != k1_relat_1(X1)
% 2.79/0.99      | v1_relat_1(X0) != iProver_top
% 2.79/0.99      | v1_relat_1(X1) != iProver_top
% 2.79/0.99      | v1_funct_1(X1) != iProver_top
% 2.79/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_5192,plain,
% 2.79/0.99      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.79/0.99      | sK5 = sK4
% 2.79/0.99      | sK3 = k1_xboole_0
% 2.79/0.99      | v1_relat_1(sK5) != iProver_top
% 2.79/0.99      | v1_relat_1(sK4) != iProver_top
% 2.79/0.99      | v1_funct_1(sK5) != iProver_top
% 2.79/0.99      | v1_funct_1(sK4) != iProver_top ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_5113,c_1711]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_5193,plain,
% 2.79/0.99      ( ~ v1_relat_1(sK5)
% 2.79/0.99      | ~ v1_relat_1(sK4)
% 2.79/0.99      | ~ v1_funct_1(sK5)
% 2.79/0.99      | ~ v1_funct_1(sK4)
% 2.79/0.99      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.79/0.99      | sK5 = sK4
% 2.79/0.99      | sK3 = k1_xboole_0 ),
% 2.79/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5192]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_5195,plain,
% 2.79/0.99      ( k1_relat_1(sK4) != k1_relat_1(sK5) | sK3 = k1_xboole_0 ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_5192,c_35,c_33,c_32,c_30,c_446,c_1958,c_1961,c_2249,
% 2.79/0.99                 c_2250,c_2316,c_5193]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_5199,plain,
% 2.79/0.99      ( k1_relat_1(sK4) != sK2 | sK3 = k1_xboole_0 ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_2932,c_5195]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_5270,plain,
% 2.79/0.99      ( sK3 = k1_xboole_0 ),
% 2.79/0.99      inference(global_propositional_subsumption,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_5199,c_2935]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_5300,plain,
% 2.79/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 2.79/0.99      inference(demodulation,[status(thm)],[c_5270,c_1706]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_5,plain,
% 2.79/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.79/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_5306,plain,
% 2.79/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.79/0.99      inference(demodulation,[status(thm)],[c_5300,c_5]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_5301,plain,
% 2.79/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 2.79/0.99      inference(demodulation,[status(thm)],[c_5270,c_1704]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_5303,plain,
% 2.79/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.79/0.99      inference(demodulation,[status(thm)],[c_5301,c_5]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_14,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.79/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4221,plain,
% 2.79/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4222,plain,
% 2.79/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 2.79/0.99      | r1_tarski(sK4,X0) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_4221]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4224,plain,
% 2.79/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.79/0.99      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_4222]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3613,plain,
% 2.79/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0)) | r1_tarski(sK5,X0) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3614,plain,
% 2.79/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 2.79/0.99      | r1_tarski(sK5,X0) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_3613]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3616,plain,
% 2.79/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.79/0.99      | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_3614]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_12,plain,
% 2.79/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.79/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2826,plain,
% 2.79/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2829,plain,
% 2.79/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2826]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2799,plain,
% 2.79/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2802,plain,
% 2.79/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2799]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2262,plain,
% 2.79/0.99      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2263,plain,
% 2.79/0.99      ( sK4 = X0
% 2.79/0.99      | r1_tarski(X0,sK4) != iProver_top
% 2.79/0.99      | r1_tarski(sK4,X0) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2262]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2265,plain,
% 2.79/0.99      ( sK4 = k1_xboole_0
% 2.79/0.99      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 2.79/0.99      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_2263]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2244,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4)) | r1_tarski(X0,sK4) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2245,plain,
% 2.79/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
% 2.79/0.99      | r1_tarski(X0,sK4) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2244]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2247,plain,
% 2.79/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
% 2.79/0.99      | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_2245]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2233,plain,
% 2.79/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5)) | r1_tarski(X0,sK5) ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2234,plain,
% 2.79/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
% 2.79/0.99      | r1_tarski(X0,sK5) = iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2233]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2236,plain,
% 2.79/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) != iProver_top
% 2.79/0.99      | r1_tarski(k1_xboole_0,sK5) = iProver_top ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_2234]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2176,plain,
% 2.79/0.99      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2177,plain,
% 2.79/0.99      ( sK5 = X0
% 2.79/0.99      | r1_tarski(X0,sK5) != iProver_top
% 2.79/0.99      | r1_tarski(sK5,X0) != iProver_top ),
% 2.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2176]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2179,plain,
% 2.79/0.99      ( sK5 = k1_xboole_0
% 2.79/0.99      | r1_tarski(sK5,k1_xboole_0) != iProver_top
% 2.79/0.99      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_2177]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2005,plain,
% 2.79/0.99      ( sK5 != k1_xboole_0 | sK4 = sK5 | sK4 != k1_xboole_0 ),
% 2.79/0.99      inference(instantiation,[status(thm)],[c_2004]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(contradiction,plain,
% 2.79/0.99      ( $false ),
% 2.79/0.99      inference(minisat,
% 2.79/0.99                [status(thm)],
% 2.79/0.99                [c_5306,c_5303,c_4224,c_3616,c_2829,c_2802,c_2265,c_2247,
% 2.79/0.99                 c_2236,c_2179,c_2005,c_446,c_30]) ).
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.79/0.99  
% 2.79/0.99  ------                               Statistics
% 2.79/0.99  
% 2.79/0.99  ------ General
% 2.79/0.99  
% 2.79/0.99  abstr_ref_over_cycles:                  0
% 2.79/0.99  abstr_ref_under_cycles:                 0
% 2.79/0.99  gc_basic_clause_elim:                   0
% 2.79/1.00  forced_gc_time:                         0
% 2.79/1.00  parsing_time:                           0.012
% 2.79/1.00  unif_index_cands_time:                  0.
% 2.79/1.00  unif_index_add_time:                    0.
% 2.79/1.00  orderings_time:                         0.
% 2.79/1.00  out_proof_time:                         0.011
% 2.79/1.00  total_time:                             0.163
% 2.79/1.00  num_of_symbols:                         51
% 2.79/1.00  num_of_terms:                           3634
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing
% 2.79/1.00  
% 2.79/1.00  num_of_splits:                          0
% 2.79/1.00  num_of_split_atoms:                     0
% 2.79/1.00  num_of_reused_defs:                     0
% 2.79/1.00  num_eq_ax_congr_red:                    26
% 2.79/1.00  num_of_sem_filtered_clauses:            1
% 2.79/1.00  num_of_subtypes:                        0
% 2.79/1.00  monotx_restored_types:                  0
% 2.79/1.00  sat_num_of_epr_types:                   0
% 2.79/1.00  sat_num_of_non_cyclic_types:            0
% 2.79/1.00  sat_guarded_non_collapsed_types:        0
% 2.79/1.00  num_pure_diseq_elim:                    0
% 2.79/1.00  simp_replaced_by:                       0
% 2.79/1.00  res_preprocessed:                       147
% 2.79/1.00  prep_upred:                             0
% 2.79/1.00  prep_unflattend:                        69
% 2.79/1.00  smt_new_axioms:                         0
% 2.79/1.00  pred_elim_cands:                        6
% 2.79/1.00  pred_elim:                              2
% 2.79/1.00  pred_elim_cl:                           4
% 2.79/1.00  pred_elim_cycles:                       5
% 2.79/1.00  merged_defs:                            8
% 2.79/1.00  merged_defs_ncl:                        0
% 2.79/1.00  bin_hyper_res:                          8
% 2.79/1.00  prep_cycles:                            4
% 2.79/1.00  pred_elim_time:                         0.008
% 2.79/1.00  splitting_time:                         0.
% 2.79/1.00  sem_filter_time:                        0.
% 2.79/1.00  monotx_time:                            0.
% 2.79/1.00  subtype_inf_time:                       0.
% 2.79/1.00  
% 2.79/1.00  ------ Problem properties
% 2.79/1.00  
% 2.79/1.00  clauses:                                31
% 2.79/1.00  conjectures:                            5
% 2.79/1.00  epr:                                    10
% 2.79/1.00  horn:                                   23
% 2.79/1.00  ground:                                 11
% 2.79/1.00  unary:                                  9
% 2.79/1.00  binary:                                 10
% 2.79/1.00  lits:                                   75
% 2.79/1.00  lits_eq:                                28
% 2.79/1.00  fd_pure:                                0
% 2.79/1.00  fd_pseudo:                              0
% 2.79/1.00  fd_cond:                                1
% 2.79/1.00  fd_pseudo_cond:                         3
% 2.79/1.00  ac_symbols:                             0
% 2.79/1.00  
% 2.79/1.00  ------ Propositional Solver
% 2.79/1.00  
% 2.79/1.00  prop_solver_calls:                      28
% 2.79/1.00  prop_fast_solver_calls:                 1063
% 2.79/1.00  smt_solver_calls:                       0
% 2.79/1.00  smt_fast_solver_calls:                  0
% 2.79/1.00  prop_num_of_clauses:                    1557
% 2.79/1.00  prop_preprocess_simplified:             5644
% 2.79/1.00  prop_fo_subsumed:                       25
% 2.79/1.00  prop_solver_time:                       0.
% 2.79/1.00  smt_solver_time:                        0.
% 2.79/1.00  smt_fast_solver_time:                   0.
% 2.79/1.00  prop_fast_solver_time:                  0.
% 2.79/1.00  prop_unsat_core_time:                   0.
% 2.79/1.00  
% 2.79/1.00  ------ QBF
% 2.79/1.00  
% 2.79/1.00  qbf_q_res:                              0
% 2.79/1.00  qbf_num_tautologies:                    0
% 2.79/1.00  qbf_prep_cycles:                        0
% 2.79/1.00  
% 2.79/1.00  ------ BMC1
% 2.79/1.00  
% 2.79/1.00  bmc1_current_bound:                     -1
% 2.79/1.00  bmc1_last_solved_bound:                 -1
% 2.79/1.00  bmc1_unsat_core_size:                   -1
% 2.79/1.00  bmc1_unsat_core_parents_size:           -1
% 2.79/1.00  bmc1_merge_next_fun:                    0
% 2.79/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.79/1.00  
% 2.79/1.00  ------ Instantiation
% 2.79/1.00  
% 2.79/1.00  inst_num_of_clauses:                    525
% 2.79/1.00  inst_num_in_passive:                    18
% 2.79/1.00  inst_num_in_active:                     331
% 2.79/1.00  inst_num_in_unprocessed:                176
% 2.79/1.00  inst_num_of_loops:                      400
% 2.79/1.00  inst_num_of_learning_restarts:          0
% 2.79/1.00  inst_num_moves_active_passive:          66
% 2.79/1.00  inst_lit_activity:                      0
% 2.79/1.00  inst_lit_activity_moves:                0
% 2.79/1.00  inst_num_tautologies:                   0
% 2.79/1.00  inst_num_prop_implied:                  0
% 2.79/1.00  inst_num_existing_simplified:           0
% 2.79/1.00  inst_num_eq_res_simplified:             0
% 2.79/1.00  inst_num_child_elim:                    0
% 2.79/1.00  inst_num_of_dismatching_blockings:      304
% 2.79/1.00  inst_num_of_non_proper_insts:           546
% 2.79/1.00  inst_num_of_duplicates:                 0
% 2.79/1.00  inst_inst_num_from_inst_to_res:         0
% 2.79/1.00  inst_dismatching_checking_time:         0.
% 2.79/1.00  
% 2.79/1.00  ------ Resolution
% 2.79/1.00  
% 2.79/1.00  res_num_of_clauses:                     0
% 2.79/1.00  res_num_in_passive:                     0
% 2.79/1.00  res_num_in_active:                      0
% 2.79/1.00  res_num_of_loops:                       151
% 2.79/1.00  res_forward_subset_subsumed:            32
% 2.79/1.00  res_backward_subset_subsumed:           0
% 2.79/1.00  res_forward_subsumed:                   0
% 2.79/1.00  res_backward_subsumed:                  0
% 2.79/1.00  res_forward_subsumption_resolution:     0
% 2.79/1.00  res_backward_subsumption_resolution:    0
% 2.79/1.00  res_clause_to_clause_subsumption:       257
% 2.79/1.00  res_orphan_elimination:                 0
% 2.79/1.00  res_tautology_del:                      59
% 2.79/1.00  res_num_eq_res_simplified:              0
% 2.79/1.00  res_num_sel_changes:                    0
% 2.79/1.00  res_moves_from_active_to_pass:          0
% 2.79/1.00  
% 2.79/1.00  ------ Superposition
% 2.79/1.00  
% 2.79/1.00  sup_time_total:                         0.
% 2.79/1.00  sup_time_generating:                    0.
% 2.79/1.00  sup_time_sim_full:                      0.
% 2.79/1.00  sup_time_sim_immed:                     0.
% 2.79/1.00  
% 2.79/1.00  sup_num_of_clauses:                     75
% 2.79/1.00  sup_num_in_active:                      41
% 2.79/1.00  sup_num_in_passive:                     34
% 2.79/1.00  sup_num_of_loops:                       78
% 2.79/1.00  sup_fw_superposition:                   66
% 2.79/1.00  sup_bw_superposition:                   51
% 2.79/1.00  sup_immediate_simplified:               27
% 2.79/1.00  sup_given_eliminated:                   0
% 2.79/1.00  comparisons_done:                       0
% 2.79/1.00  comparisons_avoided:                    14
% 2.79/1.00  
% 2.79/1.00  ------ Simplifications
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  sim_fw_subset_subsumed:                 7
% 2.79/1.00  sim_bw_subset_subsumed:                 11
% 2.79/1.00  sim_fw_subsumed:                        4
% 2.79/1.00  sim_bw_subsumed:                        0
% 2.79/1.00  sim_fw_subsumption_res:                 4
% 2.79/1.00  sim_bw_subsumption_res:                 0
% 2.79/1.00  sim_tautology_del:                      9
% 2.79/1.00  sim_eq_tautology_del:                   15
% 2.79/1.00  sim_eq_res_simp:                        2
% 2.79/1.00  sim_fw_demodulated:                     20
% 2.79/1.00  sim_bw_demodulated:                     29
% 2.79/1.00  sim_light_normalised:                   0
% 2.79/1.00  sim_joinable_taut:                      0
% 2.79/1.00  sim_joinable_simp:                      0
% 2.79/1.00  sim_ac_normalised:                      0
% 2.79/1.00  sim_smt_subsumption:                    0
% 2.79/1.00  
%------------------------------------------------------------------------------
