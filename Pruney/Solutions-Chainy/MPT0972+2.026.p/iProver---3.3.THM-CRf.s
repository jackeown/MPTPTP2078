%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:13 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  173 (2294 expanded)
%              Number of clauses        :  107 ( 687 expanded)
%              Number of leaves         :   18 ( 552 expanded)
%              Depth                    :   26
%              Number of atoms          :  573 (14520 expanded)
%              Number of equality atoms :  258 (3486 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

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

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f38,plain,(
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

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK5)
        & ! [X4] :
            ( k1_funct_1(sK5,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK5,X0,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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
          ( ~ r2_relset_1(sK2,sK3,sK4,X3)
          & ! [X4] :
              ( k1_funct_1(sK4,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK2) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5)
    & ! [X4] :
        ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
        | ~ r2_hidden(X4,sK2) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f40,f39])).

fof(f71,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f35])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f74,plain,(
    ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f73,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
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

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_230,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_231,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_230])).

cnf(c_294,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_231])).

cnf(c_397,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_294])).

cnf(c_398,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_4682,plain,
    ( ~ r2_hidden(sK0(X0,sK5),X0)
    | ~ r1_tarski(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_4684,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4682])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_498,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_500,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_498,c_27])).

cnf(c_1989,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1991,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2830,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1989,c_1991])).

cnf(c_3070,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_500,c_2830])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_508,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_509,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_511,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_509,c_30])).

cnf(c_1987,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2831,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1987,c_1991])).

cnf(c_3155,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_511,c_2831])).

cnf(c_14,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1993,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3305,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3070,c_1993])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_36,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_38,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2190,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2191,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2190])).

cnf(c_3885,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3305,c_36,c_38,c_2191])).

cnf(c_3886,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3885])).

cnf(c_3898,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_3886])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_33,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_17,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_25,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != X0
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_415,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_2193,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2194,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2193])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2292,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2554,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2292])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2555,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1449,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2219,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1449])).

cnf(c_3627,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2219])).

cnf(c_3911,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3898,c_33,c_35,c_27,c_415,c_2194,c_2554,c_2555,c_3627])).

cnf(c_3917,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_3911])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1990,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3983,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3917,c_1990])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1994,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4086,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3983,c_1994])).

cnf(c_4102,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4086])).

cnf(c_4245,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4086,c_32,c_30,c_29,c_27,c_415,c_2190,c_2193,c_2554,c_2555,c_3627,c_4102])).

cnf(c_4249,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3070,c_4245])).

cnf(c_4276,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4249,c_3155])).

cnf(c_4293,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4276,c_1989])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_4299,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4293,c_7])).

cnf(c_4348,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4299])).

cnf(c_4294,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4276,c_1987])).

cnf(c_4296,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4294,c_7])).

cnf(c_4145,plain,
    ( ~ r2_hidden(sK0(sK5,sK4),sK5)
    | ~ r1_tarski(sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_4146,plain,
    ( r2_hidden(sK0(sK5,sK4),sK5) != iProver_top
    | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4145])).

cnf(c_1450,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_2534,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,sK5)
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_1450])).

cnf(c_3170,plain,
    ( ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_2534])).

cnf(c_3171,plain,
    ( sK5 != X0
    | r1_tarski(sK4,X0) != iProver_top
    | r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3170])).

cnf(c_3173,plain,
    ( sK5 != k1_xboole_0
    | r1_tarski(sK4,sK5) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3171])).

cnf(c_2466,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_1449])).

cnf(c_3143,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2466])).

cnf(c_3145,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_3143])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2892,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2893,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2892])).

cnf(c_2895,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2893])).

cnf(c_2859,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2860,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2859])).

cnf(c_2862,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2860])).

cnf(c_2861,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2859])).

cnf(c_2529,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2270,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2528,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2270])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2513,plain,
    ( r2_hidden(sK0(X0,sK5),X0)
    | r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2525,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0)
    | r1_tarski(k1_xboole_0,sK5) ),
    inference(instantiation,[status(thm)],[c_2513])).

cnf(c_2308,plain,
    ( r2_hidden(sK0(sK5,sK4),sK5)
    | r1_tarski(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2315,plain,
    ( r2_hidden(sK0(sK5,sK4),sK5) = iProver_top
    | r1_tarski(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2308])).

cnf(c_2272,plain,
    ( ~ r1_tarski(sK5,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_2270])).

cnf(c_2210,plain,
    ( ~ r1_tarski(sK5,sK4)
    | ~ r1_tarski(sK4,sK5)
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2211,plain,
    ( sK4 = sK5
    | r1_tarski(sK5,sK4) != iProver_top
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2210])).

cnf(c_91,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4684,c_4348,c_4299,c_4296,c_4146,c_3173,c_3145,c_2895,c_2862,c_2861,c_2529,c_2528,c_2525,c_2315,c_2272,c_2211,c_415,c_91,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.14/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.02  
% 3.14/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.14/1.02  
% 3.14/1.02  ------  iProver source info
% 3.14/1.02  
% 3.14/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.14/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.14/1.02  git: non_committed_changes: false
% 3.14/1.02  git: last_make_outside_of_git: false
% 3.14/1.02  
% 3.14/1.02  ------ 
% 3.14/1.02  
% 3.14/1.02  ------ Input Options
% 3.14/1.02  
% 3.14/1.02  --out_options                           all
% 3.14/1.02  --tptp_safe_out                         true
% 3.14/1.02  --problem_path                          ""
% 3.14/1.02  --include_path                          ""
% 3.14/1.02  --clausifier                            res/vclausify_rel
% 3.14/1.02  --clausifier_options                    --mode clausify
% 3.14/1.02  --stdin                                 false
% 3.14/1.02  --stats_out                             all
% 3.14/1.02  
% 3.14/1.02  ------ General Options
% 3.14/1.02  
% 3.14/1.02  --fof                                   false
% 3.14/1.02  --time_out_real                         305.
% 3.14/1.02  --time_out_virtual                      -1.
% 3.14/1.02  --symbol_type_check                     false
% 3.14/1.02  --clausify_out                          false
% 3.14/1.02  --sig_cnt_out                           false
% 3.14/1.02  --trig_cnt_out                          false
% 3.14/1.02  --trig_cnt_out_tolerance                1.
% 3.14/1.02  --trig_cnt_out_sk_spl                   false
% 3.14/1.02  --abstr_cl_out                          false
% 3.14/1.02  
% 3.14/1.02  ------ Global Options
% 3.14/1.02  
% 3.14/1.02  --schedule                              default
% 3.14/1.02  --add_important_lit                     false
% 3.14/1.02  --prop_solver_per_cl                    1000
% 3.14/1.02  --min_unsat_core                        false
% 3.14/1.02  --soft_assumptions                      false
% 3.14/1.02  --soft_lemma_size                       3
% 3.14/1.02  --prop_impl_unit_size                   0
% 3.14/1.02  --prop_impl_unit                        []
% 3.14/1.02  --share_sel_clauses                     true
% 3.14/1.02  --reset_solvers                         false
% 3.14/1.02  --bc_imp_inh                            [conj_cone]
% 3.14/1.02  --conj_cone_tolerance                   3.
% 3.14/1.02  --extra_neg_conj                        none
% 3.14/1.02  --large_theory_mode                     true
% 3.14/1.02  --prolific_symb_bound                   200
% 3.14/1.02  --lt_threshold                          2000
% 3.14/1.02  --clause_weak_htbl                      true
% 3.14/1.02  --gc_record_bc_elim                     false
% 3.14/1.02  
% 3.14/1.02  ------ Preprocessing Options
% 3.14/1.02  
% 3.14/1.02  --preprocessing_flag                    true
% 3.14/1.02  --time_out_prep_mult                    0.1
% 3.14/1.02  --splitting_mode                        input
% 3.14/1.02  --splitting_grd                         true
% 3.14/1.02  --splitting_cvd                         false
% 3.14/1.02  --splitting_cvd_svl                     false
% 3.14/1.02  --splitting_nvd                         32
% 3.14/1.02  --sub_typing                            true
% 3.14/1.02  --prep_gs_sim                           true
% 3.14/1.02  --prep_unflatten                        true
% 3.14/1.02  --prep_res_sim                          true
% 3.14/1.02  --prep_upred                            true
% 3.14/1.02  --prep_sem_filter                       exhaustive
% 3.14/1.02  --prep_sem_filter_out                   false
% 3.14/1.02  --pred_elim                             true
% 3.14/1.02  --res_sim_input                         true
% 3.14/1.02  --eq_ax_congr_red                       true
% 3.14/1.02  --pure_diseq_elim                       true
% 3.14/1.02  --brand_transform                       false
% 3.14/1.02  --non_eq_to_eq                          false
% 3.14/1.02  --prep_def_merge                        true
% 3.14/1.02  --prep_def_merge_prop_impl              false
% 3.14/1.02  --prep_def_merge_mbd                    true
% 3.14/1.02  --prep_def_merge_tr_red                 false
% 3.14/1.02  --prep_def_merge_tr_cl                  false
% 3.14/1.02  --smt_preprocessing                     true
% 3.14/1.02  --smt_ac_axioms                         fast
% 3.14/1.02  --preprocessed_out                      false
% 3.14/1.02  --preprocessed_stats                    false
% 3.14/1.02  
% 3.14/1.02  ------ Abstraction refinement Options
% 3.14/1.02  
% 3.14/1.02  --abstr_ref                             []
% 3.14/1.02  --abstr_ref_prep                        false
% 3.14/1.02  --abstr_ref_until_sat                   false
% 3.14/1.02  --abstr_ref_sig_restrict                funpre
% 3.14/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/1.02  --abstr_ref_under                       []
% 3.14/1.02  
% 3.14/1.02  ------ SAT Options
% 3.14/1.02  
% 3.14/1.02  --sat_mode                              false
% 3.14/1.02  --sat_fm_restart_options                ""
% 3.14/1.02  --sat_gr_def                            false
% 3.14/1.02  --sat_epr_types                         true
% 3.14/1.02  --sat_non_cyclic_types                  false
% 3.14/1.02  --sat_finite_models                     false
% 3.14/1.02  --sat_fm_lemmas                         false
% 3.14/1.02  --sat_fm_prep                           false
% 3.14/1.02  --sat_fm_uc_incr                        true
% 3.14/1.02  --sat_out_model                         small
% 3.14/1.02  --sat_out_clauses                       false
% 3.14/1.02  
% 3.14/1.02  ------ QBF Options
% 3.14/1.02  
% 3.14/1.02  --qbf_mode                              false
% 3.14/1.02  --qbf_elim_univ                         false
% 3.14/1.02  --qbf_dom_inst                          none
% 3.14/1.02  --qbf_dom_pre_inst                      false
% 3.14/1.02  --qbf_sk_in                             false
% 3.14/1.02  --qbf_pred_elim                         true
% 3.14/1.02  --qbf_split                             512
% 3.14/1.02  
% 3.14/1.02  ------ BMC1 Options
% 3.14/1.02  
% 3.14/1.02  --bmc1_incremental                      false
% 3.14/1.02  --bmc1_axioms                           reachable_all
% 3.14/1.02  --bmc1_min_bound                        0
% 3.14/1.02  --bmc1_max_bound                        -1
% 3.14/1.02  --bmc1_max_bound_default                -1
% 3.14/1.02  --bmc1_symbol_reachability              true
% 3.14/1.02  --bmc1_property_lemmas                  false
% 3.14/1.02  --bmc1_k_induction                      false
% 3.14/1.02  --bmc1_non_equiv_states                 false
% 3.14/1.02  --bmc1_deadlock                         false
% 3.14/1.02  --bmc1_ucm                              false
% 3.14/1.02  --bmc1_add_unsat_core                   none
% 3.14/1.02  --bmc1_unsat_core_children              false
% 3.14/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/1.02  --bmc1_out_stat                         full
% 3.14/1.02  --bmc1_ground_init                      false
% 3.14/1.02  --bmc1_pre_inst_next_state              false
% 3.14/1.02  --bmc1_pre_inst_state                   false
% 3.14/1.02  --bmc1_pre_inst_reach_state             false
% 3.14/1.02  --bmc1_out_unsat_core                   false
% 3.14/1.02  --bmc1_aig_witness_out                  false
% 3.14/1.02  --bmc1_verbose                          false
% 3.14/1.02  --bmc1_dump_clauses_tptp                false
% 3.14/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.14/1.02  --bmc1_dump_file                        -
% 3.14/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.14/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.14/1.02  --bmc1_ucm_extend_mode                  1
% 3.14/1.02  --bmc1_ucm_init_mode                    2
% 3.14/1.02  --bmc1_ucm_cone_mode                    none
% 3.14/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.14/1.02  --bmc1_ucm_relax_model                  4
% 3.14/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.14/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/1.02  --bmc1_ucm_layered_model                none
% 3.14/1.02  --bmc1_ucm_max_lemma_size               10
% 3.14/1.02  
% 3.14/1.02  ------ AIG Options
% 3.14/1.02  
% 3.14/1.02  --aig_mode                              false
% 3.14/1.02  
% 3.14/1.02  ------ Instantiation Options
% 3.14/1.02  
% 3.14/1.02  --instantiation_flag                    true
% 3.14/1.02  --inst_sos_flag                         false
% 3.14/1.02  --inst_sos_phase                        true
% 3.14/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/1.02  --inst_lit_sel_side                     num_symb
% 3.14/1.02  --inst_solver_per_active                1400
% 3.14/1.02  --inst_solver_calls_frac                1.
% 3.14/1.02  --inst_passive_queue_type               priority_queues
% 3.14/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/1.02  --inst_passive_queues_freq              [25;2]
% 3.14/1.02  --inst_dismatching                      true
% 3.14/1.02  --inst_eager_unprocessed_to_passive     true
% 3.14/1.02  --inst_prop_sim_given                   true
% 3.14/1.02  --inst_prop_sim_new                     false
% 3.14/1.02  --inst_subs_new                         false
% 3.14/1.02  --inst_eq_res_simp                      false
% 3.14/1.02  --inst_subs_given                       false
% 3.14/1.02  --inst_orphan_elimination               true
% 3.14/1.02  --inst_learning_loop_flag               true
% 3.14/1.02  --inst_learning_start                   3000
% 3.14/1.02  --inst_learning_factor                  2
% 3.14/1.02  --inst_start_prop_sim_after_learn       3
% 3.14/1.02  --inst_sel_renew                        solver
% 3.14/1.02  --inst_lit_activity_flag                true
% 3.14/1.02  --inst_restr_to_given                   false
% 3.14/1.02  --inst_activity_threshold               500
% 3.14/1.02  --inst_out_proof                        true
% 3.14/1.02  
% 3.14/1.02  ------ Resolution Options
% 3.14/1.02  
% 3.14/1.02  --resolution_flag                       true
% 3.14/1.02  --res_lit_sel                           adaptive
% 3.14/1.02  --res_lit_sel_side                      none
% 3.14/1.02  --res_ordering                          kbo
% 3.14/1.02  --res_to_prop_solver                    active
% 3.14/1.02  --res_prop_simpl_new                    false
% 3.14/1.02  --res_prop_simpl_given                  true
% 3.14/1.02  --res_passive_queue_type                priority_queues
% 3.14/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/1.02  --res_passive_queues_freq               [15;5]
% 3.14/1.02  --res_forward_subs                      full
% 3.14/1.02  --res_backward_subs                     full
% 3.14/1.02  --res_forward_subs_resolution           true
% 3.14/1.02  --res_backward_subs_resolution          true
% 3.14/1.02  --res_orphan_elimination                true
% 3.14/1.02  --res_time_limit                        2.
% 3.14/1.02  --res_out_proof                         true
% 3.14/1.02  
% 3.14/1.02  ------ Superposition Options
% 3.14/1.02  
% 3.14/1.02  --superposition_flag                    true
% 3.14/1.02  --sup_passive_queue_type                priority_queues
% 3.14/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.14/1.02  --demod_completeness_check              fast
% 3.14/1.02  --demod_use_ground                      true
% 3.14/1.02  --sup_to_prop_solver                    passive
% 3.14/1.02  --sup_prop_simpl_new                    true
% 3.14/1.02  --sup_prop_simpl_given                  true
% 3.14/1.02  --sup_fun_splitting                     false
% 3.14/1.02  --sup_smt_interval                      50000
% 3.14/1.02  
% 3.14/1.02  ------ Superposition Simplification Setup
% 3.14/1.02  
% 3.14/1.02  --sup_indices_passive                   []
% 3.14/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.02  --sup_full_bw                           [BwDemod]
% 3.14/1.02  --sup_immed_triv                        [TrivRules]
% 3.14/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.02  --sup_immed_bw_main                     []
% 3.14/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/1.02  
% 3.14/1.02  ------ Combination Options
% 3.14/1.02  
% 3.14/1.02  --comb_res_mult                         3
% 3.14/1.02  --comb_sup_mult                         2
% 3.14/1.02  --comb_inst_mult                        10
% 3.14/1.02  
% 3.14/1.02  ------ Debug Options
% 3.14/1.02  
% 3.14/1.02  --dbg_backtrace                         false
% 3.14/1.02  --dbg_dump_prop_clauses                 false
% 3.14/1.02  --dbg_dump_prop_clauses_file            -
% 3.14/1.02  --dbg_out_stat                          false
% 3.14/1.02  ------ Parsing...
% 3.14/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.14/1.02  
% 3.14/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.14/1.02  
% 3.14/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.14/1.02  
% 3.14/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.14/1.02  ------ Proving...
% 3.14/1.02  ------ Problem Properties 
% 3.14/1.02  
% 3.14/1.02  
% 3.14/1.02  clauses                                 27
% 3.14/1.02  conjectures                             5
% 3.14/1.02  EPR                                     7
% 3.14/1.02  Horn                                    20
% 3.14/1.02  unary                                   8
% 3.14/1.02  binary                                  10
% 3.14/1.02  lits                                    65
% 3.14/1.02  lits eq                                 28
% 3.14/1.02  fd_pure                                 0
% 3.14/1.02  fd_pseudo                               0
% 3.14/1.02  fd_cond                                 1
% 3.14/1.02  fd_pseudo_cond                          3
% 3.14/1.02  AC symbols                              0
% 3.14/1.02  
% 3.14/1.02  ------ Schedule dynamic 5 is on 
% 3.14/1.02  
% 3.14/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.14/1.02  
% 3.14/1.02  
% 3.14/1.02  ------ 
% 3.14/1.02  Current options:
% 3.14/1.02  ------ 
% 3.14/1.02  
% 3.14/1.02  ------ Input Options
% 3.14/1.02  
% 3.14/1.02  --out_options                           all
% 3.14/1.02  --tptp_safe_out                         true
% 3.14/1.02  --problem_path                          ""
% 3.14/1.02  --include_path                          ""
% 3.14/1.02  --clausifier                            res/vclausify_rel
% 3.14/1.02  --clausifier_options                    --mode clausify
% 3.14/1.02  --stdin                                 false
% 3.14/1.02  --stats_out                             all
% 3.14/1.02  
% 3.14/1.02  ------ General Options
% 3.14/1.02  
% 3.14/1.02  --fof                                   false
% 3.14/1.02  --time_out_real                         305.
% 3.14/1.02  --time_out_virtual                      -1.
% 3.14/1.02  --symbol_type_check                     false
% 3.14/1.02  --clausify_out                          false
% 3.14/1.02  --sig_cnt_out                           false
% 3.14/1.02  --trig_cnt_out                          false
% 3.14/1.02  --trig_cnt_out_tolerance                1.
% 3.14/1.02  --trig_cnt_out_sk_spl                   false
% 3.14/1.02  --abstr_cl_out                          false
% 3.14/1.02  
% 3.14/1.02  ------ Global Options
% 3.14/1.02  
% 3.14/1.02  --schedule                              default
% 3.14/1.02  --add_important_lit                     false
% 3.14/1.02  --prop_solver_per_cl                    1000
% 3.14/1.02  --min_unsat_core                        false
% 3.14/1.02  --soft_assumptions                      false
% 3.14/1.02  --soft_lemma_size                       3
% 3.14/1.02  --prop_impl_unit_size                   0
% 3.14/1.02  --prop_impl_unit                        []
% 3.14/1.02  --share_sel_clauses                     true
% 3.14/1.02  --reset_solvers                         false
% 3.14/1.02  --bc_imp_inh                            [conj_cone]
% 3.14/1.02  --conj_cone_tolerance                   3.
% 3.14/1.02  --extra_neg_conj                        none
% 3.14/1.02  --large_theory_mode                     true
% 3.14/1.02  --prolific_symb_bound                   200
% 3.14/1.02  --lt_threshold                          2000
% 3.14/1.02  --clause_weak_htbl                      true
% 3.14/1.02  --gc_record_bc_elim                     false
% 3.14/1.02  
% 3.14/1.02  ------ Preprocessing Options
% 3.14/1.02  
% 3.14/1.02  --preprocessing_flag                    true
% 3.14/1.02  --time_out_prep_mult                    0.1
% 3.14/1.02  --splitting_mode                        input
% 3.14/1.02  --splitting_grd                         true
% 3.14/1.02  --splitting_cvd                         false
% 3.14/1.02  --splitting_cvd_svl                     false
% 3.14/1.02  --splitting_nvd                         32
% 3.14/1.02  --sub_typing                            true
% 3.14/1.02  --prep_gs_sim                           true
% 3.14/1.02  --prep_unflatten                        true
% 3.14/1.02  --prep_res_sim                          true
% 3.14/1.02  --prep_upred                            true
% 3.14/1.02  --prep_sem_filter                       exhaustive
% 3.14/1.02  --prep_sem_filter_out                   false
% 3.14/1.02  --pred_elim                             true
% 3.14/1.02  --res_sim_input                         true
% 3.14/1.02  --eq_ax_congr_red                       true
% 3.14/1.02  --pure_diseq_elim                       true
% 3.14/1.02  --brand_transform                       false
% 3.14/1.02  --non_eq_to_eq                          false
% 3.14/1.02  --prep_def_merge                        true
% 3.14/1.02  --prep_def_merge_prop_impl              false
% 3.14/1.02  --prep_def_merge_mbd                    true
% 3.14/1.02  --prep_def_merge_tr_red                 false
% 3.14/1.02  --prep_def_merge_tr_cl                  false
% 3.14/1.02  --smt_preprocessing                     true
% 3.14/1.02  --smt_ac_axioms                         fast
% 3.14/1.02  --preprocessed_out                      false
% 3.14/1.02  --preprocessed_stats                    false
% 3.14/1.02  
% 3.14/1.02  ------ Abstraction refinement Options
% 3.14/1.02  
% 3.14/1.02  --abstr_ref                             []
% 3.14/1.02  --abstr_ref_prep                        false
% 3.14/1.02  --abstr_ref_until_sat                   false
% 3.14/1.02  --abstr_ref_sig_restrict                funpre
% 3.14/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/1.02  --abstr_ref_under                       []
% 3.14/1.02  
% 3.14/1.02  ------ SAT Options
% 3.14/1.02  
% 3.14/1.02  --sat_mode                              false
% 3.14/1.02  --sat_fm_restart_options                ""
% 3.14/1.02  --sat_gr_def                            false
% 3.14/1.02  --sat_epr_types                         true
% 3.14/1.02  --sat_non_cyclic_types                  false
% 3.14/1.02  --sat_finite_models                     false
% 3.14/1.02  --sat_fm_lemmas                         false
% 3.14/1.02  --sat_fm_prep                           false
% 3.14/1.02  --sat_fm_uc_incr                        true
% 3.14/1.02  --sat_out_model                         small
% 3.14/1.02  --sat_out_clauses                       false
% 3.14/1.02  
% 3.14/1.02  ------ QBF Options
% 3.14/1.02  
% 3.14/1.02  --qbf_mode                              false
% 3.14/1.02  --qbf_elim_univ                         false
% 3.14/1.02  --qbf_dom_inst                          none
% 3.14/1.02  --qbf_dom_pre_inst                      false
% 3.14/1.02  --qbf_sk_in                             false
% 3.14/1.02  --qbf_pred_elim                         true
% 3.14/1.02  --qbf_split                             512
% 3.14/1.02  
% 3.14/1.02  ------ BMC1 Options
% 3.14/1.02  
% 3.14/1.02  --bmc1_incremental                      false
% 3.14/1.02  --bmc1_axioms                           reachable_all
% 3.14/1.02  --bmc1_min_bound                        0
% 3.14/1.02  --bmc1_max_bound                        -1
% 3.14/1.02  --bmc1_max_bound_default                -1
% 3.14/1.02  --bmc1_symbol_reachability              true
% 3.14/1.02  --bmc1_property_lemmas                  false
% 3.14/1.02  --bmc1_k_induction                      false
% 3.14/1.02  --bmc1_non_equiv_states                 false
% 3.14/1.02  --bmc1_deadlock                         false
% 3.14/1.02  --bmc1_ucm                              false
% 3.14/1.02  --bmc1_add_unsat_core                   none
% 3.14/1.02  --bmc1_unsat_core_children              false
% 3.14/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/1.02  --bmc1_out_stat                         full
% 3.14/1.02  --bmc1_ground_init                      false
% 3.14/1.02  --bmc1_pre_inst_next_state              false
% 3.14/1.02  --bmc1_pre_inst_state                   false
% 3.14/1.02  --bmc1_pre_inst_reach_state             false
% 3.14/1.02  --bmc1_out_unsat_core                   false
% 3.14/1.02  --bmc1_aig_witness_out                  false
% 3.14/1.02  --bmc1_verbose                          false
% 3.14/1.02  --bmc1_dump_clauses_tptp                false
% 3.14/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.14/1.02  --bmc1_dump_file                        -
% 3.14/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.14/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.14/1.02  --bmc1_ucm_extend_mode                  1
% 3.14/1.02  --bmc1_ucm_init_mode                    2
% 3.14/1.02  --bmc1_ucm_cone_mode                    none
% 3.14/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.14/1.02  --bmc1_ucm_relax_model                  4
% 3.14/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.14/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/1.02  --bmc1_ucm_layered_model                none
% 3.14/1.02  --bmc1_ucm_max_lemma_size               10
% 3.14/1.02  
% 3.14/1.02  ------ AIG Options
% 3.14/1.02  
% 3.14/1.02  --aig_mode                              false
% 3.14/1.02  
% 3.14/1.02  ------ Instantiation Options
% 3.14/1.02  
% 3.14/1.02  --instantiation_flag                    true
% 3.14/1.02  --inst_sos_flag                         false
% 3.14/1.02  --inst_sos_phase                        true
% 3.14/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/1.02  --inst_lit_sel_side                     none
% 3.14/1.02  --inst_solver_per_active                1400
% 3.14/1.02  --inst_solver_calls_frac                1.
% 3.14/1.02  --inst_passive_queue_type               priority_queues
% 3.14/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/1.02  --inst_passive_queues_freq              [25;2]
% 3.14/1.02  --inst_dismatching                      true
% 3.14/1.02  --inst_eager_unprocessed_to_passive     true
% 3.14/1.02  --inst_prop_sim_given                   true
% 3.14/1.02  --inst_prop_sim_new                     false
% 3.14/1.02  --inst_subs_new                         false
% 3.14/1.02  --inst_eq_res_simp                      false
% 3.14/1.02  --inst_subs_given                       false
% 3.14/1.02  --inst_orphan_elimination               true
% 3.14/1.02  --inst_learning_loop_flag               true
% 3.14/1.02  --inst_learning_start                   3000
% 3.14/1.02  --inst_learning_factor                  2
% 3.14/1.02  --inst_start_prop_sim_after_learn       3
% 3.14/1.02  --inst_sel_renew                        solver
% 3.14/1.02  --inst_lit_activity_flag                true
% 3.14/1.02  --inst_restr_to_given                   false
% 3.14/1.02  --inst_activity_threshold               500
% 3.14/1.02  --inst_out_proof                        true
% 3.14/1.02  
% 3.14/1.02  ------ Resolution Options
% 3.14/1.02  
% 3.14/1.02  --resolution_flag                       false
% 3.14/1.02  --res_lit_sel                           adaptive
% 3.14/1.02  --res_lit_sel_side                      none
% 3.14/1.02  --res_ordering                          kbo
% 3.14/1.02  --res_to_prop_solver                    active
% 3.14/1.02  --res_prop_simpl_new                    false
% 3.14/1.02  --res_prop_simpl_given                  true
% 3.14/1.02  --res_passive_queue_type                priority_queues
% 3.14/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/1.02  --res_passive_queues_freq               [15;5]
% 3.14/1.02  --res_forward_subs                      full
% 3.14/1.02  --res_backward_subs                     full
% 3.14/1.02  --res_forward_subs_resolution           true
% 3.14/1.02  --res_backward_subs_resolution          true
% 3.14/1.02  --res_orphan_elimination                true
% 3.14/1.02  --res_time_limit                        2.
% 3.14/1.02  --res_out_proof                         true
% 3.14/1.02  
% 3.14/1.02  ------ Superposition Options
% 3.14/1.02  
% 3.14/1.02  --superposition_flag                    true
% 3.14/1.02  --sup_passive_queue_type                priority_queues
% 3.14/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.14/1.02  --demod_completeness_check              fast
% 3.14/1.02  --demod_use_ground                      true
% 3.14/1.02  --sup_to_prop_solver                    passive
% 3.14/1.02  --sup_prop_simpl_new                    true
% 3.14/1.02  --sup_prop_simpl_given                  true
% 3.14/1.02  --sup_fun_splitting                     false
% 3.14/1.02  --sup_smt_interval                      50000
% 3.14/1.02  
% 3.14/1.02  ------ Superposition Simplification Setup
% 3.14/1.02  
% 3.14/1.02  --sup_indices_passive                   []
% 3.14/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.02  --sup_full_bw                           [BwDemod]
% 3.14/1.02  --sup_immed_triv                        [TrivRules]
% 3.14/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.02  --sup_immed_bw_main                     []
% 3.14/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/1.02  
% 3.14/1.02  ------ Combination Options
% 3.14/1.02  
% 3.14/1.02  --comb_res_mult                         3
% 3.14/1.02  --comb_sup_mult                         2
% 3.14/1.02  --comb_inst_mult                        10
% 3.14/1.02  
% 3.14/1.02  ------ Debug Options
% 3.14/1.02  
% 3.14/1.02  --dbg_backtrace                         false
% 3.14/1.02  --dbg_dump_prop_clauses                 false
% 3.14/1.02  --dbg_dump_prop_clauses_file            -
% 3.14/1.02  --dbg_out_stat                          false
% 3.14/1.02  
% 3.14/1.02  
% 3.14/1.02  
% 3.14/1.02  
% 3.14/1.02  ------ Proving...
% 3.14/1.02  
% 3.14/1.02  
% 3.14/1.02  % SZS status Theorem for theBenchmark.p
% 3.14/1.02  
% 3.14/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.14/1.02  
% 3.14/1.02  fof(f2,axiom,(
% 3.14/1.02    v1_xboole_0(k1_xboole_0)),
% 3.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f45,plain,(
% 3.14/1.02    v1_xboole_0(k1_xboole_0)),
% 3.14/1.02    inference(cnf_transformation,[],[f2])).
% 3.14/1.02  
% 3.14/1.02  fof(f6,axiom,(
% 3.14/1.02    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f15,plain,(
% 3.14/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.14/1.02    inference(ennf_transformation,[],[f6])).
% 3.14/1.02  
% 3.14/1.02  fof(f54,plain,(
% 3.14/1.02    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.14/1.02    inference(cnf_transformation,[],[f15])).
% 3.14/1.02  
% 3.14/1.02  fof(f5,axiom,(
% 3.14/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f34,plain,(
% 3.14/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.14/1.02    inference(nnf_transformation,[],[f5])).
% 3.14/1.02  
% 3.14/1.02  fof(f53,plain,(
% 3.14/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.14/1.02    inference(cnf_transformation,[],[f34])).
% 3.14/1.02  
% 3.14/1.02  fof(f11,axiom,(
% 3.14/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f22,plain,(
% 3.14/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.02    inference(ennf_transformation,[],[f11])).
% 3.14/1.02  
% 3.14/1.02  fof(f23,plain,(
% 3.14/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.02    inference(flattening,[],[f22])).
% 3.14/1.02  
% 3.14/1.02  fof(f38,plain,(
% 3.14/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.02    inference(nnf_transformation,[],[f23])).
% 3.14/1.02  
% 3.14/1.02  fof(f61,plain,(
% 3.14/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.02    inference(cnf_transformation,[],[f38])).
% 3.14/1.02  
% 3.14/1.02  fof(f12,conjecture,(
% 3.14/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f13,negated_conjecture,(
% 3.14/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.14/1.02    inference(negated_conjecture,[],[f12])).
% 3.14/1.02  
% 3.14/1.02  fof(f24,plain,(
% 3.14/1.02    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.14/1.02    inference(ennf_transformation,[],[f13])).
% 3.14/1.02  
% 3.14/1.02  fof(f25,plain,(
% 3.14/1.02    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.14/1.02    inference(flattening,[],[f24])).
% 3.14/1.02  
% 3.14/1.02  fof(f40,plain,(
% 3.14/1.02    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK5) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 3.14/1.02    introduced(choice_axiom,[])).
% 3.14/1.02  
% 3.14/1.02  fof(f39,plain,(
% 3.14/1.02    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.14/1.02    introduced(choice_axiom,[])).
% 3.14/1.02  
% 3.14/1.02  fof(f41,plain,(
% 3.14/1.02    (~r2_relset_1(sK2,sK3,sK4,sK5) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.14/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f40,f39])).
% 3.14/1.02  
% 3.14/1.02  fof(f71,plain,(
% 3.14/1.02    v1_funct_2(sK5,sK2,sK3)),
% 3.14/1.02    inference(cnf_transformation,[],[f41])).
% 3.14/1.02  
% 3.14/1.02  fof(f72,plain,(
% 3.14/1.02    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.14/1.02    inference(cnf_transformation,[],[f41])).
% 3.14/1.02  
% 3.14/1.02  fof(f9,axiom,(
% 3.14/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f19,plain,(
% 3.14/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.02    inference(ennf_transformation,[],[f9])).
% 3.14/1.02  
% 3.14/1.02  fof(f58,plain,(
% 3.14/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.02    inference(cnf_transformation,[],[f19])).
% 3.14/1.02  
% 3.14/1.02  fof(f68,plain,(
% 3.14/1.02    v1_funct_2(sK4,sK2,sK3)),
% 3.14/1.02    inference(cnf_transformation,[],[f41])).
% 3.14/1.02  
% 3.14/1.02  fof(f69,plain,(
% 3.14/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.14/1.02    inference(cnf_transformation,[],[f41])).
% 3.14/1.02  
% 3.14/1.02  fof(f7,axiom,(
% 3.14/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 3.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f16,plain,(
% 3.14/1.02    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.14/1.02    inference(ennf_transformation,[],[f7])).
% 3.14/1.02  
% 3.14/1.02  fof(f17,plain,(
% 3.14/1.02    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/1.02    inference(flattening,[],[f16])).
% 3.14/1.02  
% 3.14/1.02  fof(f35,plain,(
% 3.14/1.02    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 3.14/1.02    introduced(choice_axiom,[])).
% 3.14/1.02  
% 3.14/1.02  fof(f36,plain,(
% 3.14/1.02    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f35])).
% 3.14/1.02  
% 3.14/1.02  fof(f55,plain,(
% 3.14/1.02    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/1.02    inference(cnf_transformation,[],[f36])).
% 3.14/1.02  
% 3.14/1.02  fof(f70,plain,(
% 3.14/1.02    v1_funct_1(sK5)),
% 3.14/1.02    inference(cnf_transformation,[],[f41])).
% 3.14/1.02  
% 3.14/1.02  fof(f8,axiom,(
% 3.14/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f18,plain,(
% 3.14/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.02    inference(ennf_transformation,[],[f8])).
% 3.14/1.02  
% 3.14/1.02  fof(f57,plain,(
% 3.14/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.02    inference(cnf_transformation,[],[f18])).
% 3.14/1.02  
% 3.14/1.02  fof(f67,plain,(
% 3.14/1.02    v1_funct_1(sK4)),
% 3.14/1.02    inference(cnf_transformation,[],[f41])).
% 3.14/1.02  
% 3.14/1.02  fof(f10,axiom,(
% 3.14/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f20,plain,(
% 3.14/1.02    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.14/1.02    inference(ennf_transformation,[],[f10])).
% 3.14/1.02  
% 3.14/1.02  fof(f21,plain,(
% 3.14/1.02    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.02    inference(flattening,[],[f20])).
% 3.14/1.02  
% 3.14/1.02  fof(f37,plain,(
% 3.14/1.02    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.02    inference(nnf_transformation,[],[f21])).
% 3.14/1.02  
% 3.14/1.02  fof(f60,plain,(
% 3.14/1.02    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.02    inference(cnf_transformation,[],[f37])).
% 3.14/1.02  
% 3.14/1.02  fof(f79,plain,(
% 3.14/1.02    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.02    inference(equality_resolution,[],[f60])).
% 3.14/1.02  
% 3.14/1.02  fof(f74,plain,(
% 3.14/1.02    ~r2_relset_1(sK2,sK3,sK4,sK5)),
% 3.14/1.02    inference(cnf_transformation,[],[f41])).
% 3.14/1.02  
% 3.14/1.02  fof(f3,axiom,(
% 3.14/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f30,plain,(
% 3.14/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.14/1.02    inference(nnf_transformation,[],[f3])).
% 3.14/1.02  
% 3.14/1.02  fof(f31,plain,(
% 3.14/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.14/1.02    inference(flattening,[],[f30])).
% 3.14/1.02  
% 3.14/1.02  fof(f48,plain,(
% 3.14/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.14/1.02    inference(cnf_transformation,[],[f31])).
% 3.14/1.02  
% 3.14/1.02  fof(f46,plain,(
% 3.14/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.14/1.02    inference(cnf_transformation,[],[f31])).
% 3.14/1.02  
% 3.14/1.02  fof(f76,plain,(
% 3.14/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.14/1.02    inference(equality_resolution,[],[f46])).
% 3.14/1.02  
% 3.14/1.02  fof(f73,plain,(
% 3.14/1.02    ( ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK2)) )),
% 3.14/1.02    inference(cnf_transformation,[],[f41])).
% 3.14/1.02  
% 3.14/1.02  fof(f56,plain,(
% 3.14/1.02    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/1.02    inference(cnf_transformation,[],[f36])).
% 3.14/1.02  
% 3.14/1.02  fof(f4,axiom,(
% 3.14/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f32,plain,(
% 3.14/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.14/1.02    inference(nnf_transformation,[],[f4])).
% 3.14/1.02  
% 3.14/1.02  fof(f33,plain,(
% 3.14/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.14/1.02    inference(flattening,[],[f32])).
% 3.14/1.02  
% 3.14/1.02  fof(f51,plain,(
% 3.14/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.14/1.02    inference(cnf_transformation,[],[f33])).
% 3.14/1.02  
% 3.14/1.02  fof(f77,plain,(
% 3.14/1.02    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.14/1.02    inference(equality_resolution,[],[f51])).
% 3.14/1.02  
% 3.14/1.02  fof(f52,plain,(
% 3.14/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.14/1.02    inference(cnf_transformation,[],[f34])).
% 3.14/1.02  
% 3.14/1.02  fof(f1,axiom,(
% 3.14/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.14/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.02  
% 3.14/1.02  fof(f14,plain,(
% 3.14/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.14/1.02    inference(ennf_transformation,[],[f1])).
% 3.14/1.02  
% 3.14/1.02  fof(f26,plain,(
% 3.14/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.14/1.02    inference(nnf_transformation,[],[f14])).
% 3.14/1.02  
% 3.14/1.02  fof(f27,plain,(
% 3.14/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.14/1.02    inference(rectify,[],[f26])).
% 3.14/1.02  
% 3.14/1.02  fof(f28,plain,(
% 3.14/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.14/1.02    introduced(choice_axiom,[])).
% 3.14/1.02  
% 3.14/1.02  fof(f29,plain,(
% 3.14/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.14/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.14/1.02  
% 3.14/1.02  fof(f43,plain,(
% 3.14/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.14/1.02    inference(cnf_transformation,[],[f29])).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3,plain,
% 3.14/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 3.14/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_12,plain,
% 3.14/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.14/1.02      | ~ r2_hidden(X2,X0)
% 3.14/1.02      | ~ v1_xboole_0(X1) ),
% 3.14/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_10,plain,
% 3.14/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.14/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_230,plain,
% 3.14/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.14/1.02      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_231,plain,
% 3.14/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.14/1.02      inference(renaming,[status(thm)],[c_230]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_294,plain,
% 3.14/1.02      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 3.14/1.02      inference(bin_hyper_res,[status(thm)],[c_12,c_231]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_397,plain,
% 3.14/1.02      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | k1_xboole_0 != X2 ),
% 3.14/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_294]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_398,plain,
% 3.14/1.02      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) ),
% 3.14/1.02      inference(unflattening,[status(thm)],[c_397]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4682,plain,
% 3.14/1.02      ( ~ r2_hidden(sK0(X0,sK5),X0) | ~ r1_tarski(X0,k1_xboole_0) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_398]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4684,plain,
% 3.14/1.02      ( ~ r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0)
% 3.14/1.02      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_4682]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_24,plain,
% 3.14/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.14/1.02      | k1_xboole_0 = X2 ),
% 3.14/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_28,negated_conjecture,
% 3.14/1.02      ( v1_funct_2(sK5,sK2,sK3) ),
% 3.14/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_497,plain,
% 3.14/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.14/1.02      | sK5 != X0
% 3.14/1.02      | sK3 != X2
% 3.14/1.02      | sK2 != X1
% 3.14/1.02      | k1_xboole_0 = X2 ),
% 3.14/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_498,plain,
% 3.14/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.14/1.02      | k1_relset_1(sK2,sK3,sK5) = sK2
% 3.14/1.02      | k1_xboole_0 = sK3 ),
% 3.14/1.02      inference(unflattening,[status(thm)],[c_497]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_27,negated_conjecture,
% 3.14/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.14/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_500,plain,
% 3.14/1.02      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 3.14/1.02      inference(global_propositional_subsumption,
% 3.14/1.02                [status(thm)],
% 3.14/1.02                [c_498,c_27]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1989,plain,
% 3.14/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_16,plain,
% 3.14/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.14/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1991,plain,
% 3.14/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.14/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2830,plain,
% 3.14/1.02      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 3.14/1.02      inference(superposition,[status(thm)],[c_1989,c_1991]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3070,plain,
% 3.14/1.02      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 3.14/1.02      inference(superposition,[status(thm)],[c_500,c_2830]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_31,negated_conjecture,
% 3.14/1.02      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.14/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_508,plain,
% 3.14/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.14/1.02      | sK4 != X0
% 3.14/1.02      | sK3 != X2
% 3.14/1.02      | sK2 != X1
% 3.14/1.02      | k1_xboole_0 = X2 ),
% 3.14/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_509,plain,
% 3.14/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.14/1.02      | k1_relset_1(sK2,sK3,sK4) = sK2
% 3.14/1.02      | k1_xboole_0 = sK3 ),
% 3.14/1.02      inference(unflattening,[status(thm)],[c_508]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_30,negated_conjecture,
% 3.14/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.14/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_511,plain,
% 3.14/1.02      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 3.14/1.02      inference(global_propositional_subsumption,
% 3.14/1.02                [status(thm)],
% 3.14/1.02                [c_509,c_30]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1987,plain,
% 3.14/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2831,plain,
% 3.14/1.02      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.14/1.02      inference(superposition,[status(thm)],[c_1987,c_1991]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3155,plain,
% 3.14/1.02      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.14/1.02      inference(superposition,[status(thm)],[c_511,c_2831]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_14,plain,
% 3.14/1.02      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 3.14/1.02      | ~ v1_relat_1(X1)
% 3.14/1.02      | ~ v1_relat_1(X0)
% 3.14/1.02      | ~ v1_funct_1(X1)
% 3.14/1.02      | ~ v1_funct_1(X0)
% 3.14/1.02      | X1 = X0
% 3.14/1.02      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.14/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1993,plain,
% 3.14/1.02      ( X0 = X1
% 3.14/1.02      | k1_relat_1(X0) != k1_relat_1(X1)
% 3.14/1.02      | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.14/1.02      | v1_relat_1(X1) != iProver_top
% 3.14/1.02      | v1_relat_1(X0) != iProver_top
% 3.14/1.02      | v1_funct_1(X0) != iProver_top
% 3.14/1.02      | v1_funct_1(X1) != iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3305,plain,
% 3.14/1.02      ( k1_relat_1(X0) != sK2
% 3.14/1.02      | sK5 = X0
% 3.14/1.02      | sK3 = k1_xboole_0
% 3.14/1.02      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 3.14/1.02      | v1_relat_1(X0) != iProver_top
% 3.14/1.02      | v1_relat_1(sK5) != iProver_top
% 3.14/1.02      | v1_funct_1(X0) != iProver_top
% 3.14/1.02      | v1_funct_1(sK5) != iProver_top ),
% 3.14/1.02      inference(superposition,[status(thm)],[c_3070,c_1993]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_29,negated_conjecture,
% 3.14/1.02      ( v1_funct_1(sK5) ),
% 3.14/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_36,plain,
% 3.14/1.02      ( v1_funct_1(sK5) = iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_38,plain,
% 3.14/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_15,plain,
% 3.14/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.02      | v1_relat_1(X0) ),
% 3.14/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2190,plain,
% 3.14/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.14/1.02      | v1_relat_1(sK5) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_15]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2191,plain,
% 3.14/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.14/1.02      | v1_relat_1(sK5) = iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_2190]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3885,plain,
% 3.14/1.02      ( v1_funct_1(X0) != iProver_top
% 3.14/1.02      | k1_relat_1(X0) != sK2
% 3.14/1.02      | sK5 = X0
% 3.14/1.02      | sK3 = k1_xboole_0
% 3.14/1.02      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 3.14/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.14/1.02      inference(global_propositional_subsumption,
% 3.14/1.02                [status(thm)],
% 3.14/1.02                [c_3305,c_36,c_38,c_2191]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3886,plain,
% 3.14/1.02      ( k1_relat_1(X0) != sK2
% 3.14/1.02      | sK5 = X0
% 3.14/1.02      | sK3 = k1_xboole_0
% 3.14/1.02      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 3.14/1.02      | v1_relat_1(X0) != iProver_top
% 3.14/1.02      | v1_funct_1(X0) != iProver_top ),
% 3.14/1.02      inference(renaming,[status(thm)],[c_3885]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3898,plain,
% 3.14/1.02      ( sK5 = sK4
% 3.14/1.02      | sK3 = k1_xboole_0
% 3.14/1.02      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
% 3.14/1.02      | v1_relat_1(sK4) != iProver_top
% 3.14/1.02      | v1_funct_1(sK4) != iProver_top ),
% 3.14/1.02      inference(superposition,[status(thm)],[c_3155,c_3886]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_32,negated_conjecture,
% 3.14/1.02      ( v1_funct_1(sK4) ),
% 3.14/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_33,plain,
% 3.14/1.02      ( v1_funct_1(sK4) = iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_35,plain,
% 3.14/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_17,plain,
% 3.14/1.02      ( r2_relset_1(X0,X1,X2,X2)
% 3.14/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.14/1.02      inference(cnf_transformation,[],[f79]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_25,negated_conjecture,
% 3.14/1.02      ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
% 3.14/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_414,plain,
% 3.14/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.02      | sK5 != X0
% 3.14/1.02      | sK4 != X0
% 3.14/1.02      | sK3 != X2
% 3.14/1.02      | sK2 != X1 ),
% 3.14/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_415,plain,
% 3.14/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.14/1.02      | sK4 != sK5 ),
% 3.14/1.02      inference(unflattening,[status(thm)],[c_414]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2193,plain,
% 3.14/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.14/1.02      | v1_relat_1(sK4) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_15]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2194,plain,
% 3.14/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.14/1.02      | v1_relat_1(sK4) = iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_2193]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4,plain,
% 3.14/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.14/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2292,plain,
% 3.14/1.02      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2554,plain,
% 3.14/1.02      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_2292]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_6,plain,
% 3.14/1.02      ( r1_tarski(X0,X0) ),
% 3.14/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2555,plain,
% 3.14/1.02      ( r1_tarski(sK4,sK4) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1449,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2219,plain,
% 3.14/1.02      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_1449]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3627,plain,
% 3.14/1.02      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_2219]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3911,plain,
% 3.14/1.02      ( sK3 = k1_xboole_0
% 3.14/1.02      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
% 3.14/1.02      inference(global_propositional_subsumption,
% 3.14/1.02                [status(thm)],
% 3.14/1.02                [c_3898,c_33,c_35,c_27,c_415,c_2194,c_2554,c_2555,c_3627]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3917,plain,
% 3.14/1.02      ( sK3 = k1_xboole_0 | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
% 3.14/1.02      inference(superposition,[status(thm)],[c_3155,c_3911]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_26,negated_conjecture,
% 3.14/1.02      ( ~ r2_hidden(X0,sK2) | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
% 3.14/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1990,plain,
% 3.14/1.02      ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
% 3.14/1.02      | r2_hidden(X0,sK2) != iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3983,plain,
% 3.14/1.02      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 3.14/1.02      | sK3 = k1_xboole_0 ),
% 3.14/1.02      inference(superposition,[status(thm)],[c_3917,c_1990]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_13,plain,
% 3.14/1.02      ( ~ v1_relat_1(X0)
% 3.14/1.02      | ~ v1_relat_1(X1)
% 3.14/1.02      | ~ v1_funct_1(X0)
% 3.14/1.02      | ~ v1_funct_1(X1)
% 3.14/1.02      | X0 = X1
% 3.14/1.02      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 3.14/1.02      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 3.14/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1994,plain,
% 3.14/1.02      ( X0 = X1
% 3.14/1.02      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 3.14/1.02      | k1_relat_1(X0) != k1_relat_1(X1)
% 3.14/1.02      | v1_relat_1(X0) != iProver_top
% 3.14/1.02      | v1_relat_1(X1) != iProver_top
% 3.14/1.02      | v1_funct_1(X1) != iProver_top
% 3.14/1.02      | v1_funct_1(X0) != iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4086,plain,
% 3.14/1.02      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 3.14/1.02      | sK5 = sK4
% 3.14/1.02      | sK3 = k1_xboole_0
% 3.14/1.02      | v1_relat_1(sK5) != iProver_top
% 3.14/1.02      | v1_relat_1(sK4) != iProver_top
% 3.14/1.02      | v1_funct_1(sK5) != iProver_top
% 3.14/1.02      | v1_funct_1(sK4) != iProver_top ),
% 3.14/1.02      inference(superposition,[status(thm)],[c_3983,c_1994]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4102,plain,
% 3.14/1.02      ( ~ v1_relat_1(sK5)
% 3.14/1.02      | ~ v1_relat_1(sK4)
% 3.14/1.02      | ~ v1_funct_1(sK5)
% 3.14/1.02      | ~ v1_funct_1(sK4)
% 3.14/1.02      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 3.14/1.02      | sK5 = sK4
% 3.14/1.02      | sK3 = k1_xboole_0 ),
% 3.14/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_4086]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4245,plain,
% 3.14/1.02      ( k1_relat_1(sK4) != k1_relat_1(sK5) | sK3 = k1_xboole_0 ),
% 3.14/1.02      inference(global_propositional_subsumption,
% 3.14/1.02                [status(thm)],
% 3.14/1.02                [c_4086,c_32,c_30,c_29,c_27,c_415,c_2190,c_2193,c_2554,
% 3.14/1.02                 c_2555,c_3627,c_4102]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4249,plain,
% 3.14/1.02      ( k1_relat_1(sK4) != sK2 | sK3 = k1_xboole_0 ),
% 3.14/1.02      inference(superposition,[status(thm)],[c_3070,c_4245]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4276,plain,
% 3.14/1.02      ( sK3 = k1_xboole_0 ),
% 3.14/1.02      inference(global_propositional_subsumption,
% 3.14/1.02                [status(thm)],
% 3.14/1.02                [c_4249,c_3155]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4293,plain,
% 3.14/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.14/1.02      inference(demodulation,[status(thm)],[c_4276,c_1989]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_7,plain,
% 3.14/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.14/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4299,plain,
% 3.14/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.14/1.02      inference(demodulation,[status(thm)],[c_4293,c_7]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4348,plain,
% 3.14/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
% 3.14/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_4299]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4294,plain,
% 3.14/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.14/1.02      inference(demodulation,[status(thm)],[c_4276,c_1987]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4296,plain,
% 3.14/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.14/1.02      inference(demodulation,[status(thm)],[c_4294,c_7]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4145,plain,
% 3.14/1.02      ( ~ r2_hidden(sK0(sK5,sK4),sK5) | ~ r1_tarski(sK5,k1_xboole_0) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_398]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4146,plain,
% 3.14/1.02      ( r2_hidden(sK0(sK5,sK4),sK5) != iProver_top
% 3.14/1.02      | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_4145]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1450,plain,
% 3.14/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,X2) | X2 != X1 ),
% 3.14/1.02      theory(equality) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2534,plain,
% 3.14/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,sK5) | sK5 != X1 ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_1450]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3170,plain,
% 3.14/1.02      ( ~ r1_tarski(sK4,X0) | r1_tarski(sK4,sK5) | sK5 != X0 ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_2534]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3171,plain,
% 3.14/1.02      ( sK5 != X0
% 3.14/1.02      | r1_tarski(sK4,X0) != iProver_top
% 3.14/1.02      | r1_tarski(sK4,sK5) = iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_3170]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3173,plain,
% 3.14/1.02      ( sK5 != k1_xboole_0
% 3.14/1.02      | r1_tarski(sK4,sK5) = iProver_top
% 3.14/1.02      | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_3171]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2466,plain,
% 3.14/1.02      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_1449]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3143,plain,
% 3.14/1.02      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_2466]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3145,plain,
% 3.14/1.02      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_3143]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_11,plain,
% 3.14/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.14/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2892,plain,
% 3.14/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2893,plain,
% 3.14/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.14/1.02      | r1_tarski(sK4,X0) = iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_2892]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2895,plain,
% 3.14/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.14/1.02      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_2893]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2859,plain,
% 3.14/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0)) | r1_tarski(sK5,X0) ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2860,plain,
% 3.14/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 3.14/1.02      | r1_tarski(sK5,X0) = iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_2859]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2862,plain,
% 3.14/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.14/1.02      | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 3.14/1.02      inference(instantiation,[status(thm)],[c_2860]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2861,plain,
% 3.14/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
% 3.14/1.03      | r1_tarski(sK5,k1_xboole_0) ),
% 3.14/1.03      inference(instantiation,[status(thm)],[c_2859]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_2529,plain,
% 3.14/1.03      ( r1_tarski(sK5,sK5) ),
% 3.14/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_2270,plain,
% 3.14/1.03      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | X0 = sK5 ),
% 3.14/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_2528,plain,
% 3.14/1.03      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 3.14/1.03      inference(instantiation,[status(thm)],[c_2270]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1,plain,
% 3.14/1.03      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.14/1.03      inference(cnf_transformation,[],[f43]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_2513,plain,
% 3.14/1.03      ( r2_hidden(sK0(X0,sK5),X0) | r1_tarski(X0,sK5) ),
% 3.14/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_2525,plain,
% 3.14/1.03      ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0)
% 3.14/1.03      | r1_tarski(k1_xboole_0,sK5) ),
% 3.14/1.03      inference(instantiation,[status(thm)],[c_2513]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_2308,plain,
% 3.14/1.03      ( r2_hidden(sK0(sK5,sK4),sK5) | r1_tarski(sK5,sK4) ),
% 3.14/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_2315,plain,
% 3.14/1.03      ( r2_hidden(sK0(sK5,sK4),sK5) = iProver_top
% 3.14/1.03      | r1_tarski(sK5,sK4) = iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_2308]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_2272,plain,
% 3.14/1.03      ( ~ r1_tarski(sK5,k1_xboole_0)
% 3.14/1.03      | ~ r1_tarski(k1_xboole_0,sK5)
% 3.14/1.03      | k1_xboole_0 = sK5 ),
% 3.14/1.03      inference(instantiation,[status(thm)],[c_2270]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_2210,plain,
% 3.14/1.03      ( ~ r1_tarski(sK5,sK4) | ~ r1_tarski(sK4,sK5) | sK4 = sK5 ),
% 3.14/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_2211,plain,
% 3.14/1.03      ( sK4 = sK5
% 3.14/1.03      | r1_tarski(sK5,sK4) != iProver_top
% 3.14/1.03      | r1_tarski(sK4,sK5) != iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_2210]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_91,plain,
% 3.14/1.03      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.14/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(contradiction,plain,
% 3.14/1.03      ( $false ),
% 3.14/1.03      inference(minisat,
% 3.14/1.03                [status(thm)],
% 3.14/1.03                [c_4684,c_4348,c_4299,c_4296,c_4146,c_3173,c_3145,c_2895,
% 3.14/1.03                 c_2862,c_2861,c_2529,c_2528,c_2525,c_2315,c_2272,c_2211,
% 3.14/1.03                 c_415,c_91,c_27]) ).
% 3.14/1.03  
% 3.14/1.03  
% 3.14/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.14/1.03  
% 3.14/1.03  ------                               Statistics
% 3.14/1.03  
% 3.14/1.03  ------ General
% 3.14/1.03  
% 3.14/1.03  abstr_ref_over_cycles:                  0
% 3.14/1.03  abstr_ref_under_cycles:                 0
% 3.14/1.03  gc_basic_clause_elim:                   0
% 3.14/1.03  forced_gc_time:                         0
% 3.14/1.03  parsing_time:                           0.01
% 3.14/1.03  unif_index_cands_time:                  0.
% 3.14/1.03  unif_index_add_time:                    0.
% 3.14/1.03  orderings_time:                         0.
% 3.14/1.03  out_proof_time:                         0.01
% 3.14/1.03  total_time:                             0.146
% 3.14/1.03  num_of_symbols:                         51
% 3.14/1.03  num_of_terms:                           3321
% 3.14/1.03  
% 3.14/1.03  ------ Preprocessing
% 3.14/1.03  
% 3.14/1.03  num_of_splits:                          0
% 3.14/1.03  num_of_split_atoms:                     0
% 3.14/1.03  num_of_reused_defs:                     0
% 3.14/1.03  num_eq_ax_congr_red:                    24
% 3.14/1.03  num_of_sem_filtered_clauses:            1
% 3.14/1.03  num_of_subtypes:                        0
% 3.14/1.03  monotx_restored_types:                  0
% 3.14/1.03  sat_num_of_epr_types:                   0
% 3.14/1.03  sat_num_of_non_cyclic_types:            0
% 3.14/1.03  sat_guarded_non_collapsed_types:        0
% 3.14/1.03  num_pure_diseq_elim:                    0
% 3.14/1.03  simp_replaced_by:                       0
% 3.14/1.03  res_preprocessed:                       134
% 3.14/1.03  prep_upred:                             0
% 3.14/1.03  prep_unflattend:                        66
% 3.14/1.03  smt_new_axioms:                         0
% 3.14/1.03  pred_elim_cands:                        5
% 3.14/1.03  pred_elim:                              3
% 3.14/1.03  pred_elim_cl:                           5
% 3.14/1.03  pred_elim_cycles:                       5
% 3.14/1.03  merged_defs:                            8
% 3.14/1.03  merged_defs_ncl:                        0
% 3.14/1.03  bin_hyper_res:                          9
% 3.14/1.03  prep_cycles:                            4
% 3.14/1.03  pred_elim_time:                         0.014
% 3.14/1.03  splitting_time:                         0.
% 3.14/1.03  sem_filter_time:                        0.
% 3.14/1.03  monotx_time:                            0.001
% 3.14/1.03  subtype_inf_time:                       0.
% 3.14/1.03  
% 3.14/1.03  ------ Problem properties
% 3.14/1.03  
% 3.14/1.03  clauses:                                27
% 3.14/1.03  conjectures:                            5
% 3.14/1.03  epr:                                    7
% 3.14/1.03  horn:                                   20
% 3.14/1.03  ground:                                 11
% 3.14/1.03  unary:                                  8
% 3.14/1.03  binary:                                 10
% 3.14/1.03  lits:                                   65
% 3.14/1.03  lits_eq:                                28
% 3.14/1.03  fd_pure:                                0
% 3.14/1.03  fd_pseudo:                              0
% 3.14/1.03  fd_cond:                                1
% 3.14/1.03  fd_pseudo_cond:                         3
% 3.14/1.03  ac_symbols:                             0
% 3.14/1.03  
% 3.14/1.03  ------ Propositional Solver
% 3.14/1.03  
% 3.14/1.03  prop_solver_calls:                      27
% 3.14/1.03  prop_fast_solver_calls:                 993
% 3.14/1.03  smt_solver_calls:                       0
% 3.14/1.03  smt_fast_solver_calls:                  0
% 3.14/1.03  prop_num_of_clauses:                    1330
% 3.14/1.03  prop_preprocess_simplified:             4773
% 3.14/1.03  prop_fo_subsumed:                       21
% 3.14/1.03  prop_solver_time:                       0.
% 3.14/1.03  smt_solver_time:                        0.
% 3.14/1.03  smt_fast_solver_time:                   0.
% 3.14/1.03  prop_fast_solver_time:                  0.
% 3.14/1.03  prop_unsat_core_time:                   0.
% 3.14/1.03  
% 3.14/1.03  ------ QBF
% 3.14/1.03  
% 3.14/1.03  qbf_q_res:                              0
% 3.14/1.03  qbf_num_tautologies:                    0
% 3.14/1.03  qbf_prep_cycles:                        0
% 3.14/1.03  
% 3.14/1.03  ------ BMC1
% 3.14/1.03  
% 3.14/1.03  bmc1_current_bound:                     -1
% 3.14/1.03  bmc1_last_solved_bound:                 -1
% 3.14/1.03  bmc1_unsat_core_size:                   -1
% 3.14/1.03  bmc1_unsat_core_parents_size:           -1
% 3.14/1.03  bmc1_merge_next_fun:                    0
% 3.14/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.14/1.03  
% 3.14/1.03  ------ Instantiation
% 3.14/1.03  
% 3.14/1.03  inst_num_of_clauses:                    403
% 3.14/1.03  inst_num_in_passive:                    109
% 3.14/1.03  inst_num_in_active:                     212
% 3.14/1.03  inst_num_in_unprocessed:                81
% 3.14/1.03  inst_num_of_loops:                      298
% 3.14/1.03  inst_num_of_learning_restarts:          0
% 3.14/1.03  inst_num_moves_active_passive:          82
% 3.14/1.03  inst_lit_activity:                      0
% 3.14/1.03  inst_lit_activity_moves:                0
% 3.14/1.03  inst_num_tautologies:                   0
% 3.14/1.03  inst_num_prop_implied:                  0
% 3.14/1.03  inst_num_existing_simplified:           0
% 3.14/1.03  inst_num_eq_res_simplified:             0
% 3.14/1.03  inst_num_child_elim:                    0
% 3.14/1.03  inst_num_of_dismatching_blockings:      110
% 3.14/1.03  inst_num_of_non_proper_insts:           445
% 3.14/1.03  inst_num_of_duplicates:                 0
% 3.14/1.03  inst_inst_num_from_inst_to_res:         0
% 3.14/1.03  inst_dismatching_checking_time:         0.
% 3.14/1.03  
% 3.14/1.03  ------ Resolution
% 3.14/1.03  
% 3.14/1.03  res_num_of_clauses:                     0
% 3.14/1.03  res_num_in_passive:                     0
% 3.14/1.03  res_num_in_active:                      0
% 3.14/1.03  res_num_of_loops:                       138
% 3.14/1.03  res_forward_subset_subsumed:            38
% 3.14/1.03  res_backward_subset_subsumed:           0
% 3.14/1.03  res_forward_subsumed:                   0
% 3.14/1.03  res_backward_subsumed:                  0
% 3.14/1.03  res_forward_subsumption_resolution:     0
% 3.14/1.03  res_backward_subsumption_resolution:    0
% 3.14/1.03  res_clause_to_clause_subsumption:       244
% 3.14/1.03  res_orphan_elimination:                 0
% 3.14/1.03  res_tautology_del:                      50
% 3.14/1.03  res_num_eq_res_simplified:              0
% 3.14/1.03  res_num_sel_changes:                    0
% 3.14/1.03  res_moves_from_active_to_pass:          0
% 3.14/1.03  
% 3.14/1.03  ------ Superposition
% 3.14/1.03  
% 3.14/1.03  sup_time_total:                         0.
% 3.14/1.03  sup_time_generating:                    0.
% 3.14/1.03  sup_time_sim_full:                      0.
% 3.14/1.03  sup_time_sim_immed:                     0.
% 3.14/1.03  
% 3.14/1.03  sup_num_of_clauses:                     66
% 3.14/1.03  sup_num_in_active:                      40
% 3.14/1.03  sup_num_in_passive:                     26
% 3.14/1.03  sup_num_of_loops:                       58
% 3.14/1.03  sup_fw_superposition:                   47
% 3.14/1.03  sup_bw_superposition:                   20
% 3.14/1.03  sup_immediate_simplified:               10
% 3.14/1.03  sup_given_eliminated:                   0
% 3.14/1.03  comparisons_done:                       0
% 3.14/1.03  comparisons_avoided:                    11
% 3.14/1.03  
% 3.14/1.03  ------ Simplifications
% 3.14/1.03  
% 3.14/1.03  
% 3.14/1.03  sim_fw_subset_subsumed:                 0
% 3.14/1.03  sim_bw_subset_subsumed:                 6
% 3.14/1.03  sim_fw_subsumed:                        0
% 3.14/1.03  sim_bw_subsumed:                        0
% 3.14/1.03  sim_fw_subsumption_res:                 4
% 3.14/1.03  sim_bw_subsumption_res:                 0
% 3.14/1.03  sim_tautology_del:                      1
% 3.14/1.03  sim_eq_tautology_del:                   10
% 3.14/1.03  sim_eq_res_simp:                        2
% 3.14/1.03  sim_fw_demodulated:                     10
% 3.14/1.03  sim_bw_demodulated:                     16
% 3.14/1.03  sim_light_normalised:                   0
% 3.14/1.03  sim_joinable_taut:                      0
% 3.14/1.03  sim_joinable_simp:                      0
% 3.14/1.03  sim_ac_normalised:                      0
% 3.14/1.03  sim_smt_subsumption:                    0
% 3.14/1.03  
%------------------------------------------------------------------------------
