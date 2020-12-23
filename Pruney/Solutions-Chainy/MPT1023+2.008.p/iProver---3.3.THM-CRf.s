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
% DateTime   : Thu Dec  3 12:07:42 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  203 (7533 expanded)
%              Number of clauses        :  134 (2251 expanded)
%              Number of leaves         :   18 (1819 expanded)
%              Depth                    :   31
%              Number of atoms          :  660 (48121 expanded)
%              Number of equality atoms :  339 (11636 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f41,f40])).

fof(f71,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f42])).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f36])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f74,plain,(
    ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_499,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_501,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_26])).

cnf(c_2506,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2508,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3310,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2506,c_2508])).

cnf(c_3403,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_501,c_3310])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_509,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_510,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_512,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_29])).

cnf(c_2504,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3311,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2504,c_2508])).

cnf(c_3489,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_512,c_3311])).

cnf(c_12,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2511,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3709,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3403,c_2511])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2716,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2717,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2716])).

cnf(c_4067,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3709,c_35,c_37,c_2717])).

cnf(c_4068,plain,
    ( k1_relat_1(X0) != sK2
    | sK5 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4067])).

cnf(c_4080,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3489,c_4068])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_32,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_16,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_24,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != X0
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_416,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_2719,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2720,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2719])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2814,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3019,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2814])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3020,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1926,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2745,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1926])).

cnf(c_3357,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2745])).

cnf(c_4093,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4080,c_32,c_34,c_26,c_416,c_2720,c_3019,c_3020,c_3357])).

cnf(c_4099,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3489,c_4093])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2515,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4207,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK1(sK4,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4099,c_2515])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2507,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4668,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4207,c_2507])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2512,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4691,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4668,c_2512])).

cnf(c_4692,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4691])).

cnf(c_4702,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4691,c_31,c_29,c_28,c_26,c_416,c_2716,c_2719,c_3019,c_3020,c_3357,c_4692])).

cnf(c_4706,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3403,c_4702])).

cnf(c_4729,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4706,c_3489])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_452,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK4 != X0
    | sK3 != k1_xboole_0
    | sK2 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_453,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_2500,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK2
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_4744,plain,
    ( sK4 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4729,c_2500])).

cnf(c_4773,plain,
    ( sK4 = k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4744])).

cnf(c_4752,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4729,c_2504])).

cnf(c_4777,plain,
    ( sK4 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4773,c_4752])).

cnf(c_2824,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_1926])).

cnf(c_3356,plain,
    ( sK5 != X0
    | sK5 = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2824])).

cnf(c_3358,plain,
    ( sK5 = sK4
    | sK5 != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3356])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK5 != X0
    | sK3 != k1_xboole_0
    | sK2 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_437,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_2501,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK2
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_4743,plain,
    ( sK5 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4729,c_2501])).

cnf(c_4780,plain,
    ( sK5 = k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4743])).

cnf(c_4751,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4729,c_2506])).

cnf(c_4784,plain,
    ( sK5 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4780,c_4751])).

cnf(c_5744,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4777,c_26,c_416,c_3019,c_3020,c_3358,c_3357,c_4784])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2513,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3084,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2504,c_2513])).

cnf(c_4746,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4729,c_3084])).

cnf(c_5748,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5744,c_4746])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2520,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_240,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_241,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_240])).

cnf(c_304,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_241])).

cnf(c_2502,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_6693,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2520,c_2502])).

cnf(c_6701,plain,
    ( r1_tarski(sK4,X0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5748,c_6693])).

cnf(c_6733,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6701])).

cnf(c_3083,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2506,c_2513])).

cnf(c_4747,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4729,c_3083])).

cnf(c_5747,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5744,c_4747])).

cnf(c_6700,plain,
    ( r1_tarski(sK5,X0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5747,c_6693])).

cnf(c_6730,plain,
    ( r1_tarski(sK5,k1_xboole_0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6700])).

cnf(c_2516,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2514,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2509,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3604,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2514,c_2509])).

cnf(c_5789,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2516,c_3604])).

cnf(c_5796,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5789])).

cnf(c_4548,plain,
    ( ~ r2_hidden(sK0(X0,sK4),X0)
    | ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_4559,plain,
    ( r2_hidden(sK0(X0,sK4),X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4548])).

cnf(c_4561,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4559])).

cnf(c_3453,plain,
    ( ~ r2_hidden(sK0(X0,sK5),X0)
    | ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_3464,plain,
    ( r2_hidden(sK0(X0,sK5),X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3453])).

cnf(c_3466,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3464])).

cnf(c_3041,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3042,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3041])).

cnf(c_3044,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3042])).

cnf(c_3004,plain,
    ( r2_hidden(sK0(X0,sK4),X0)
    | r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3015,plain,
    ( r2_hidden(sK0(X0,sK4),X0) = iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3004])).

cnf(c_3017,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3015])).

cnf(c_2983,plain,
    ( r2_hidden(sK0(X0,sK5),X0)
    | r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2994,plain,
    ( r2_hidden(sK0(X0,sK5),X0) = iProver_top
    | r1_tarski(X0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2983])).

cnf(c_2996,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2994])).

cnf(c_2948,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2949,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2948])).

cnf(c_2951,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2949])).

cnf(c_2746,plain,
    ( sK5 != k1_xboole_0
    | sK4 = sK5
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2745])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_98,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_91,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_93,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_91])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6733,c_6730,c_5796,c_4561,c_3466,c_3044,c_3017,c_2996,c_2951,c_2746,c_416,c_98,c_93,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:20:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.07/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/0.98  
% 3.07/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.07/0.98  
% 3.07/0.98  ------  iProver source info
% 3.07/0.98  
% 3.07/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.07/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.07/0.98  git: non_committed_changes: false
% 3.07/0.98  git: last_make_outside_of_git: false
% 3.07/0.98  
% 3.07/0.98  ------ 
% 3.07/0.98  
% 3.07/0.98  ------ Input Options
% 3.07/0.98  
% 3.07/0.98  --out_options                           all
% 3.07/0.98  --tptp_safe_out                         true
% 3.07/0.98  --problem_path                          ""
% 3.07/0.98  --include_path                          ""
% 3.07/0.98  --clausifier                            res/vclausify_rel
% 3.07/0.98  --clausifier_options                    --mode clausify
% 3.07/0.98  --stdin                                 false
% 3.07/0.98  --stats_out                             all
% 3.07/0.98  
% 3.07/0.98  ------ General Options
% 3.07/0.98  
% 3.07/0.98  --fof                                   false
% 3.07/0.98  --time_out_real                         305.
% 3.07/0.98  --time_out_virtual                      -1.
% 3.07/0.98  --symbol_type_check                     false
% 3.07/0.98  --clausify_out                          false
% 3.07/0.98  --sig_cnt_out                           false
% 3.07/0.98  --trig_cnt_out                          false
% 3.07/0.98  --trig_cnt_out_tolerance                1.
% 3.07/0.98  --trig_cnt_out_sk_spl                   false
% 3.07/0.98  --abstr_cl_out                          false
% 3.07/0.98  
% 3.07/0.98  ------ Global Options
% 3.07/0.98  
% 3.07/0.98  --schedule                              default
% 3.07/0.98  --add_important_lit                     false
% 3.07/0.98  --prop_solver_per_cl                    1000
% 3.07/0.98  --min_unsat_core                        false
% 3.07/0.98  --soft_assumptions                      false
% 3.07/0.98  --soft_lemma_size                       3
% 3.07/0.98  --prop_impl_unit_size                   0
% 3.07/0.98  --prop_impl_unit                        []
% 3.07/0.98  --share_sel_clauses                     true
% 3.07/0.98  --reset_solvers                         false
% 3.07/0.98  --bc_imp_inh                            [conj_cone]
% 3.07/0.98  --conj_cone_tolerance                   3.
% 3.07/0.98  --extra_neg_conj                        none
% 3.07/0.98  --large_theory_mode                     true
% 3.07/0.98  --prolific_symb_bound                   200
% 3.07/0.98  --lt_threshold                          2000
% 3.07/0.98  --clause_weak_htbl                      true
% 3.07/0.98  --gc_record_bc_elim                     false
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing Options
% 3.07/0.98  
% 3.07/0.98  --preprocessing_flag                    true
% 3.07/0.98  --time_out_prep_mult                    0.1
% 3.07/0.98  --splitting_mode                        input
% 3.07/0.98  --splitting_grd                         true
% 3.07/0.98  --splitting_cvd                         false
% 3.07/0.98  --splitting_cvd_svl                     false
% 3.07/0.98  --splitting_nvd                         32
% 3.07/0.98  --sub_typing                            true
% 3.07/0.98  --prep_gs_sim                           true
% 3.07/0.98  --prep_unflatten                        true
% 3.07/0.98  --prep_res_sim                          true
% 3.07/0.98  --prep_upred                            true
% 3.07/0.98  --prep_sem_filter                       exhaustive
% 3.07/0.98  --prep_sem_filter_out                   false
% 3.07/0.98  --pred_elim                             true
% 3.07/0.98  --res_sim_input                         true
% 3.07/0.98  --eq_ax_congr_red                       true
% 3.07/0.98  --pure_diseq_elim                       true
% 3.07/0.98  --brand_transform                       false
% 3.07/0.98  --non_eq_to_eq                          false
% 3.07/0.98  --prep_def_merge                        true
% 3.07/0.98  --prep_def_merge_prop_impl              false
% 3.07/0.98  --prep_def_merge_mbd                    true
% 3.07/0.98  --prep_def_merge_tr_red                 false
% 3.07/0.98  --prep_def_merge_tr_cl                  false
% 3.07/0.98  --smt_preprocessing                     true
% 3.07/0.98  --smt_ac_axioms                         fast
% 3.07/0.98  --preprocessed_out                      false
% 3.07/0.98  --preprocessed_stats                    false
% 3.07/0.98  
% 3.07/0.98  ------ Abstraction refinement Options
% 3.07/0.98  
% 3.07/0.98  --abstr_ref                             []
% 3.07/0.98  --abstr_ref_prep                        false
% 3.07/0.98  --abstr_ref_until_sat                   false
% 3.07/0.98  --abstr_ref_sig_restrict                funpre
% 3.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/0.98  --abstr_ref_under                       []
% 3.07/0.98  
% 3.07/0.98  ------ SAT Options
% 3.07/0.98  
% 3.07/0.98  --sat_mode                              false
% 3.07/0.98  --sat_fm_restart_options                ""
% 3.07/0.98  --sat_gr_def                            false
% 3.07/0.98  --sat_epr_types                         true
% 3.07/0.98  --sat_non_cyclic_types                  false
% 3.07/0.98  --sat_finite_models                     false
% 3.07/0.98  --sat_fm_lemmas                         false
% 3.07/0.98  --sat_fm_prep                           false
% 3.07/0.98  --sat_fm_uc_incr                        true
% 3.07/0.98  --sat_out_model                         small
% 3.07/0.98  --sat_out_clauses                       false
% 3.07/0.98  
% 3.07/0.98  ------ QBF Options
% 3.07/0.98  
% 3.07/0.98  --qbf_mode                              false
% 3.07/0.98  --qbf_elim_univ                         false
% 3.07/0.98  --qbf_dom_inst                          none
% 3.07/0.98  --qbf_dom_pre_inst                      false
% 3.07/0.98  --qbf_sk_in                             false
% 3.07/0.98  --qbf_pred_elim                         true
% 3.07/0.98  --qbf_split                             512
% 3.07/0.98  
% 3.07/0.98  ------ BMC1 Options
% 3.07/0.98  
% 3.07/0.98  --bmc1_incremental                      false
% 3.07/0.98  --bmc1_axioms                           reachable_all
% 3.07/0.98  --bmc1_min_bound                        0
% 3.07/0.98  --bmc1_max_bound                        -1
% 3.07/0.98  --bmc1_max_bound_default                -1
% 3.07/0.98  --bmc1_symbol_reachability              true
% 3.07/0.98  --bmc1_property_lemmas                  false
% 3.07/0.98  --bmc1_k_induction                      false
% 3.07/0.98  --bmc1_non_equiv_states                 false
% 3.07/0.98  --bmc1_deadlock                         false
% 3.07/0.98  --bmc1_ucm                              false
% 3.07/0.98  --bmc1_add_unsat_core                   none
% 3.07/0.98  --bmc1_unsat_core_children              false
% 3.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/0.98  --bmc1_out_stat                         full
% 3.07/0.98  --bmc1_ground_init                      false
% 3.07/0.98  --bmc1_pre_inst_next_state              false
% 3.07/0.98  --bmc1_pre_inst_state                   false
% 3.07/0.98  --bmc1_pre_inst_reach_state             false
% 3.07/0.98  --bmc1_out_unsat_core                   false
% 3.07/0.98  --bmc1_aig_witness_out                  false
% 3.07/0.98  --bmc1_verbose                          false
% 3.07/0.98  --bmc1_dump_clauses_tptp                false
% 3.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.07/0.98  --bmc1_dump_file                        -
% 3.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.07/0.98  --bmc1_ucm_extend_mode                  1
% 3.07/0.98  --bmc1_ucm_init_mode                    2
% 3.07/0.98  --bmc1_ucm_cone_mode                    none
% 3.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.07/0.98  --bmc1_ucm_relax_model                  4
% 3.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/0.98  --bmc1_ucm_layered_model                none
% 3.07/0.98  --bmc1_ucm_max_lemma_size               10
% 3.07/0.98  
% 3.07/0.98  ------ AIG Options
% 3.07/0.98  
% 3.07/0.98  --aig_mode                              false
% 3.07/0.98  
% 3.07/0.98  ------ Instantiation Options
% 3.07/0.98  
% 3.07/0.98  --instantiation_flag                    true
% 3.07/0.98  --inst_sos_flag                         false
% 3.07/0.98  --inst_sos_phase                        true
% 3.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/0.98  --inst_lit_sel_side                     num_symb
% 3.07/0.98  --inst_solver_per_active                1400
% 3.07/0.98  --inst_solver_calls_frac                1.
% 3.07/0.98  --inst_passive_queue_type               priority_queues
% 3.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/0.98  --inst_passive_queues_freq              [25;2]
% 3.07/0.98  --inst_dismatching                      true
% 3.07/0.98  --inst_eager_unprocessed_to_passive     true
% 3.07/0.98  --inst_prop_sim_given                   true
% 3.07/0.98  --inst_prop_sim_new                     false
% 3.07/0.98  --inst_subs_new                         false
% 3.07/0.98  --inst_eq_res_simp                      false
% 3.07/0.98  --inst_subs_given                       false
% 3.07/0.98  --inst_orphan_elimination               true
% 3.07/0.98  --inst_learning_loop_flag               true
% 3.07/0.98  --inst_learning_start                   3000
% 3.07/0.98  --inst_learning_factor                  2
% 3.07/0.98  --inst_start_prop_sim_after_learn       3
% 3.07/0.98  --inst_sel_renew                        solver
% 3.07/0.98  --inst_lit_activity_flag                true
% 3.07/0.98  --inst_restr_to_given                   false
% 3.07/0.98  --inst_activity_threshold               500
% 3.07/0.98  --inst_out_proof                        true
% 3.07/0.98  
% 3.07/0.98  ------ Resolution Options
% 3.07/0.98  
% 3.07/0.98  --resolution_flag                       true
% 3.07/0.98  --res_lit_sel                           adaptive
% 3.07/0.98  --res_lit_sel_side                      none
% 3.07/0.98  --res_ordering                          kbo
% 3.07/0.98  --res_to_prop_solver                    active
% 3.07/0.98  --res_prop_simpl_new                    false
% 3.07/0.98  --res_prop_simpl_given                  true
% 3.07/0.98  --res_passive_queue_type                priority_queues
% 3.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/0.98  --res_passive_queues_freq               [15;5]
% 3.07/0.98  --res_forward_subs                      full
% 3.07/0.98  --res_backward_subs                     full
% 3.07/0.98  --res_forward_subs_resolution           true
% 3.07/0.98  --res_backward_subs_resolution          true
% 3.07/0.98  --res_orphan_elimination                true
% 3.07/0.98  --res_time_limit                        2.
% 3.07/0.98  --res_out_proof                         true
% 3.07/0.98  
% 3.07/0.98  ------ Superposition Options
% 3.07/0.98  
% 3.07/0.98  --superposition_flag                    true
% 3.07/0.98  --sup_passive_queue_type                priority_queues
% 3.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.07/0.98  --demod_completeness_check              fast
% 3.07/0.98  --demod_use_ground                      true
% 3.07/0.98  --sup_to_prop_solver                    passive
% 3.07/0.98  --sup_prop_simpl_new                    true
% 3.07/0.98  --sup_prop_simpl_given                  true
% 3.07/0.98  --sup_fun_splitting                     false
% 3.07/0.98  --sup_smt_interval                      50000
% 3.07/0.98  
% 3.07/0.98  ------ Superposition Simplification Setup
% 3.07/0.98  
% 3.07/0.98  --sup_indices_passive                   []
% 3.07/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_full_bw                           [BwDemod]
% 3.07/0.98  --sup_immed_triv                        [TrivRules]
% 3.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_immed_bw_main                     []
% 3.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.98  
% 3.07/0.98  ------ Combination Options
% 3.07/0.98  
% 3.07/0.98  --comb_res_mult                         3
% 3.07/0.98  --comb_sup_mult                         2
% 3.07/0.98  --comb_inst_mult                        10
% 3.07/0.98  
% 3.07/0.98  ------ Debug Options
% 3.07/0.98  
% 3.07/0.98  --dbg_backtrace                         false
% 3.07/0.98  --dbg_dump_prop_clauses                 false
% 3.07/0.98  --dbg_dump_prop_clauses_file            -
% 3.07/0.98  --dbg_out_stat                          false
% 3.07/0.98  ------ Parsing...
% 3.07/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.07/0.98  ------ Proving...
% 3.07/0.98  ------ Problem Properties 
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  clauses                                 27
% 3.07/0.98  conjectures                             5
% 3.07/0.98  EPR                                     9
% 3.07/0.98  Horn                                    21
% 3.07/0.98  unary                                   7
% 3.07/0.98  binary                                  10
% 3.07/0.98  lits                                    67
% 3.07/0.98  lits eq                                 23
% 3.07/0.98  fd_pure                                 0
% 3.07/0.98  fd_pseudo                               0
% 3.07/0.98  fd_cond                                 0
% 3.07/0.98  fd_pseudo_cond                          3
% 3.07/0.98  AC symbols                              0
% 3.07/0.98  
% 3.07/0.98  ------ Schedule dynamic 5 is on 
% 3.07/0.98  
% 3.07/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  ------ 
% 3.07/0.98  Current options:
% 3.07/0.98  ------ 
% 3.07/0.98  
% 3.07/0.98  ------ Input Options
% 3.07/0.98  
% 3.07/0.98  --out_options                           all
% 3.07/0.98  --tptp_safe_out                         true
% 3.07/0.98  --problem_path                          ""
% 3.07/0.98  --include_path                          ""
% 3.07/0.98  --clausifier                            res/vclausify_rel
% 3.07/0.98  --clausifier_options                    --mode clausify
% 3.07/0.98  --stdin                                 false
% 3.07/0.98  --stats_out                             all
% 3.07/0.98  
% 3.07/0.98  ------ General Options
% 3.07/0.98  
% 3.07/0.98  --fof                                   false
% 3.07/0.98  --time_out_real                         305.
% 3.07/0.98  --time_out_virtual                      -1.
% 3.07/0.98  --symbol_type_check                     false
% 3.07/0.98  --clausify_out                          false
% 3.07/0.98  --sig_cnt_out                           false
% 3.07/0.98  --trig_cnt_out                          false
% 3.07/0.98  --trig_cnt_out_tolerance                1.
% 3.07/0.98  --trig_cnt_out_sk_spl                   false
% 3.07/0.98  --abstr_cl_out                          false
% 3.07/0.98  
% 3.07/0.98  ------ Global Options
% 3.07/0.98  
% 3.07/0.98  --schedule                              default
% 3.07/0.98  --add_important_lit                     false
% 3.07/0.98  --prop_solver_per_cl                    1000
% 3.07/0.98  --min_unsat_core                        false
% 3.07/0.98  --soft_assumptions                      false
% 3.07/0.98  --soft_lemma_size                       3
% 3.07/0.98  --prop_impl_unit_size                   0
% 3.07/0.98  --prop_impl_unit                        []
% 3.07/0.98  --share_sel_clauses                     true
% 3.07/0.98  --reset_solvers                         false
% 3.07/0.98  --bc_imp_inh                            [conj_cone]
% 3.07/0.98  --conj_cone_tolerance                   3.
% 3.07/0.98  --extra_neg_conj                        none
% 3.07/0.98  --large_theory_mode                     true
% 3.07/0.98  --prolific_symb_bound                   200
% 3.07/0.98  --lt_threshold                          2000
% 3.07/0.98  --clause_weak_htbl                      true
% 3.07/0.98  --gc_record_bc_elim                     false
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing Options
% 3.07/0.98  
% 3.07/0.98  --preprocessing_flag                    true
% 3.07/0.98  --time_out_prep_mult                    0.1
% 3.07/0.98  --splitting_mode                        input
% 3.07/0.98  --splitting_grd                         true
% 3.07/0.98  --splitting_cvd                         false
% 3.07/0.98  --splitting_cvd_svl                     false
% 3.07/0.98  --splitting_nvd                         32
% 3.07/0.98  --sub_typing                            true
% 3.07/0.98  --prep_gs_sim                           true
% 3.07/0.98  --prep_unflatten                        true
% 3.07/0.98  --prep_res_sim                          true
% 3.07/0.98  --prep_upred                            true
% 3.07/0.98  --prep_sem_filter                       exhaustive
% 3.07/0.98  --prep_sem_filter_out                   false
% 3.07/0.98  --pred_elim                             true
% 3.07/0.98  --res_sim_input                         true
% 3.07/0.98  --eq_ax_congr_red                       true
% 3.07/0.98  --pure_diseq_elim                       true
% 3.07/0.98  --brand_transform                       false
% 3.07/0.98  --non_eq_to_eq                          false
% 3.07/0.98  --prep_def_merge                        true
% 3.07/0.98  --prep_def_merge_prop_impl              false
% 3.07/0.98  --prep_def_merge_mbd                    true
% 3.07/0.98  --prep_def_merge_tr_red                 false
% 3.07/0.98  --prep_def_merge_tr_cl                  false
% 3.07/0.98  --smt_preprocessing                     true
% 3.07/0.98  --smt_ac_axioms                         fast
% 3.07/0.98  --preprocessed_out                      false
% 3.07/0.98  --preprocessed_stats                    false
% 3.07/0.98  
% 3.07/0.98  ------ Abstraction refinement Options
% 3.07/0.98  
% 3.07/0.98  --abstr_ref                             []
% 3.07/0.98  --abstr_ref_prep                        false
% 3.07/0.98  --abstr_ref_until_sat                   false
% 3.07/0.98  --abstr_ref_sig_restrict                funpre
% 3.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/0.98  --abstr_ref_under                       []
% 3.07/0.98  
% 3.07/0.98  ------ SAT Options
% 3.07/0.98  
% 3.07/0.98  --sat_mode                              false
% 3.07/0.98  --sat_fm_restart_options                ""
% 3.07/0.98  --sat_gr_def                            false
% 3.07/0.98  --sat_epr_types                         true
% 3.07/0.98  --sat_non_cyclic_types                  false
% 3.07/0.98  --sat_finite_models                     false
% 3.07/0.98  --sat_fm_lemmas                         false
% 3.07/0.98  --sat_fm_prep                           false
% 3.07/0.98  --sat_fm_uc_incr                        true
% 3.07/0.98  --sat_out_model                         small
% 3.07/0.98  --sat_out_clauses                       false
% 3.07/0.98  
% 3.07/0.98  ------ QBF Options
% 3.07/0.98  
% 3.07/0.98  --qbf_mode                              false
% 3.07/0.98  --qbf_elim_univ                         false
% 3.07/0.98  --qbf_dom_inst                          none
% 3.07/0.98  --qbf_dom_pre_inst                      false
% 3.07/0.98  --qbf_sk_in                             false
% 3.07/0.98  --qbf_pred_elim                         true
% 3.07/0.98  --qbf_split                             512
% 3.07/0.98  
% 3.07/0.98  ------ BMC1 Options
% 3.07/0.98  
% 3.07/0.98  --bmc1_incremental                      false
% 3.07/0.98  --bmc1_axioms                           reachable_all
% 3.07/0.98  --bmc1_min_bound                        0
% 3.07/0.98  --bmc1_max_bound                        -1
% 3.07/0.98  --bmc1_max_bound_default                -1
% 3.07/0.98  --bmc1_symbol_reachability              true
% 3.07/0.98  --bmc1_property_lemmas                  false
% 3.07/0.98  --bmc1_k_induction                      false
% 3.07/0.98  --bmc1_non_equiv_states                 false
% 3.07/0.98  --bmc1_deadlock                         false
% 3.07/0.98  --bmc1_ucm                              false
% 3.07/0.98  --bmc1_add_unsat_core                   none
% 3.07/0.98  --bmc1_unsat_core_children              false
% 3.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/0.98  --bmc1_out_stat                         full
% 3.07/0.98  --bmc1_ground_init                      false
% 3.07/0.98  --bmc1_pre_inst_next_state              false
% 3.07/0.98  --bmc1_pre_inst_state                   false
% 3.07/0.98  --bmc1_pre_inst_reach_state             false
% 3.07/0.98  --bmc1_out_unsat_core                   false
% 3.07/0.98  --bmc1_aig_witness_out                  false
% 3.07/0.98  --bmc1_verbose                          false
% 3.07/0.98  --bmc1_dump_clauses_tptp                false
% 3.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.07/0.98  --bmc1_dump_file                        -
% 3.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.07/0.98  --bmc1_ucm_extend_mode                  1
% 3.07/0.98  --bmc1_ucm_init_mode                    2
% 3.07/0.98  --bmc1_ucm_cone_mode                    none
% 3.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.07/0.98  --bmc1_ucm_relax_model                  4
% 3.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/0.98  --bmc1_ucm_layered_model                none
% 3.07/0.98  --bmc1_ucm_max_lemma_size               10
% 3.07/0.98  
% 3.07/0.98  ------ AIG Options
% 3.07/0.98  
% 3.07/0.98  --aig_mode                              false
% 3.07/0.98  
% 3.07/0.98  ------ Instantiation Options
% 3.07/0.98  
% 3.07/0.98  --instantiation_flag                    true
% 3.07/0.98  --inst_sos_flag                         false
% 3.07/0.98  --inst_sos_phase                        true
% 3.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/0.98  --inst_lit_sel_side                     none
% 3.07/0.98  --inst_solver_per_active                1400
% 3.07/0.98  --inst_solver_calls_frac                1.
% 3.07/0.98  --inst_passive_queue_type               priority_queues
% 3.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/0.98  --inst_passive_queues_freq              [25;2]
% 3.07/0.98  --inst_dismatching                      true
% 3.07/0.98  --inst_eager_unprocessed_to_passive     true
% 3.07/0.98  --inst_prop_sim_given                   true
% 3.07/0.98  --inst_prop_sim_new                     false
% 3.07/0.98  --inst_subs_new                         false
% 3.07/0.98  --inst_eq_res_simp                      false
% 3.07/0.98  --inst_subs_given                       false
% 3.07/0.98  --inst_orphan_elimination               true
% 3.07/0.98  --inst_learning_loop_flag               true
% 3.07/0.98  --inst_learning_start                   3000
% 3.07/0.98  --inst_learning_factor                  2
% 3.07/0.98  --inst_start_prop_sim_after_learn       3
% 3.07/0.98  --inst_sel_renew                        solver
% 3.07/0.98  --inst_lit_activity_flag                true
% 3.07/0.98  --inst_restr_to_given                   false
% 3.07/0.98  --inst_activity_threshold               500
% 3.07/0.98  --inst_out_proof                        true
% 3.07/0.98  
% 3.07/0.98  ------ Resolution Options
% 3.07/0.98  
% 3.07/0.98  --resolution_flag                       false
% 3.07/0.98  --res_lit_sel                           adaptive
% 3.07/0.98  --res_lit_sel_side                      none
% 3.07/0.98  --res_ordering                          kbo
% 3.07/0.98  --res_to_prop_solver                    active
% 3.07/0.98  --res_prop_simpl_new                    false
% 3.07/0.98  --res_prop_simpl_given                  true
% 3.07/0.98  --res_passive_queue_type                priority_queues
% 3.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/0.98  --res_passive_queues_freq               [15;5]
% 3.07/0.98  --res_forward_subs                      full
% 3.07/0.98  --res_backward_subs                     full
% 3.07/0.98  --res_forward_subs_resolution           true
% 3.07/0.98  --res_backward_subs_resolution          true
% 3.07/0.98  --res_orphan_elimination                true
% 3.07/0.98  --res_time_limit                        2.
% 3.07/0.98  --res_out_proof                         true
% 3.07/0.98  
% 3.07/0.98  ------ Superposition Options
% 3.07/0.98  
% 3.07/0.98  --superposition_flag                    true
% 3.07/0.98  --sup_passive_queue_type                priority_queues
% 3.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.07/0.98  --demod_completeness_check              fast
% 3.07/0.98  --demod_use_ground                      true
% 3.07/0.98  --sup_to_prop_solver                    passive
% 3.07/0.98  --sup_prop_simpl_new                    true
% 3.07/0.98  --sup_prop_simpl_given                  true
% 3.07/0.98  --sup_fun_splitting                     false
% 3.07/0.98  --sup_smt_interval                      50000
% 3.07/0.98  
% 3.07/0.98  ------ Superposition Simplification Setup
% 3.07/0.98  
% 3.07/0.98  --sup_indices_passive                   []
% 3.07/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_full_bw                           [BwDemod]
% 3.07/0.98  --sup_immed_triv                        [TrivRules]
% 3.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_immed_bw_main                     []
% 3.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.98  
% 3.07/0.98  ------ Combination Options
% 3.07/0.98  
% 3.07/0.98  --comb_res_mult                         3
% 3.07/0.98  --comb_sup_mult                         2
% 3.07/0.98  --comb_inst_mult                        10
% 3.07/0.98  
% 3.07/0.98  ------ Debug Options
% 3.07/0.98  
% 3.07/0.98  --dbg_backtrace                         false
% 3.07/0.98  --dbg_dump_prop_clauses                 false
% 3.07/0.98  --dbg_dump_prop_clauses_file            -
% 3.07/0.98  --dbg_out_stat                          false
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  ------ Proving...
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  % SZS status Theorem for theBenchmark.p
% 3.07/0.98  
% 3.07/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.07/0.98  
% 3.07/0.98  fof(f12,axiom,(
% 3.07/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f25,plain,(
% 3.07/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.07/0.98    inference(ennf_transformation,[],[f12])).
% 3.07/0.98  
% 3.07/0.98  fof(f26,plain,(
% 3.07/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.07/0.98    inference(flattening,[],[f25])).
% 3.07/0.98  
% 3.07/0.98  fof(f39,plain,(
% 3.07/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.07/0.98    inference(nnf_transformation,[],[f26])).
% 3.07/0.98  
% 3.07/0.98  fof(f61,plain,(
% 3.07/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.07/0.98    inference(cnf_transformation,[],[f39])).
% 3.07/0.98  
% 3.07/0.98  fof(f13,conjecture,(
% 3.07/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f14,negated_conjecture,(
% 3.07/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.07/0.98    inference(negated_conjecture,[],[f13])).
% 3.07/0.98  
% 3.07/0.98  fof(f27,plain,(
% 3.07/0.98    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.07/0.98    inference(ennf_transformation,[],[f14])).
% 3.07/0.98  
% 3.07/0.98  fof(f28,plain,(
% 3.07/0.98    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.07/0.98    inference(flattening,[],[f27])).
% 3.07/0.98  
% 3.07/0.98  fof(f41,plain,(
% 3.07/0.98    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK5) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X2,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 3.07/0.98    introduced(choice_axiom,[])).
% 3.07/0.98  
% 3.07/0.98  fof(f40,plain,(
% 3.07/0.98    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.07/0.98    introduced(choice_axiom,[])).
% 3.07/0.98  
% 3.07/0.98  fof(f42,plain,(
% 3.07/0.98    (~r2_relset_1(sK2,sK3,sK4,sK5) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f41,f40])).
% 3.07/0.98  
% 3.07/0.98  fof(f71,plain,(
% 3.07/0.98    v1_funct_2(sK5,sK2,sK3)),
% 3.07/0.98    inference(cnf_transformation,[],[f42])).
% 3.07/0.98  
% 3.07/0.98  fof(f72,plain,(
% 3.07/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.07/0.98    inference(cnf_transformation,[],[f42])).
% 3.07/0.98  
% 3.07/0.98  fof(f10,axiom,(
% 3.07/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f22,plain,(
% 3.07/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.07/0.98    inference(ennf_transformation,[],[f10])).
% 3.07/0.98  
% 3.07/0.98  fof(f58,plain,(
% 3.07/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.07/0.98    inference(cnf_transformation,[],[f22])).
% 3.07/0.98  
% 3.07/0.98  fof(f68,plain,(
% 3.07/0.98    v1_funct_2(sK4,sK2,sK3)),
% 3.07/0.98    inference(cnf_transformation,[],[f42])).
% 3.07/0.98  
% 3.07/0.98  fof(f69,plain,(
% 3.07/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.07/0.98    inference(cnf_transformation,[],[f42])).
% 3.07/0.98  
% 3.07/0.98  fof(f7,axiom,(
% 3.07/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 3.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f18,plain,(
% 3.07/0.98    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.07/0.99    inference(ennf_transformation,[],[f7])).
% 3.07/0.99  
% 3.07/0.99  fof(f19,plain,(
% 3.07/0.99    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.07/0.99    inference(flattening,[],[f18])).
% 3.07/0.99  
% 3.07/0.99  fof(f36,plain,(
% 3.07/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 3.07/0.99    introduced(choice_axiom,[])).
% 3.07/0.99  
% 3.07/0.99  fof(f37,plain,(
% 3.07/0.99    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f36])).
% 3.07/0.99  
% 3.07/0.99  fof(f54,plain,(
% 3.07/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f37])).
% 3.07/0.99  
% 3.07/0.99  fof(f70,plain,(
% 3.07/0.99    v1_funct_1(sK5)),
% 3.07/0.99    inference(cnf_transformation,[],[f42])).
% 3.07/0.99  
% 3.07/0.99  fof(f8,axiom,(
% 3.07/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f20,plain,(
% 3.07/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.07/0.99    inference(ennf_transformation,[],[f8])).
% 3.07/0.99  
% 3.07/0.99  fof(f56,plain,(
% 3.07/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.07/0.99    inference(cnf_transformation,[],[f20])).
% 3.07/0.99  
% 3.07/0.99  fof(f67,plain,(
% 3.07/0.99    v1_funct_1(sK4)),
% 3.07/0.99    inference(cnf_transformation,[],[f42])).
% 3.07/0.99  
% 3.07/0.99  fof(f11,axiom,(
% 3.07/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f23,plain,(
% 3.07/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.07/0.99    inference(ennf_transformation,[],[f11])).
% 3.07/0.99  
% 3.07/0.99  fof(f24,plain,(
% 3.07/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.07/0.99    inference(flattening,[],[f23])).
% 3.07/0.99  
% 3.07/0.99  fof(f38,plain,(
% 3.07/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.07/0.99    inference(nnf_transformation,[],[f24])).
% 3.07/0.99  
% 3.07/0.99  fof(f60,plain,(
% 3.07/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.07/0.99    inference(cnf_transformation,[],[f38])).
% 3.07/0.99  
% 3.07/0.99  fof(f77,plain,(
% 3.07/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.07/0.99    inference(equality_resolution,[],[f60])).
% 3.07/0.99  
% 3.07/0.99  fof(f74,plain,(
% 3.07/0.99    ~r2_relset_1(sK2,sK3,sK4,sK5)),
% 3.07/0.99    inference(cnf_transformation,[],[f42])).
% 3.07/0.99  
% 3.07/0.99  fof(f3,axiom,(
% 3.07/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f33,plain,(
% 3.07/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.07/0.99    inference(nnf_transformation,[],[f3])).
% 3.07/0.99  
% 3.07/0.99  fof(f34,plain,(
% 3.07/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.07/0.99    inference(flattening,[],[f33])).
% 3.07/0.99  
% 3.07/0.99  fof(f49,plain,(
% 3.07/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f34])).
% 3.07/0.99  
% 3.07/0.99  fof(f47,plain,(
% 3.07/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.07/0.99    inference(cnf_transformation,[],[f34])).
% 3.07/0.99  
% 3.07/0.99  fof(f76,plain,(
% 3.07/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.07/0.99    inference(equality_resolution,[],[f47])).
% 3.07/0.99  
% 3.07/0.99  fof(f4,axiom,(
% 3.07/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f16,plain,(
% 3.07/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.07/0.99    inference(ennf_transformation,[],[f4])).
% 3.07/0.99  
% 3.07/0.99  fof(f50,plain,(
% 3.07/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f16])).
% 3.07/0.99  
% 3.07/0.99  fof(f73,plain,(
% 3.07/0.99    ( ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK2)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f42])).
% 3.07/0.99  
% 3.07/0.99  fof(f55,plain,(
% 3.07/0.99    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f37])).
% 3.07/0.99  
% 3.07/0.99  fof(f65,plain,(
% 3.07/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.07/0.99    inference(cnf_transformation,[],[f39])).
% 3.07/0.99  
% 3.07/0.99  fof(f80,plain,(
% 3.07/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.07/0.99    inference(equality_resolution,[],[f65])).
% 3.07/0.99  
% 3.07/0.99  fof(f5,axiom,(
% 3.07/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f35,plain,(
% 3.07/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.07/0.99    inference(nnf_transformation,[],[f5])).
% 3.07/0.99  
% 3.07/0.99  fof(f51,plain,(
% 3.07/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.07/0.99    inference(cnf_transformation,[],[f35])).
% 3.07/0.99  
% 3.07/0.99  fof(f1,axiom,(
% 3.07/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f15,plain,(
% 3.07/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.07/0.99    inference(ennf_transformation,[],[f1])).
% 3.07/0.99  
% 3.07/0.99  fof(f29,plain,(
% 3.07/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.07/0.99    inference(nnf_transformation,[],[f15])).
% 3.07/0.99  
% 3.07/0.99  fof(f30,plain,(
% 3.07/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.07/0.99    inference(rectify,[],[f29])).
% 3.07/0.99  
% 3.07/0.99  fof(f31,plain,(
% 3.07/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.07/0.99    introduced(choice_axiom,[])).
% 3.07/0.99  
% 3.07/0.99  fof(f32,plain,(
% 3.07/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.07/0.99  
% 3.07/0.99  fof(f44,plain,(
% 3.07/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f32])).
% 3.07/0.99  
% 3.07/0.99  fof(f6,axiom,(
% 3.07/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f17,plain,(
% 3.07/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.07/0.99    inference(ennf_transformation,[],[f6])).
% 3.07/0.99  
% 3.07/0.99  fof(f53,plain,(
% 3.07/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f17])).
% 3.07/0.99  
% 3.07/0.99  fof(f52,plain,(
% 3.07/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f35])).
% 3.07/0.99  
% 3.07/0.99  fof(f9,axiom,(
% 3.07/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f21,plain,(
% 3.07/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.07/0.99    inference(ennf_transformation,[],[f9])).
% 3.07/0.99  
% 3.07/0.99  fof(f57,plain,(
% 3.07/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f21])).
% 3.07/0.99  
% 3.07/0.99  fof(f2,axiom,(
% 3.07/0.99    v1_xboole_0(k1_xboole_0)),
% 3.07/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f46,plain,(
% 3.07/0.99    v1_xboole_0(k1_xboole_0)),
% 3.07/0.99    inference(cnf_transformation,[],[f2])).
% 3.07/0.99  
% 3.07/0.99  cnf(c_23,plain,
% 3.07/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.07/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.07/0.99      | k1_xboole_0 = X2 ),
% 3.07/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_27,negated_conjecture,
% 3.07/0.99      ( v1_funct_2(sK5,sK2,sK3) ),
% 3.07/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_498,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.07/0.99      | sK5 != X0
% 3.07/0.99      | sK3 != X2
% 3.07/0.99      | sK2 != X1
% 3.07/0.99      | k1_xboole_0 = X2 ),
% 3.07/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_499,plain,
% 3.07/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.07/0.99      | k1_relset_1(sK2,sK3,sK5) = sK2
% 3.07/0.99      | k1_xboole_0 = sK3 ),
% 3.07/0.99      inference(unflattening,[status(thm)],[c_498]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_26,negated_conjecture,
% 3.07/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.07/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_501,plain,
% 3.07/0.99      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_499,c_26]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2506,plain,
% 3.07/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_15,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.07/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2508,plain,
% 3.07/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.07/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3310,plain,
% 3.07/0.99      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2506,c_2508]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3403,plain,
% 3.07/0.99      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_501,c_3310]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_30,negated_conjecture,
% 3.07/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.07/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_509,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.07/0.99      | sK4 != X0
% 3.07/0.99      | sK3 != X2
% 3.07/0.99      | sK2 != X1
% 3.07/0.99      | k1_xboole_0 = X2 ),
% 3.07/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_510,plain,
% 3.07/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.07/0.99      | k1_relset_1(sK2,sK3,sK4) = sK2
% 3.07/0.99      | k1_xboole_0 = sK3 ),
% 3.07/0.99      inference(unflattening,[status(thm)],[c_509]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_29,negated_conjecture,
% 3.07/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.07/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_512,plain,
% 3.07/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_510,c_29]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2504,plain,
% 3.07/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3311,plain,
% 3.07/0.99      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2504,c_2508]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3489,plain,
% 3.07/0.99      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_512,c_3311]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_12,plain,
% 3.07/0.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 3.07/0.99      | ~ v1_relat_1(X1)
% 3.07/0.99      | ~ v1_relat_1(X0)
% 3.07/0.99      | ~ v1_funct_1(X1)
% 3.07/0.99      | ~ v1_funct_1(X0)
% 3.07/0.99      | X1 = X0
% 3.07/0.99      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.07/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2511,plain,
% 3.07/0.99      ( X0 = X1
% 3.07/0.99      | k1_relat_1(X0) != k1_relat_1(X1)
% 3.07/0.99      | r2_hidden(sK1(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.07/0.99      | v1_relat_1(X1) != iProver_top
% 3.07/0.99      | v1_relat_1(X0) != iProver_top
% 3.07/0.99      | v1_funct_1(X0) != iProver_top
% 3.07/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3709,plain,
% 3.07/0.99      ( k1_relat_1(X0) != sK2
% 3.07/0.99      | sK5 = X0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 3.07/0.99      | v1_relat_1(X0) != iProver_top
% 3.07/0.99      | v1_relat_1(sK5) != iProver_top
% 3.07/0.99      | v1_funct_1(X0) != iProver_top
% 3.07/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_3403,c_2511]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_28,negated_conjecture,
% 3.07/0.99      ( v1_funct_1(sK5) ),
% 3.07/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_35,plain,
% 3.07/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_37,plain,
% 3.07/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_13,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/0.99      | v1_relat_1(X0) ),
% 3.07/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2716,plain,
% 3.07/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.07/0.99      | v1_relat_1(sK5) ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2717,plain,
% 3.07/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.07/0.99      | v1_relat_1(sK5) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_2716]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4067,plain,
% 3.07/0.99      ( v1_funct_1(X0) != iProver_top
% 3.07/0.99      | k1_relat_1(X0) != sK2
% 3.07/0.99      | sK5 = X0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 3.07/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_3709,c_35,c_37,c_2717]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4068,plain,
% 3.07/0.99      ( k1_relat_1(X0) != sK2
% 3.07/0.99      | sK5 = X0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(sK1(X0,sK5),k1_relat_1(X0)) = iProver_top
% 3.07/0.99      | v1_relat_1(X0) != iProver_top
% 3.07/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.07/0.99      inference(renaming,[status(thm)],[c_4067]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4080,plain,
% 3.07/0.99      ( sK5 = sK4
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top
% 3.07/0.99      | v1_relat_1(sK4) != iProver_top
% 3.07/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_3489,c_4068]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_31,negated_conjecture,
% 3.07/0.99      ( v1_funct_1(sK4) ),
% 3.07/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_32,plain,
% 3.07/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_34,plain,
% 3.07/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_16,plain,
% 3.07/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.07/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.07/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_24,negated_conjecture,
% 3.07/0.99      ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
% 3.07/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_415,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/0.99      | sK5 != X0
% 3.07/0.99      | sK4 != X0
% 3.07/0.99      | sK3 != X2
% 3.07/0.99      | sK2 != X1 ),
% 3.07/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_416,plain,
% 3.07/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.07/0.99      | sK4 != sK5 ),
% 3.07/0.99      inference(unflattening,[status(thm)],[c_415]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2719,plain,
% 3.07/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.07/0.99      | v1_relat_1(sK4) ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2720,plain,
% 3.07/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.07/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_2719]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4,plain,
% 3.07/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.07/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2814,plain,
% 3.07/0.99      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3019,plain,
% 3.07/0.99      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_2814]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_6,plain,
% 3.07/0.99      ( r1_tarski(X0,X0) ),
% 3.07/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3020,plain,
% 3.07/0.99      ( r1_tarski(sK4,sK4) ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1926,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2745,plain,
% 3.07/0.99      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_1926]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3357,plain,
% 3.07/0.99      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_2745]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4093,plain,
% 3.07/0.99      ( sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(sK1(sK4,sK5),k1_relat_1(sK4)) = iProver_top ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_4080,c_32,c_34,c_26,c_416,c_2720,c_3019,c_3020,c_3357]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4099,plain,
% 3.07/0.99      ( sK3 = k1_xboole_0 | r2_hidden(sK1(sK4,sK5),sK2) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_3489,c_4093]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_7,plain,
% 3.07/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.07/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2515,plain,
% 3.07/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.07/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4207,plain,
% 3.07/0.99      ( sK3 = k1_xboole_0 | m1_subset_1(sK1(sK4,sK5),sK2) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_4099,c_2515]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_25,negated_conjecture,
% 3.07/0.99      ( ~ m1_subset_1(X0,sK2) | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
% 3.07/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2507,plain,
% 3.07/0.99      ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
% 3.07/0.99      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4668,plain,
% 3.07/0.99      ( k1_funct_1(sK4,sK1(sK4,sK5)) = k1_funct_1(sK5,sK1(sK4,sK5))
% 3.07/0.99      | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_4207,c_2507]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_11,plain,
% 3.07/0.99      ( ~ v1_relat_1(X0)
% 3.07/0.99      | ~ v1_relat_1(X1)
% 3.07/0.99      | ~ v1_funct_1(X0)
% 3.07/0.99      | ~ v1_funct_1(X1)
% 3.07/0.99      | X0 = X1
% 3.07/0.99      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 3.07/0.99      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 3.07/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2512,plain,
% 3.07/0.99      ( X0 = X1
% 3.07/0.99      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 3.07/0.99      | k1_relat_1(X0) != k1_relat_1(X1)
% 3.07/0.99      | v1_relat_1(X0) != iProver_top
% 3.07/0.99      | v1_relat_1(X1) != iProver_top
% 3.07/0.99      | v1_funct_1(X1) != iProver_top
% 3.07/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4691,plain,
% 3.07/0.99      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 3.07/0.99      | sK5 = sK4
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | v1_relat_1(sK5) != iProver_top
% 3.07/0.99      | v1_relat_1(sK4) != iProver_top
% 3.07/0.99      | v1_funct_1(sK5) != iProver_top
% 3.07/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_4668,c_2512]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4692,plain,
% 3.07/0.99      ( ~ v1_relat_1(sK5)
% 3.07/0.99      | ~ v1_relat_1(sK4)
% 3.07/0.99      | ~ v1_funct_1(sK5)
% 3.07/0.99      | ~ v1_funct_1(sK4)
% 3.07/0.99      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 3.07/0.99      | sK5 = sK4
% 3.07/0.99      | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4691]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4702,plain,
% 3.07/0.99      ( k1_relat_1(sK4) != k1_relat_1(sK5) | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_4691,c_31,c_29,c_28,c_26,c_416,c_2716,c_2719,c_3019,
% 3.07/0.99                 c_3020,c_3357,c_4692]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4706,plain,
% 3.07/0.99      ( k1_relat_1(sK4) != sK2 | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_3403,c_4702]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4729,plain,
% 3.07/0.99      ( sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_4706,c_3489]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_19,plain,
% 3.07/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.07/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.07/0.99      | k1_xboole_0 = X1
% 3.07/0.99      | k1_xboole_0 = X0 ),
% 3.07/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_452,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.07/0.99      | sK4 != X0
% 3.07/0.99      | sK3 != k1_xboole_0
% 3.07/0.99      | sK2 != X1
% 3.07/0.99      | k1_xboole_0 = X0
% 3.07/0.99      | k1_xboole_0 = X1 ),
% 3.07/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_453,plain,
% 3.07/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.07/0.99      | sK3 != k1_xboole_0
% 3.07/0.99      | k1_xboole_0 = sK4
% 3.07/0.99      | k1_xboole_0 = sK2 ),
% 3.07/0.99      inference(unflattening,[status(thm)],[c_452]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2500,plain,
% 3.07/0.99      ( sK3 != k1_xboole_0
% 3.07/0.99      | k1_xboole_0 = sK4
% 3.07/0.99      | k1_xboole_0 = sK2
% 3.07/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4744,plain,
% 3.07/0.99      ( sK4 = k1_xboole_0
% 3.07/0.99      | sK2 = k1_xboole_0
% 3.07/0.99      | k1_xboole_0 != k1_xboole_0
% 3.07/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.07/0.99      inference(demodulation,[status(thm)],[c_4729,c_2500]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4773,plain,
% 3.07/0.99      ( sK4 = k1_xboole_0
% 3.07/0.99      | sK2 = k1_xboole_0
% 3.07/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.07/0.99      inference(equality_resolution_simp,[status(thm)],[c_4744]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4752,plain,
% 3.07/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.07/0.99      inference(demodulation,[status(thm)],[c_4729,c_2504]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4777,plain,
% 3.07/0.99      ( sK4 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.07/0.99      inference(forward_subsumption_resolution,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_4773,c_4752]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2824,plain,
% 3.07/0.99      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_1926]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3356,plain,
% 3.07/0.99      ( sK5 != X0 | sK5 = sK4 | sK4 != X0 ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_2824]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3358,plain,
% 3.07/0.99      ( sK5 = sK4 | sK5 != k1_xboole_0 | sK4 != k1_xboole_0 ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_3356]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_436,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.07/0.99      | sK5 != X0
% 3.07/0.99      | sK3 != k1_xboole_0
% 3.07/0.99      | sK2 != X1
% 3.07/0.99      | k1_xboole_0 = X0
% 3.07/0.99      | k1_xboole_0 = X1 ),
% 3.07/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_437,plain,
% 3.07/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.07/0.99      | sK3 != k1_xboole_0
% 3.07/0.99      | k1_xboole_0 = sK5
% 3.07/0.99      | k1_xboole_0 = sK2 ),
% 3.07/0.99      inference(unflattening,[status(thm)],[c_436]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2501,plain,
% 3.07/0.99      ( sK3 != k1_xboole_0
% 3.07/0.99      | k1_xboole_0 = sK5
% 3.07/0.99      | k1_xboole_0 = sK2
% 3.07/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4743,plain,
% 3.07/0.99      ( sK5 = k1_xboole_0
% 3.07/0.99      | sK2 = k1_xboole_0
% 3.07/0.99      | k1_xboole_0 != k1_xboole_0
% 3.07/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.07/0.99      inference(demodulation,[status(thm)],[c_4729,c_2501]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4780,plain,
% 3.07/0.99      ( sK5 = k1_xboole_0
% 3.07/0.99      | sK2 = k1_xboole_0
% 3.07/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.07/0.99      inference(equality_resolution_simp,[status(thm)],[c_4743]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4751,plain,
% 3.07/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.07/0.99      inference(demodulation,[status(thm)],[c_4729,c_2506]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4784,plain,
% 3.07/0.99      ( sK5 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.07/0.99      inference(forward_subsumption_resolution,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_4780,c_4751]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5744,plain,
% 3.07/0.99      ( sK2 = k1_xboole_0 ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_4777,c_26,c_416,c_3019,c_3020,c_3358,c_3357,c_4784]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_9,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.07/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2513,plain,
% 3.07/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.07/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3084,plain,
% 3.07/0.99      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2504,c_2513]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4746,plain,
% 3.07/0.99      ( r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
% 3.07/0.99      inference(demodulation,[status(thm)],[c_4729,c_3084]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5748,plain,
% 3.07/0.99      ( r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.07/0.99      inference(demodulation,[status(thm)],[c_5744,c_4746]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1,plain,
% 3.07/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.07/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2520,plain,
% 3.07/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.07/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_10,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.07/0.99      | ~ r2_hidden(X2,X0)
% 3.07/0.99      | ~ v1_xboole_0(X1) ),
% 3.07/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_8,plain,
% 3.07/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.07/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_240,plain,
% 3.07/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.07/0.99      inference(prop_impl,[status(thm)],[c_8]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_241,plain,
% 3.07/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.07/0.99      inference(renaming,[status(thm)],[c_240]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_304,plain,
% 3.07/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 3.07/0.99      inference(bin_hyper_res,[status(thm)],[c_10,c_241]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2502,plain,
% 3.07/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.07/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.07/0.99      | v1_xboole_0(X2) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_6693,plain,
% 3.07/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.07/0.99      | r1_tarski(X0,X2) = iProver_top
% 3.07/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2520,c_2502]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_6701,plain,
% 3.07/0.99      ( r1_tarski(sK4,X0) = iProver_top
% 3.07/0.99      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_5748,c_6693]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_6733,plain,
% 3.07/0.99      ( r1_tarski(sK4,k1_xboole_0) = iProver_top
% 3.07/0.99      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_6701]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3083,plain,
% 3.07/0.99      ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2506,c_2513]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4747,plain,
% 3.07/0.99      ( r1_tarski(sK5,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
% 3.07/0.99      inference(demodulation,[status(thm)],[c_4729,c_3083]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5747,plain,
% 3.07/0.99      ( r1_tarski(sK5,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.07/0.99      inference(demodulation,[status(thm)],[c_5744,c_4747]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_6700,plain,
% 3.07/0.99      ( r1_tarski(sK5,X0) = iProver_top
% 3.07/0.99      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_5747,c_6693]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_6730,plain,
% 3.07/0.99      ( r1_tarski(sK5,k1_xboole_0) = iProver_top
% 3.07/0.99      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_6700]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2516,plain,
% 3.07/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2514,plain,
% 3.07/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.07/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_14,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/0.99      | ~ v1_xboole_0(X2)
% 3.07/0.99      | v1_xboole_0(X0) ),
% 3.07/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2509,plain,
% 3.07/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.07/0.99      | v1_xboole_0(X2) != iProver_top
% 3.07/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3604,plain,
% 3.07/0.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.07/0.99      | v1_xboole_0(X2) != iProver_top
% 3.07/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2514,c_2509]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5789,plain,
% 3.07/0.99      ( v1_xboole_0(X0) != iProver_top
% 3.07/0.99      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2516,c_3604]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5796,plain,
% 3.07/0.99      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 3.07/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_5789]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4548,plain,
% 3.07/0.99      ( ~ r2_hidden(sK0(X0,sK4),X0)
% 3.07/0.99      | ~ r1_tarski(X0,X1)
% 3.07/0.99      | ~ v1_xboole_0(X1) ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_304]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4559,plain,
% 3.07/0.99      ( r2_hidden(sK0(X0,sK4),X0) != iProver_top
% 3.07/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.07/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_4548]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4561,plain,
% 3.07/0.99      ( r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) != iProver_top
% 3.07/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.07/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_4559]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3453,plain,
% 3.07/0.99      ( ~ r2_hidden(sK0(X0,sK5),X0)
% 3.07/0.99      | ~ r1_tarski(X0,X1)
% 3.07/0.99      | ~ v1_xboole_0(X1) ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_304]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3464,plain,
% 3.07/0.99      ( r2_hidden(sK0(X0,sK5),X0) != iProver_top
% 3.07/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.07/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_3453]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3466,plain,
% 3.07/0.99      ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) != iProver_top
% 3.07/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.07/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_3464]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3041,plain,
% 3.07/0.99      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3042,plain,
% 3.07/0.99      ( sK4 = X0
% 3.07/0.99      | r1_tarski(X0,sK4) != iProver_top
% 3.07/0.99      | r1_tarski(sK4,X0) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_3041]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3044,plain,
% 3.07/0.99      ( sK4 = k1_xboole_0
% 3.07/0.99      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.07/0.99      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_3042]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3004,plain,
% 3.07/0.99      ( r2_hidden(sK0(X0,sK4),X0) | r1_tarski(X0,sK4) ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3015,plain,
% 3.07/0.99      ( r2_hidden(sK0(X0,sK4),X0) = iProver_top
% 3.07/0.99      | r1_tarski(X0,sK4) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_3004]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3017,plain,
% 3.07/0.99      ( r2_hidden(sK0(k1_xboole_0,sK4),k1_xboole_0) = iProver_top
% 3.07/0.99      | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_3015]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2983,plain,
% 3.07/0.99      ( r2_hidden(sK0(X0,sK5),X0) | r1_tarski(X0,sK5) ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2994,plain,
% 3.07/0.99      ( r2_hidden(sK0(X0,sK5),X0) = iProver_top
% 3.07/0.99      | r1_tarski(X0,sK5) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_2983]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2996,plain,
% 3.07/0.99      ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) = iProver_top
% 3.07/0.99      | r1_tarski(k1_xboole_0,sK5) = iProver_top ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_2994]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2948,plain,
% 3.07/0.99      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2949,plain,
% 3.07/0.99      ( sK5 = X0
% 3.07/0.99      | r1_tarski(X0,sK5) != iProver_top
% 3.07/0.99      | r1_tarski(sK5,X0) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_2948]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2951,plain,
% 3.07/0.99      ( sK5 = k1_xboole_0
% 3.07/0.99      | r1_tarski(sK5,k1_xboole_0) != iProver_top
% 3.07/0.99      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_2949]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2746,plain,
% 3.07/0.99      ( sK5 != k1_xboole_0 | sK4 = sK5 | sK4 != k1_xboole_0 ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_2745]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3,plain,
% 3.07/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.07/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_98,plain,
% 3.07/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_91,plain,
% 3.07/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_93,plain,
% 3.07/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_91]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(contradiction,plain,
% 3.07/0.99      ( $false ),
% 3.07/0.99      inference(minisat,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_6733,c_6730,c_5796,c_4561,c_3466,c_3044,c_3017,c_2996,
% 3.07/0.99                 c_2951,c_2746,c_416,c_98,c_93,c_26]) ).
% 3.07/0.99  
% 3.07/0.99  
% 3.07/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.07/0.99  
% 3.07/0.99  ------                               Statistics
% 3.07/0.99  
% 3.07/0.99  ------ General
% 3.07/0.99  
% 3.07/0.99  abstr_ref_over_cycles:                  0
% 3.07/0.99  abstr_ref_under_cycles:                 0
% 3.07/0.99  gc_basic_clause_elim:                   0
% 3.07/0.99  forced_gc_time:                         0
% 3.07/0.99  parsing_time:                           0.01
% 3.07/0.99  unif_index_cands_time:                  0.
% 3.07/0.99  unif_index_add_time:                    0.
% 3.07/0.99  orderings_time:                         0.
% 3.07/0.99  out_proof_time:                         0.011
% 3.07/0.99  total_time:                             0.192
% 3.07/0.99  num_of_symbols:                         51
% 3.07/0.99  num_of_terms:                           4599
% 3.07/0.99  
% 3.07/0.99  ------ Preprocessing
% 3.07/0.99  
% 3.07/0.99  num_of_splits:                          0
% 3.07/0.99  num_of_split_atoms:                     0
% 3.07/0.99  num_of_reused_defs:                     0
% 3.07/0.99  num_eq_ax_congr_red:                    26
% 3.07/0.99  num_of_sem_filtered_clauses:            1
% 3.07/0.99  num_of_subtypes:                        0
% 3.07/0.99  monotx_restored_types:                  0
% 3.07/0.99  sat_num_of_epr_types:                   0
% 3.07/0.99  sat_num_of_non_cyclic_types:            0
% 3.07/0.99  sat_guarded_non_collapsed_types:        0
% 3.07/0.99  num_pure_diseq_elim:                    0
% 3.07/0.99  simp_replaced_by:                       0
% 3.07/0.99  res_preprocessed:                       133
% 3.07/0.99  prep_upred:                             0
% 3.07/0.99  prep_unflattend:                        113
% 3.07/0.99  smt_new_axioms:                         0
% 3.07/0.99  pred_elim_cands:                        6
% 3.07/0.99  pred_elim:                              2
% 3.07/0.99  pred_elim_cl:                           4
% 3.07/0.99  pred_elim_cycles:                       4
% 3.07/0.99  merged_defs:                            8
% 3.07/0.99  merged_defs_ncl:                        0
% 3.07/0.99  bin_hyper_res:                          9
% 3.07/0.99  prep_cycles:                            4
% 3.07/0.99  pred_elim_time:                         0.025
% 3.07/0.99  splitting_time:                         0.
% 3.07/0.99  sem_filter_time:                        0.
% 3.07/0.99  monotx_time:                            0.001
% 3.07/0.99  subtype_inf_time:                       0.
% 3.07/0.99  
% 3.07/0.99  ------ Problem properties
% 3.07/0.99  
% 3.07/0.99  clauses:                                27
% 3.07/0.99  conjectures:                            5
% 3.07/0.99  epr:                                    9
% 3.07/0.99  horn:                                   21
% 3.07/0.99  ground:                                 12
% 3.07/0.99  unary:                                  7
% 3.07/0.99  binary:                                 10
% 3.07/0.99  lits:                                   67
% 3.07/0.99  lits_eq:                                23
% 3.07/0.99  fd_pure:                                0
% 3.07/0.99  fd_pseudo:                              0
% 3.07/0.99  fd_cond:                                0
% 3.07/0.99  fd_pseudo_cond:                         3
% 3.07/0.99  ac_symbols:                             0
% 3.07/0.99  
% 3.07/0.99  ------ Propositional Solver
% 3.07/0.99  
% 3.07/0.99  prop_solver_calls:                      29
% 3.07/0.99  prop_fast_solver_calls:                 1205
% 3.07/0.99  smt_solver_calls:                       0
% 3.07/0.99  smt_fast_solver_calls:                  0
% 3.07/0.99  prop_num_of_clauses:                    1967
% 3.07/0.99  prop_preprocess_simplified:             5679
% 3.07/0.99  prop_fo_subsumed:                       31
% 3.07/0.99  prop_solver_time:                       0.
% 3.07/0.99  smt_solver_time:                        0.
% 3.07/0.99  smt_fast_solver_time:                   0.
% 3.07/0.99  prop_fast_solver_time:                  0.
% 3.07/0.99  prop_unsat_core_time:                   0.
% 3.07/0.99  
% 3.07/0.99  ------ QBF
% 3.07/0.99  
% 3.07/0.99  qbf_q_res:                              0
% 3.07/0.99  qbf_num_tautologies:                    0
% 3.07/0.99  qbf_prep_cycles:                        0
% 3.07/0.99  
% 3.07/0.99  ------ BMC1
% 3.07/0.99  
% 3.07/0.99  bmc1_current_bound:                     -1
% 3.07/0.99  bmc1_last_solved_bound:                 -1
% 3.07/0.99  bmc1_unsat_core_size:                   -1
% 3.07/0.99  bmc1_unsat_core_parents_size:           -1
% 3.07/0.99  bmc1_merge_next_fun:                    0
% 3.07/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.07/0.99  
% 3.07/0.99  ------ Instantiation
% 3.07/0.99  
% 3.07/0.99  inst_num_of_clauses:                    560
% 3.07/0.99  inst_num_in_passive:                    203
% 3.07/0.99  inst_num_in_active:                     341
% 3.07/0.99  inst_num_in_unprocessed:                16
% 3.07/0.99  inst_num_of_loops:                      450
% 3.07/0.99  inst_num_of_learning_restarts:          0
% 3.07/0.99  inst_num_moves_active_passive:          105
% 3.07/0.99  inst_lit_activity:                      0
% 3.07/0.99  inst_lit_activity_moves:                0
% 3.07/0.99  inst_num_tautologies:                   0
% 3.07/0.99  inst_num_prop_implied:                  0
% 3.07/0.99  inst_num_existing_simplified:           0
% 3.07/0.99  inst_num_eq_res_simplified:             0
% 3.07/0.99  inst_num_child_elim:                    0
% 3.07/0.99  inst_num_of_dismatching_blockings:      211
% 3.07/0.99  inst_num_of_non_proper_insts:           586
% 3.07/0.99  inst_num_of_duplicates:                 0
% 3.07/0.99  inst_inst_num_from_inst_to_res:         0
% 3.07/0.99  inst_dismatching_checking_time:         0.
% 3.07/0.99  
% 3.07/0.99  ------ Resolution
% 3.07/0.99  
% 3.07/0.99  res_num_of_clauses:                     0
% 3.07/0.99  res_num_in_passive:                     0
% 3.07/0.99  res_num_in_active:                      0
% 3.07/0.99  res_num_of_loops:                       137
% 3.07/0.99  res_forward_subset_subsumed:            78
% 3.07/0.99  res_backward_subset_subsumed:           0
% 3.07/0.99  res_forward_subsumed:                   0
% 3.07/0.99  res_backward_subsumed:                  0
% 3.07/0.99  res_forward_subsumption_resolution:     0
% 3.07/0.99  res_backward_subsumption_resolution:    0
% 3.07/0.99  res_clause_to_clause_subsumption:       315
% 3.07/0.99  res_orphan_elimination:                 0
% 3.07/0.99  res_tautology_del:                      68
% 3.07/0.99  res_num_eq_res_simplified:              0
% 3.07/0.99  res_num_sel_changes:                    0
% 3.07/0.99  res_moves_from_active_to_pass:          0
% 3.07/0.99  
% 3.07/0.99  ------ Superposition
% 3.07/0.99  
% 3.07/0.99  sup_time_total:                         0.
% 3.07/0.99  sup_time_generating:                    0.
% 3.07/0.99  sup_time_sim_full:                      0.
% 3.07/0.99  sup_time_sim_immed:                     0.
% 3.07/0.99  
% 3.07/0.99  sup_num_of_clauses:                     69
% 3.07/0.99  sup_num_in_active:                      50
% 3.07/0.99  sup_num_in_passive:                     19
% 3.07/0.99  sup_num_of_loops:                       89
% 3.07/0.99  sup_fw_superposition:                   49
% 3.07/0.99  sup_bw_superposition:                   65
% 3.07/0.99  sup_immediate_simplified:               9
% 3.07/0.99  sup_given_eliminated:                   0
% 3.07/0.99  comparisons_done:                       0
% 3.07/0.99  comparisons_avoided:                    12
% 3.07/0.99  
% 3.07/0.99  ------ Simplifications
% 3.07/0.99  
% 3.07/0.99  
% 3.07/0.99  sim_fw_subset_subsumed:                 5
% 3.07/0.99  sim_bw_subset_subsumed:                 14
% 3.07/0.99  sim_fw_subsumed:                        0
% 3.07/0.99  sim_bw_subsumed:                        0
% 3.07/0.99  sim_fw_subsumption_res:                 2
% 3.07/0.99  sim_bw_subsumption_res:                 0
% 3.07/0.99  sim_tautology_del:                      1
% 3.07/0.99  sim_eq_tautology_del:                   14
% 3.07/0.99  sim_eq_res_simp:                        2
% 3.07/0.99  sim_fw_demodulated:                     1
% 3.07/0.99  sim_bw_demodulated:                     31
% 3.07/0.99  sim_light_normalised:                   9
% 3.07/0.99  sim_joinable_taut:                      0
% 3.07/0.99  sim_joinable_simp:                      0
% 3.07/0.99  sim_ac_normalised:                      0
% 3.07/0.99  sim_smt_subsumption:                    0
% 3.07/0.99  
%------------------------------------------------------------------------------
