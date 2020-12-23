%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:08 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  213 (1137 expanded)
%              Number of clauses        :  137 ( 353 expanded)
%              Number of leaves         :   26 ( 283 expanded)
%              Depth                    :   25
%              Number of atoms          :  686 (6720 expanded)
%              Number of equality atoms :  326 (1403 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK8)
        & ! [X4] :
            ( k1_funct_1(sK8,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK8,X0,X1)
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
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
          ( ~ r2_relset_1(sK5,sK6,sK7,X3)
          & ! [X4] :
              ( k1_funct_1(sK7,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK5) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X3,sK5,sK6)
          & v1_funct_1(X3) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ~ r2_relset_1(sK5,sK6,sK7,sK8)
    & ! [X4] :
        ( k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4)
        | ~ r2_hidden(X4,sK5) )
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f31,f50,f49])).

fof(f80,plain,(
    v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f46])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f5,f43])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    ~ r2_relset_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f86,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f74])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f82,plain,(
    ! [X4] :
      ( k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4)
      | ~ r2_hidden(X4,sK5) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK8 != X0
    | sK6 != X2
    | sK5 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_517,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k1_relset_1(sK5,sK6,sK8) = sK5
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_519,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | k1_xboole_0 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_26])).

cnf(c_1839,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1841,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2693,plain,
    ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1839,c_1841])).

cnf(c_3049,plain,
    ( k1_relat_1(sK8) = sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_519,c_2693])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK7 != X0
    | sK6 != X2
    | sK5 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_528,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k1_relset_1(sK5,sK6,sK7) = sK5
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_530,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | k1_xboole_0 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_528,c_29])).

cnf(c_1837,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2694,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1837,c_1841])).

cnf(c_3122,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_530,c_2694])).

cnf(c_12,plain,
    ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X1 = X0
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1844,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3710,plain,
    ( k1_relat_1(X0) != sK5
    | sK8 = X0
    | sK6 = k1_xboole_0
    | r2_hidden(sK4(sK8,X0),k1_relat_1(sK8)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3049,c_1844])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_35,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_37,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2058,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2059,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2058])).

cnf(c_4754,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != sK5
    | sK8 = X0
    | sK6 = k1_xboole_0
    | r2_hidden(sK4(sK8,X0),k1_relat_1(sK8)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3710,c_35,c_37,c_2059])).

cnf(c_4755,plain,
    ( k1_relat_1(X0) != sK5
    | sK8 = X0
    | sK6 = k1_xboole_0
    | r2_hidden(sK4(sK8,X0),k1_relat_1(sK8)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4754])).

cnf(c_4767,plain,
    ( sK8 = sK7
    | sK6 = k1_xboole_0
    | r2_hidden(sK4(sK8,sK7),k1_relat_1(sK8)) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3122,c_4755])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_34,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_8,plain,
    ( m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_17,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_24,negated_conjecture,
    ( ~ r2_relset_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK8 != X0
    | sK7 != X0
    | sK6 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | sK7 != sK8 ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | sK7 != sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_353,c_26])).

cnf(c_596,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != X0
    | sK3(X0) != X1
    | sK8 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_357])).

cnf(c_597,plain,
    ( sK8 != sK7 ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_2061,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2062,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2061])).

cnf(c_4780,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4(sK8,sK7),k1_relat_1(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4767,c_32,c_34,c_597,c_2062])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_14,c_10])).

cnf(c_377,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_373,c_13])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_377])).

cnf(c_1834,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_2583,plain,
    ( r1_tarski(k1_relat_1(sK8),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1839,c_1834])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1850,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3545,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2583,c_1850])).

cnf(c_4788,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4(sK8,sK7),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4780,c_3545])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_454,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK8 != X0
    | sK6 != k1_xboole_0
    | sK5 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_455,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)))
    | sK6 != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_749,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK8 != sK8
    | sK8 = k1_xboole_0
    | sK6 != k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_455])).

cnf(c_470,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK7 != X0
    | sK6 != k1_xboole_0
    | sK5 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_471,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)))
    | sK6 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_783,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
    | sK7 != sK7
    | sK7 = k1_xboole_0
    | sK6 != k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_471])).

cnf(c_1375,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1396,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_1376,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2086,plain,
    ( sK8 != X0
    | sK7 != X0
    | sK7 = sK8 ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_2087,plain,
    ( sK8 != k1_xboole_0
    | sK7 = sK8
    | sK7 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2086])).

cnf(c_2211,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_2268,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_3441,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_1383,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_2562,plain,
    ( X0 != sK6
    | X1 != sK5
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1383])).

cnf(c_3525,plain,
    ( X0 != sK6
    | k2_zfmisc_1(sK5,X0) = k2_zfmisc_1(sK5,sK6)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2562])).

cnf(c_3527,plain,
    ( k2_zfmisc_1(sK5,k1_xboole_0) = k2_zfmisc_1(sK5,sK6)
    | sK5 != sK5
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_3525])).

cnf(c_3526,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_4284,plain,
    ( X0 != X1
    | X0 = sK6
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_4285,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4284])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1853,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4787,plain,
    ( sK6 = k1_xboole_0
    | v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4780,c_1853])).

cnf(c_4880,plain,
    ( sK6 = k1_xboole_0
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3049,c_4787])).

cnf(c_2136,plain,
    ( r2_hidden(sK4(sK8,sK7),k1_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK7)
    | k1_relat_1(sK8) != k1_relat_1(sK7)
    | sK7 = sK8 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2137,plain,
    ( k1_relat_1(sK8) != k1_relat_1(sK7)
    | sK7 = sK8
    | r2_hidden(sK4(sK8,sK7),k1_relat_1(sK8)) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2136])).

cnf(c_7,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r2_hidden(sK2(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2412,plain,
    ( r2_hidden(sK2(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(sK8))
    | r2_hidden(sK2(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(sK7))
    | k1_relat_1(sK8) = k1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2416,plain,
    ( k1_relat_1(sK8) = k1_relat_1(sK7)
    | r2_hidden(sK2(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(sK8)) = iProver_top
    | r2_hidden(sK2(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2412])).

cnf(c_2750,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(sK8))
    | ~ v1_xboole_0(k1_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2751,plain,
    ( r2_hidden(sK2(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(sK8)) != iProver_top
    | v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2750])).

cnf(c_2773,plain,
    ( ~ r2_hidden(sK4(sK8,sK7),k1_relat_1(sK8))
    | ~ v1_xboole_0(k1_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2774,plain,
    ( r2_hidden(sK4(sK8,sK7),k1_relat_1(sK8)) != iProver_top
    | v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2773])).

cnf(c_4474,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(sK7))
    | ~ v1_xboole_0(k1_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4475,plain,
    ( r2_hidden(sK2(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(sK7)) != iProver_top
    | v1_xboole_0(k1_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4474])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1854,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3950,plain,
    ( r2_hidden(sK0(k1_relat_1(sK8)),sK5) = iProver_top
    | v1_xboole_0(k1_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1854,c_3545])).

cnf(c_4971,plain,
    ( v1_xboole_0(k1_relat_1(sK8)) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3950,c_1853])).

cnf(c_2584,plain,
    ( r1_tarski(k1_relat_1(sK7),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1837,c_1834])).

cnf(c_3546,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2584,c_1850])).

cnf(c_4048,plain,
    ( r2_hidden(sK0(k1_relat_1(sK7)),sK5) = iProver_top
    | v1_xboole_0(k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1854,c_3546])).

cnf(c_5076,plain,
    ( v1_xboole_0(k1_relat_1(sK7)) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4048,c_1853])).

cnf(c_5245,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4880,c_32,c_34,c_35,c_26,c_37,c_2059,c_2062,c_2137,c_2268,c_2416,c_2751,c_2774,c_4475,c_4971,c_5076])).

cnf(c_5247,plain,
    ( ~ v1_xboole_0(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5245])).

cnf(c_1377,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_10395,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_10397,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10395])).

cnf(c_1384,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2254,plain,
    ( X0 != k2_zfmisc_1(sK5,sK6)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1384])).

cnf(c_2561,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK5,sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2254])).

cnf(c_15233,plain,
    ( k2_zfmisc_1(sK5,X0) != k2_zfmisc_1(sK5,sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,X0)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2561])).

cnf(c_15234,plain,
    ( k2_zfmisc_1(sK5,k1_xboole_0) != k2_zfmisc_1(sK5,sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_15233])).

cnf(c_17267,plain,
    ( r2_hidden(sK4(sK8,sK7),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4788,c_26,c_5,c_749,c_783,c_1396,c_2087,c_2211,c_2268,c_3441,c_3527,c_3526,c_4285,c_5247,c_10397,c_15234])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK7,X0) = k1_funct_1(sK8,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1840,plain,
    ( k1_funct_1(sK7,X0) = k1_funct_1(sK8,X0)
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_17273,plain,
    ( k1_funct_1(sK8,sK4(sK8,sK7)) = k1_funct_1(sK7,sK4(sK8,sK7)) ),
    inference(superposition,[status(thm)],[c_17267,c_1840])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK4(X1,X0)) != k1_funct_1(X1,sK4(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1845,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK4(X1,X0)) != k1_funct_1(X1,sK4(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_17538,plain,
    ( k1_relat_1(sK7) != k1_relat_1(sK8)
    | sK8 = sK7
    | v1_funct_1(sK8) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_17273,c_1845])).

cnf(c_17890,plain,
    ( k1_relat_1(sK7) != k1_relat_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17538,c_32,c_34,c_35,c_37,c_597,c_2059,c_2062])).

cnf(c_17893,plain,
    ( k1_relat_1(sK7) != sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3049,c_17890])).

cnf(c_17784,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_17785,plain,
    ( sK6 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17784])).

cnf(c_17787,plain,
    ( sK6 != k1_xboole_0
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_17785])).

cnf(c_2948,plain,
    ( ~ r2_hidden(sK2(sK8,X0),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5018,plain,
    ( ~ r2_hidden(sK2(sK8,sK7),sK7)
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2948])).

cnf(c_5019,plain,
    ( r2_hidden(sK2(sK8,sK7),sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5018])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1842,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3378,plain,
    ( v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1837,c_1842])).

cnf(c_3377,plain,
    ( v1_xboole_0(sK8) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1839,c_1842])).

cnf(c_2397,plain,
    ( ~ r2_hidden(sK2(sK8,sK7),sK8)
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2398,plain,
    ( r2_hidden(sK2(sK8,sK7),sK8) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2397])).

cnf(c_2112,plain,
    ( r2_hidden(sK2(sK8,sK7),sK8)
    | r2_hidden(sK2(sK8,sK7),sK7)
    | sK7 = sK8 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2113,plain,
    ( sK7 = sK8
    | r2_hidden(sK2(sK8,sK7),sK8) = iProver_top
    | r2_hidden(sK2(sK8,sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2112])).

cnf(c_94,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17893,c_17787,c_5019,c_3378,c_3377,c_3122,c_2398,c_2268,c_2113,c_94,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n021.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 09:36:19 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.71/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/0.96  
% 3.71/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/0.96  
% 3.71/0.96  ------  iProver source info
% 3.71/0.96  
% 3.71/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.71/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/0.96  git: non_committed_changes: false
% 3.71/0.96  git: last_make_outside_of_git: false
% 3.71/0.96  
% 3.71/0.96  ------ 
% 3.71/0.96  
% 3.71/0.96  ------ Input Options
% 3.71/0.96  
% 3.71/0.96  --out_options                           all
% 3.71/0.96  --tptp_safe_out                         true
% 3.71/0.96  --problem_path                          ""
% 3.71/0.96  --include_path                          ""
% 3.71/0.96  --clausifier                            res/vclausify_rel
% 3.71/0.96  --clausifier_options                    --mode clausify
% 3.71/0.96  --stdin                                 false
% 3.71/0.96  --stats_out                             all
% 3.71/0.96  
% 3.71/0.96  ------ General Options
% 3.71/0.96  
% 3.71/0.96  --fof                                   false
% 3.71/0.96  --time_out_real                         305.
% 3.71/0.96  --time_out_virtual                      -1.
% 3.71/0.96  --symbol_type_check                     false
% 3.71/0.96  --clausify_out                          false
% 3.71/0.96  --sig_cnt_out                           false
% 3.71/0.96  --trig_cnt_out                          false
% 3.71/0.96  --trig_cnt_out_tolerance                1.
% 3.71/0.96  --trig_cnt_out_sk_spl                   false
% 3.71/0.96  --abstr_cl_out                          false
% 3.71/0.96  
% 3.71/0.96  ------ Global Options
% 3.71/0.96  
% 3.71/0.96  --schedule                              default
% 3.71/0.96  --add_important_lit                     false
% 3.71/0.96  --prop_solver_per_cl                    1000
% 3.71/0.96  --min_unsat_core                        false
% 3.71/0.96  --soft_assumptions                      false
% 3.71/0.96  --soft_lemma_size                       3
% 3.71/0.96  --prop_impl_unit_size                   0
% 3.71/0.96  --prop_impl_unit                        []
% 3.71/0.96  --share_sel_clauses                     true
% 3.71/0.96  --reset_solvers                         false
% 3.71/0.96  --bc_imp_inh                            [conj_cone]
% 3.71/0.96  --conj_cone_tolerance                   3.
% 3.71/0.96  --extra_neg_conj                        none
% 3.71/0.96  --large_theory_mode                     true
% 3.71/0.96  --prolific_symb_bound                   200
% 3.71/0.96  --lt_threshold                          2000
% 3.71/0.96  --clause_weak_htbl                      true
% 3.71/0.96  --gc_record_bc_elim                     false
% 3.71/0.96  
% 3.71/0.96  ------ Preprocessing Options
% 3.71/0.96  
% 3.71/0.96  --preprocessing_flag                    true
% 3.71/0.96  --time_out_prep_mult                    0.1
% 3.71/0.96  --splitting_mode                        input
% 3.71/0.96  --splitting_grd                         true
% 3.71/0.96  --splitting_cvd                         false
% 3.71/0.96  --splitting_cvd_svl                     false
% 3.71/0.96  --splitting_nvd                         32
% 3.71/0.96  --sub_typing                            true
% 3.71/0.96  --prep_gs_sim                           true
% 3.71/0.96  --prep_unflatten                        true
% 3.71/0.96  --prep_res_sim                          true
% 3.71/0.96  --prep_upred                            true
% 3.71/0.96  --prep_sem_filter                       exhaustive
% 3.71/0.96  --prep_sem_filter_out                   false
% 3.71/0.96  --pred_elim                             true
% 3.71/0.96  --res_sim_input                         true
% 3.71/0.96  --eq_ax_congr_red                       true
% 3.71/0.96  --pure_diseq_elim                       true
% 3.71/0.96  --brand_transform                       false
% 3.71/0.96  --non_eq_to_eq                          false
% 3.71/0.96  --prep_def_merge                        true
% 3.71/0.96  --prep_def_merge_prop_impl              false
% 3.71/0.96  --prep_def_merge_mbd                    true
% 3.71/0.96  --prep_def_merge_tr_red                 false
% 3.71/0.96  --prep_def_merge_tr_cl                  false
% 3.71/0.96  --smt_preprocessing                     true
% 3.71/0.96  --smt_ac_axioms                         fast
% 3.71/0.96  --preprocessed_out                      false
% 3.71/0.96  --preprocessed_stats                    false
% 3.71/0.96  
% 3.71/0.96  ------ Abstraction refinement Options
% 3.71/0.96  
% 3.71/0.96  --abstr_ref                             []
% 3.71/0.96  --abstr_ref_prep                        false
% 3.71/0.96  --abstr_ref_until_sat                   false
% 3.71/0.96  --abstr_ref_sig_restrict                funpre
% 3.71/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/0.96  --abstr_ref_under                       []
% 3.71/0.96  
% 3.71/0.96  ------ SAT Options
% 3.71/0.96  
% 3.71/0.96  --sat_mode                              false
% 3.71/0.96  --sat_fm_restart_options                ""
% 3.71/0.96  --sat_gr_def                            false
% 3.71/0.96  --sat_epr_types                         true
% 3.71/0.96  --sat_non_cyclic_types                  false
% 3.71/0.96  --sat_finite_models                     false
% 3.71/0.96  --sat_fm_lemmas                         false
% 3.71/0.96  --sat_fm_prep                           false
% 3.71/0.96  --sat_fm_uc_incr                        true
% 3.71/0.96  --sat_out_model                         small
% 3.71/0.96  --sat_out_clauses                       false
% 3.71/0.96  
% 3.71/0.96  ------ QBF Options
% 3.71/0.96  
% 3.71/0.96  --qbf_mode                              false
% 3.71/0.96  --qbf_elim_univ                         false
% 3.71/0.96  --qbf_dom_inst                          none
% 3.71/0.96  --qbf_dom_pre_inst                      false
% 3.71/0.96  --qbf_sk_in                             false
% 3.71/0.96  --qbf_pred_elim                         true
% 3.71/0.96  --qbf_split                             512
% 3.71/0.96  
% 3.71/0.96  ------ BMC1 Options
% 3.71/0.96  
% 3.71/0.96  --bmc1_incremental                      false
% 3.71/0.96  --bmc1_axioms                           reachable_all
% 3.71/0.96  --bmc1_min_bound                        0
% 3.71/0.96  --bmc1_max_bound                        -1
% 3.71/0.96  --bmc1_max_bound_default                -1
% 3.71/0.96  --bmc1_symbol_reachability              true
% 3.71/0.96  --bmc1_property_lemmas                  false
% 3.71/0.96  --bmc1_k_induction                      false
% 3.71/0.96  --bmc1_non_equiv_states                 false
% 3.71/0.96  --bmc1_deadlock                         false
% 3.71/0.96  --bmc1_ucm                              false
% 3.71/0.96  --bmc1_add_unsat_core                   none
% 3.71/0.96  --bmc1_unsat_core_children              false
% 3.71/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/0.96  --bmc1_out_stat                         full
% 3.71/0.96  --bmc1_ground_init                      false
% 3.71/0.96  --bmc1_pre_inst_next_state              false
% 3.71/0.96  --bmc1_pre_inst_state                   false
% 3.71/0.96  --bmc1_pre_inst_reach_state             false
% 3.71/0.96  --bmc1_out_unsat_core                   false
% 3.71/0.96  --bmc1_aig_witness_out                  false
% 3.71/0.96  --bmc1_verbose                          false
% 3.71/0.96  --bmc1_dump_clauses_tptp                false
% 3.71/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.71/0.96  --bmc1_dump_file                        -
% 3.71/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.71/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.71/0.96  --bmc1_ucm_extend_mode                  1
% 3.71/0.96  --bmc1_ucm_init_mode                    2
% 3.71/0.96  --bmc1_ucm_cone_mode                    none
% 3.71/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.71/0.96  --bmc1_ucm_relax_model                  4
% 3.71/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.71/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/0.96  --bmc1_ucm_layered_model                none
% 3.71/0.96  --bmc1_ucm_max_lemma_size               10
% 3.71/0.96  
% 3.71/0.96  ------ AIG Options
% 3.71/0.96  
% 3.71/0.96  --aig_mode                              false
% 3.71/0.96  
% 3.71/0.96  ------ Instantiation Options
% 3.71/0.96  
% 3.71/0.96  --instantiation_flag                    true
% 3.71/0.96  --inst_sos_flag                         false
% 3.71/0.96  --inst_sos_phase                        true
% 3.71/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/0.96  --inst_lit_sel_side                     num_symb
% 3.71/0.96  --inst_solver_per_active                1400
% 3.71/0.96  --inst_solver_calls_frac                1.
% 3.71/0.96  --inst_passive_queue_type               priority_queues
% 3.71/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/0.96  --inst_passive_queues_freq              [25;2]
% 3.71/0.96  --inst_dismatching                      true
% 3.71/0.96  --inst_eager_unprocessed_to_passive     true
% 3.71/0.96  --inst_prop_sim_given                   true
% 3.71/0.96  --inst_prop_sim_new                     false
% 3.71/0.96  --inst_subs_new                         false
% 3.71/0.96  --inst_eq_res_simp                      false
% 3.71/0.96  --inst_subs_given                       false
% 3.71/0.96  --inst_orphan_elimination               true
% 3.71/0.96  --inst_learning_loop_flag               true
% 3.71/0.96  --inst_learning_start                   3000
% 3.71/0.96  --inst_learning_factor                  2
% 3.71/0.96  --inst_start_prop_sim_after_learn       3
% 3.71/0.96  --inst_sel_renew                        solver
% 3.71/0.96  --inst_lit_activity_flag                true
% 3.71/0.96  --inst_restr_to_given                   false
% 3.71/0.96  --inst_activity_threshold               500
% 3.71/0.96  --inst_out_proof                        true
% 3.71/0.96  
% 3.71/0.96  ------ Resolution Options
% 3.71/0.96  
% 3.71/0.96  --resolution_flag                       true
% 3.71/0.96  --res_lit_sel                           adaptive
% 3.71/0.96  --res_lit_sel_side                      none
% 3.71/0.96  --res_ordering                          kbo
% 3.71/0.96  --res_to_prop_solver                    active
% 3.71/0.96  --res_prop_simpl_new                    false
% 3.71/0.96  --res_prop_simpl_given                  true
% 3.71/0.96  --res_passive_queue_type                priority_queues
% 3.71/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/0.96  --res_passive_queues_freq               [15;5]
% 3.71/0.96  --res_forward_subs                      full
% 3.71/0.96  --res_backward_subs                     full
% 3.71/0.96  --res_forward_subs_resolution           true
% 3.71/0.96  --res_backward_subs_resolution          true
% 3.71/0.96  --res_orphan_elimination                true
% 3.71/0.96  --res_time_limit                        2.
% 3.71/0.96  --res_out_proof                         true
% 3.71/0.96  
% 3.71/0.96  ------ Superposition Options
% 3.71/0.96  
% 3.71/0.96  --superposition_flag                    true
% 3.71/0.96  --sup_passive_queue_type                priority_queues
% 3.71/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.71/0.96  --demod_completeness_check              fast
% 3.71/0.96  --demod_use_ground                      true
% 3.71/0.96  --sup_to_prop_solver                    passive
% 3.71/0.96  --sup_prop_simpl_new                    true
% 3.71/0.96  --sup_prop_simpl_given                  true
% 3.71/0.96  --sup_fun_splitting                     false
% 3.71/0.96  --sup_smt_interval                      50000
% 3.71/0.96  
% 3.71/0.96  ------ Superposition Simplification Setup
% 3.71/0.96  
% 3.71/0.96  --sup_indices_passive                   []
% 3.71/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.96  --sup_full_bw                           [BwDemod]
% 3.71/0.96  --sup_immed_triv                        [TrivRules]
% 3.71/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.96  --sup_immed_bw_main                     []
% 3.71/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/0.96  
% 3.71/0.96  ------ Combination Options
% 3.71/0.96  
% 3.71/0.96  --comb_res_mult                         3
% 3.71/0.96  --comb_sup_mult                         2
% 3.71/0.96  --comb_inst_mult                        10
% 3.71/0.96  
% 3.71/0.96  ------ Debug Options
% 3.71/0.96  
% 3.71/0.96  --dbg_backtrace                         false
% 3.71/0.96  --dbg_dump_prop_clauses                 false
% 3.71/0.96  --dbg_dump_prop_clauses_file            -
% 3.71/0.96  --dbg_out_stat                          false
% 3.71/0.96  ------ Parsing...
% 3.71/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/0.96  
% 3.71/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.71/0.96  
% 3.71/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/0.96  
% 3.71/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/0.96  ------ Proving...
% 3.71/0.96  ------ Problem Properties 
% 3.71/0.96  
% 3.71/0.96  
% 3.71/0.96  clauses                                 27
% 3.71/0.96  conjectures                             5
% 3.71/0.96  EPR                                     5
% 3.71/0.96  Horn                                    19
% 3.71/0.96  unary                                   6
% 3.71/0.96  binary                                  11
% 3.71/0.96  lits                                    68
% 3.71/0.96  lits eq                                 24
% 3.71/0.96  fd_pure                                 0
% 3.71/0.96  fd_pseudo                               0
% 3.71/0.96  fd_cond                                 0
% 3.71/0.96  fd_pseudo_cond                          4
% 3.71/0.96  AC symbols                              0
% 3.71/0.96  
% 3.71/0.96  ------ Schedule dynamic 5 is on 
% 3.71/0.96  
% 3.71/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.71/0.96  
% 3.71/0.96  
% 3.71/0.96  ------ 
% 3.71/0.96  Current options:
% 3.71/0.96  ------ 
% 3.71/0.96  
% 3.71/0.96  ------ Input Options
% 3.71/0.96  
% 3.71/0.96  --out_options                           all
% 3.71/0.96  --tptp_safe_out                         true
% 3.71/0.96  --problem_path                          ""
% 3.71/0.96  --include_path                          ""
% 3.71/0.96  --clausifier                            res/vclausify_rel
% 3.71/0.96  --clausifier_options                    --mode clausify
% 3.71/0.96  --stdin                                 false
% 3.71/0.96  --stats_out                             all
% 3.71/0.96  
% 3.71/0.96  ------ General Options
% 3.71/0.96  
% 3.71/0.96  --fof                                   false
% 3.71/0.96  --time_out_real                         305.
% 3.71/0.96  --time_out_virtual                      -1.
% 3.71/0.96  --symbol_type_check                     false
% 3.71/0.96  --clausify_out                          false
% 3.71/0.96  --sig_cnt_out                           false
% 3.71/0.96  --trig_cnt_out                          false
% 3.71/0.96  --trig_cnt_out_tolerance                1.
% 3.71/0.96  --trig_cnt_out_sk_spl                   false
% 3.71/0.96  --abstr_cl_out                          false
% 3.71/0.96  
% 3.71/0.96  ------ Global Options
% 3.71/0.96  
% 3.71/0.96  --schedule                              default
% 3.71/0.96  --add_important_lit                     false
% 3.71/0.96  --prop_solver_per_cl                    1000
% 3.71/0.96  --min_unsat_core                        false
% 3.71/0.96  --soft_assumptions                      false
% 3.71/0.96  --soft_lemma_size                       3
% 3.71/0.96  --prop_impl_unit_size                   0
% 3.71/0.96  --prop_impl_unit                        []
% 3.71/0.96  --share_sel_clauses                     true
% 3.71/0.96  --reset_solvers                         false
% 3.71/0.96  --bc_imp_inh                            [conj_cone]
% 3.71/0.96  --conj_cone_tolerance                   3.
% 3.71/0.96  --extra_neg_conj                        none
% 3.71/0.96  --large_theory_mode                     true
% 3.71/0.96  --prolific_symb_bound                   200
% 3.71/0.96  --lt_threshold                          2000
% 3.71/0.96  --clause_weak_htbl                      true
% 3.71/0.96  --gc_record_bc_elim                     false
% 3.71/0.96  
% 3.71/0.96  ------ Preprocessing Options
% 3.71/0.96  
% 3.71/0.96  --preprocessing_flag                    true
% 3.71/0.96  --time_out_prep_mult                    0.1
% 3.71/0.96  --splitting_mode                        input
% 3.71/0.96  --splitting_grd                         true
% 3.71/0.96  --splitting_cvd                         false
% 3.71/0.96  --splitting_cvd_svl                     false
% 3.71/0.96  --splitting_nvd                         32
% 3.71/0.96  --sub_typing                            true
% 3.71/0.96  --prep_gs_sim                           true
% 3.71/0.96  --prep_unflatten                        true
% 3.71/0.96  --prep_res_sim                          true
% 3.71/0.96  --prep_upred                            true
% 3.71/0.96  --prep_sem_filter                       exhaustive
% 3.71/0.96  --prep_sem_filter_out                   false
% 3.71/0.96  --pred_elim                             true
% 3.71/0.96  --res_sim_input                         true
% 3.71/0.96  --eq_ax_congr_red                       true
% 3.71/0.96  --pure_diseq_elim                       true
% 3.71/0.96  --brand_transform                       false
% 3.71/0.96  --non_eq_to_eq                          false
% 3.71/0.96  --prep_def_merge                        true
% 3.71/0.96  --prep_def_merge_prop_impl              false
% 3.71/0.96  --prep_def_merge_mbd                    true
% 3.71/0.96  --prep_def_merge_tr_red                 false
% 3.71/0.96  --prep_def_merge_tr_cl                  false
% 3.71/0.96  --smt_preprocessing                     true
% 3.71/0.96  --smt_ac_axioms                         fast
% 3.71/0.96  --preprocessed_out                      false
% 3.71/0.96  --preprocessed_stats                    false
% 3.71/0.96  
% 3.71/0.96  ------ Abstraction refinement Options
% 3.71/0.96  
% 3.71/0.96  --abstr_ref                             []
% 3.71/0.96  --abstr_ref_prep                        false
% 3.71/0.96  --abstr_ref_until_sat                   false
% 3.71/0.96  --abstr_ref_sig_restrict                funpre
% 3.71/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/0.96  --abstr_ref_under                       []
% 3.71/0.96  
% 3.71/0.96  ------ SAT Options
% 3.71/0.96  
% 3.71/0.96  --sat_mode                              false
% 3.71/0.96  --sat_fm_restart_options                ""
% 3.71/0.96  --sat_gr_def                            false
% 3.71/0.96  --sat_epr_types                         true
% 3.71/0.96  --sat_non_cyclic_types                  false
% 3.71/0.96  --sat_finite_models                     false
% 3.71/0.96  --sat_fm_lemmas                         false
% 3.71/0.96  --sat_fm_prep                           false
% 3.71/0.96  --sat_fm_uc_incr                        true
% 3.71/0.96  --sat_out_model                         small
% 3.71/0.96  --sat_out_clauses                       false
% 3.71/0.96  
% 3.71/0.96  ------ QBF Options
% 3.71/0.96  
% 3.71/0.96  --qbf_mode                              false
% 3.71/0.96  --qbf_elim_univ                         false
% 3.71/0.96  --qbf_dom_inst                          none
% 3.71/0.96  --qbf_dom_pre_inst                      false
% 3.71/0.96  --qbf_sk_in                             false
% 3.71/0.96  --qbf_pred_elim                         true
% 3.71/0.96  --qbf_split                             512
% 3.71/0.96  
% 3.71/0.96  ------ BMC1 Options
% 3.71/0.96  
% 3.71/0.96  --bmc1_incremental                      false
% 3.71/0.96  --bmc1_axioms                           reachable_all
% 3.71/0.96  --bmc1_min_bound                        0
% 3.71/0.96  --bmc1_max_bound                        -1
% 3.71/0.96  --bmc1_max_bound_default                -1
% 3.71/0.96  --bmc1_symbol_reachability              true
% 3.71/0.96  --bmc1_property_lemmas                  false
% 3.71/0.96  --bmc1_k_induction                      false
% 3.71/0.96  --bmc1_non_equiv_states                 false
% 3.71/0.96  --bmc1_deadlock                         false
% 3.71/0.96  --bmc1_ucm                              false
% 3.71/0.96  --bmc1_add_unsat_core                   none
% 3.71/0.96  --bmc1_unsat_core_children              false
% 3.71/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/0.96  --bmc1_out_stat                         full
% 3.71/0.96  --bmc1_ground_init                      false
% 3.71/0.96  --bmc1_pre_inst_next_state              false
% 3.71/0.96  --bmc1_pre_inst_state                   false
% 3.71/0.96  --bmc1_pre_inst_reach_state             false
% 3.71/0.96  --bmc1_out_unsat_core                   false
% 3.71/0.96  --bmc1_aig_witness_out                  false
% 3.71/0.96  --bmc1_verbose                          false
% 3.71/0.96  --bmc1_dump_clauses_tptp                false
% 3.71/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.71/0.96  --bmc1_dump_file                        -
% 3.71/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.71/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.71/0.96  --bmc1_ucm_extend_mode                  1
% 3.71/0.96  --bmc1_ucm_init_mode                    2
% 3.71/0.96  --bmc1_ucm_cone_mode                    none
% 3.71/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.71/0.96  --bmc1_ucm_relax_model                  4
% 3.71/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.71/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/0.96  --bmc1_ucm_layered_model                none
% 3.71/0.96  --bmc1_ucm_max_lemma_size               10
% 3.71/0.96  
% 3.71/0.96  ------ AIG Options
% 3.71/0.96  
% 3.71/0.96  --aig_mode                              false
% 3.71/0.96  
% 3.71/0.96  ------ Instantiation Options
% 3.71/0.96  
% 3.71/0.96  --instantiation_flag                    true
% 3.71/0.96  --inst_sos_flag                         false
% 3.71/0.96  --inst_sos_phase                        true
% 3.71/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/0.96  --inst_lit_sel_side                     none
% 3.71/0.96  --inst_solver_per_active                1400
% 3.71/0.96  --inst_solver_calls_frac                1.
% 3.71/0.96  --inst_passive_queue_type               priority_queues
% 3.71/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/0.96  --inst_passive_queues_freq              [25;2]
% 3.71/0.96  --inst_dismatching                      true
% 3.71/0.96  --inst_eager_unprocessed_to_passive     true
% 3.71/0.96  --inst_prop_sim_given                   true
% 3.71/0.96  --inst_prop_sim_new                     false
% 3.71/0.96  --inst_subs_new                         false
% 3.71/0.96  --inst_eq_res_simp                      false
% 3.71/0.96  --inst_subs_given                       false
% 3.71/0.96  --inst_orphan_elimination               true
% 3.71/0.96  --inst_learning_loop_flag               true
% 3.71/0.96  --inst_learning_start                   3000
% 3.71/0.96  --inst_learning_factor                  2
% 3.71/0.96  --inst_start_prop_sim_after_learn       3
% 3.71/0.96  --inst_sel_renew                        solver
% 3.71/0.96  --inst_lit_activity_flag                true
% 3.71/0.96  --inst_restr_to_given                   false
% 3.71/0.96  --inst_activity_threshold               500
% 3.71/0.96  --inst_out_proof                        true
% 3.71/0.96  
% 3.71/0.96  ------ Resolution Options
% 3.71/0.96  
% 3.71/0.96  --resolution_flag                       false
% 3.71/0.96  --res_lit_sel                           adaptive
% 3.71/0.96  --res_lit_sel_side                      none
% 3.71/0.96  --res_ordering                          kbo
% 3.71/0.96  --res_to_prop_solver                    active
% 3.71/0.96  --res_prop_simpl_new                    false
% 3.71/0.96  --res_prop_simpl_given                  true
% 3.71/0.96  --res_passive_queue_type                priority_queues
% 3.71/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/0.96  --res_passive_queues_freq               [15;5]
% 3.71/0.96  --res_forward_subs                      full
% 3.71/0.96  --res_backward_subs                     full
% 3.71/0.96  --res_forward_subs_resolution           true
% 3.71/0.96  --res_backward_subs_resolution          true
% 3.71/0.96  --res_orphan_elimination                true
% 3.71/0.96  --res_time_limit                        2.
% 3.71/0.96  --res_out_proof                         true
% 3.71/0.96  
% 3.71/0.96  ------ Superposition Options
% 3.71/0.96  
% 3.71/0.96  --superposition_flag                    true
% 3.71/0.96  --sup_passive_queue_type                priority_queues
% 3.71/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.71/0.96  --demod_completeness_check              fast
% 3.71/0.96  --demod_use_ground                      true
% 3.71/0.96  --sup_to_prop_solver                    passive
% 3.71/0.96  --sup_prop_simpl_new                    true
% 3.71/0.96  --sup_prop_simpl_given                  true
% 3.71/0.96  --sup_fun_splitting                     false
% 3.71/0.96  --sup_smt_interval                      50000
% 3.71/0.96  
% 3.71/0.96  ------ Superposition Simplification Setup
% 3.71/0.96  
% 3.71/0.96  --sup_indices_passive                   []
% 3.71/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.96  --sup_full_bw                           [BwDemod]
% 3.71/0.96  --sup_immed_triv                        [TrivRules]
% 3.71/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.96  --sup_immed_bw_main                     []
% 3.71/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/0.96  
% 3.71/0.96  ------ Combination Options
% 3.71/0.96  
% 3.71/0.96  --comb_res_mult                         3
% 3.71/0.96  --comb_sup_mult                         2
% 3.71/0.96  --comb_inst_mult                        10
% 3.71/0.96  
% 3.71/0.96  ------ Debug Options
% 3.71/0.96  
% 3.71/0.96  --dbg_backtrace                         false
% 3.71/0.96  --dbg_dump_prop_clauses                 false
% 3.71/0.96  --dbg_dump_prop_clauses_file            -
% 3.71/0.96  --dbg_out_stat                          false
% 3.71/0.96  
% 3.71/0.96  
% 3.71/0.96  
% 3.71/0.96  
% 3.71/0.96  ------ Proving...
% 3.71/0.96  
% 3.71/0.96  
% 3.71/0.96  % SZS status Theorem for theBenchmark.p
% 3.71/0.96  
% 3.71/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/0.96  
% 3.71/0.96  fof(f13,axiom,(
% 3.71/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.96  
% 3.71/0.96  fof(f28,plain,(
% 3.71/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.96    inference(ennf_transformation,[],[f13])).
% 3.71/0.96  
% 3.71/0.96  fof(f29,plain,(
% 3.71/0.96    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.96    inference(flattening,[],[f28])).
% 3.71/0.96  
% 3.71/0.96  fof(f48,plain,(
% 3.71/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.96    inference(nnf_transformation,[],[f29])).
% 3.71/0.96  
% 3.71/0.96  fof(f70,plain,(
% 3.71/0.96    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.96    inference(cnf_transformation,[],[f48])).
% 3.71/0.96  
% 3.71/0.96  fof(f14,conjecture,(
% 3.71/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.96  
% 3.71/0.96  fof(f15,negated_conjecture,(
% 3.71/0.96    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.71/0.96    inference(negated_conjecture,[],[f14])).
% 3.71/0.96  
% 3.71/0.96  fof(f30,plain,(
% 3.71/0.96    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.71/0.96    inference(ennf_transformation,[],[f15])).
% 3.71/0.96  
% 3.71/0.96  fof(f31,plain,(
% 3.71/0.96    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.71/0.96    inference(flattening,[],[f30])).
% 3.71/0.96  
% 3.71/0.96  fof(f50,plain,(
% 3.71/0.96    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK8) & ! [X4] : (k1_funct_1(sK8,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK8,X0,X1) & v1_funct_1(sK8))) )),
% 3.71/0.96    introduced(choice_axiom,[])).
% 3.71/0.96  
% 3.71/0.96  fof(f49,plain,(
% 3.71/0.96    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK5,sK6,sK7,X3) & ! [X4] : (k1_funct_1(sK7,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 3.71/0.96    introduced(choice_axiom,[])).
% 3.71/0.96  
% 3.71/0.96  fof(f51,plain,(
% 3.71/0.96    (~r2_relset_1(sK5,sK6,sK7,sK8) & ! [X4] : (k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4) | ~r2_hidden(X4,sK5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)),
% 3.71/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f31,f50,f49])).
% 3.71/0.96  
% 3.71/0.96  fof(f80,plain,(
% 3.71/0.96    v1_funct_2(sK8,sK5,sK6)),
% 3.71/0.96    inference(cnf_transformation,[],[f51])).
% 3.71/0.96  
% 3.71/0.96  fof(f81,plain,(
% 3.71/0.96    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.71/0.96    inference(cnf_transformation,[],[f51])).
% 3.71/0.96  
% 3.71/0.96  fof(f11,axiom,(
% 3.71/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.96  
% 3.71/0.96  fof(f25,plain,(
% 3.71/0.96    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.96    inference(ennf_transformation,[],[f11])).
% 3.71/0.96  
% 3.71/0.96  fof(f68,plain,(
% 3.71/0.96    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.96    inference(cnf_transformation,[],[f25])).
% 3.71/0.96  
% 3.71/0.96  fof(f77,plain,(
% 3.71/0.96    v1_funct_2(sK7,sK5,sK6)),
% 3.71/0.96    inference(cnf_transformation,[],[f51])).
% 3.71/0.96  
% 3.71/0.96  fof(f78,plain,(
% 3.71/0.96    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.71/0.96    inference(cnf_transformation,[],[f51])).
% 3.71/0.96  
% 3.71/0.96  fof(f7,axiom,(
% 3.71/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 3.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.96  
% 3.71/0.96  fof(f20,plain,(
% 3.71/0.96    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.71/0.96    inference(ennf_transformation,[],[f7])).
% 3.71/0.96  
% 3.71/0.96  fof(f21,plain,(
% 3.71/0.96    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.71/0.96    inference(flattening,[],[f20])).
% 3.71/0.96  
% 3.71/0.96  fof(f46,plain,(
% 3.71/0.96    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 3.71/0.96    introduced(choice_axiom,[])).
% 3.71/0.96  
% 3.71/0.96  fof(f47,plain,(
% 3.71/0.96    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.71/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f46])).
% 3.71/0.96  
% 3.71/0.96  fof(f63,plain,(
% 3.71/0.96    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/0.96    inference(cnf_transformation,[],[f47])).
% 3.71/0.96  
% 3.71/0.96  fof(f79,plain,(
% 3.71/0.96    v1_funct_1(sK8)),
% 3.71/0.96    inference(cnf_transformation,[],[f51])).
% 3.71/0.96  
% 3.71/0.96  fof(f8,axiom,(
% 3.71/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.96  
% 3.71/0.96  fof(f22,plain,(
% 3.71/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.96    inference(ennf_transformation,[],[f8])).
% 3.71/0.96  
% 3.71/0.96  fof(f65,plain,(
% 3.71/0.96    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.96    inference(cnf_transformation,[],[f22])).
% 3.71/0.96  
% 3.71/0.96  fof(f76,plain,(
% 3.71/0.96    v1_funct_1(sK7)),
% 3.71/0.96    inference(cnf_transformation,[],[f51])).
% 3.71/0.96  
% 3.71/0.96  fof(f5,axiom,(
% 3.71/0.96    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.96  
% 3.71/0.96  fof(f43,plain,(
% 3.71/0.96    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK3(X0),X0))),
% 3.71/0.96    introduced(choice_axiom,[])).
% 3.71/0.96  
% 3.71/0.96  fof(f44,plain,(
% 3.71/0.96    ! [X0] : m1_subset_1(sK3(X0),X0)),
% 3.71/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f5,f43])).
% 3.71/0.96  
% 3.71/0.96  fof(f60,plain,(
% 3.71/0.96    ( ! [X0] : (m1_subset_1(sK3(X0),X0)) )),
% 3.71/0.96    inference(cnf_transformation,[],[f44])).
% 3.71/0.96  
% 3.71/0.96  fof(f12,axiom,(
% 3.71/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.96  
% 3.71/0.96  fof(f26,plain,(
% 3.71/0.96    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.71/0.96    inference(ennf_transformation,[],[f12])).
% 3.71/0.96  
% 3.71/0.96  fof(f27,plain,(
% 3.71/0.96    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.96    inference(flattening,[],[f26])).
% 3.71/0.96  
% 3.71/0.96  fof(f69,plain,(
% 3.71/0.96    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.96    inference(cnf_transformation,[],[f27])).
% 3.71/0.96  
% 3.71/0.96  fof(f83,plain,(
% 3.71/0.96    ~r2_relset_1(sK5,sK6,sK7,sK8)),
% 3.71/0.96    inference(cnf_transformation,[],[f51])).
% 3.71/0.96  
% 3.71/0.96  fof(f9,axiom,(
% 3.71/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.96  
% 3.71/0.96  fof(f16,plain,(
% 3.71/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.71/0.96    inference(pure_predicate_removal,[],[f9])).
% 3.71/0.96  
% 3.71/0.96  fof(f23,plain,(
% 3.71/0.96    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.96    inference(ennf_transformation,[],[f16])).
% 3.71/0.96  
% 3.71/0.96  fof(f66,plain,(
% 3.71/0.96    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.96    inference(cnf_transformation,[],[f23])).
% 3.71/0.96  
% 3.71/0.96  fof(f6,axiom,(
% 3.71/0.96    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.96  
% 3.71/0.96  fof(f19,plain,(
% 3.71/0.96    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.71/0.96    inference(ennf_transformation,[],[f6])).
% 3.71/0.96  
% 3.71/0.96  fof(f45,plain,(
% 3.71/0.96    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.71/0.96    inference(nnf_transformation,[],[f19])).
% 3.71/0.96  
% 3.71/0.96  fof(f61,plain,(
% 3.71/0.96    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.71/0.96    inference(cnf_transformation,[],[f45])).
% 3.71/0.96  
% 3.71/0.96  fof(f2,axiom,(
% 3.71/0.96    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.96  
% 3.71/0.96  fof(f17,plain,(
% 3.71/0.96    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.71/0.96    inference(ennf_transformation,[],[f2])).
% 3.71/0.96  
% 3.71/0.96  fof(f36,plain,(
% 3.71/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.71/0.96    inference(nnf_transformation,[],[f17])).
% 3.71/0.96  
% 3.71/0.96  fof(f37,plain,(
% 3.71/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.71/0.96    inference(rectify,[],[f36])).
% 3.71/0.96  
% 3.71/0.96  fof(f38,plain,(
% 3.71/0.96    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.71/0.96    introduced(choice_axiom,[])).
% 3.71/0.96  
% 3.71/0.96  fof(f39,plain,(
% 3.71/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.71/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 3.71/0.96  
% 3.71/0.96  fof(f54,plain,(
% 3.71/0.96    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.71/0.96    inference(cnf_transformation,[],[f39])).
% 3.71/0.96  
% 3.71/0.96  fof(f3,axiom,(
% 3.71/0.96    v1_xboole_0(k1_xboole_0)),
% 3.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.96  
% 3.71/0.96  fof(f57,plain,(
% 3.71/0.96    v1_xboole_0(k1_xboole_0)),
% 3.71/0.96    inference(cnf_transformation,[],[f3])).
% 3.71/0.96  
% 3.71/0.96  fof(f74,plain,(
% 3.71/0.96    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.96    inference(cnf_transformation,[],[f48])).
% 3.71/0.96  
% 3.71/0.96  fof(f86,plain,(
% 3.71/0.96    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.71/0.96    inference(equality_resolution,[],[f74])).
% 3.71/0.96  
% 3.71/0.96  fof(f1,axiom,(
% 3.71/0.96    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.96  
% 3.71/0.96  fof(f32,plain,(
% 3.71/0.96    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.71/0.96    inference(nnf_transformation,[],[f1])).
% 3.71/0.96  
% 3.71/0.96  fof(f33,plain,(
% 3.71/0.96    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.71/0.96    inference(rectify,[],[f32])).
% 3.71/0.96  
% 3.71/0.96  fof(f34,plain,(
% 3.71/0.96    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.71/0.96    introduced(choice_axiom,[])).
% 3.71/0.96  
% 3.71/0.96  fof(f35,plain,(
% 3.71/0.96    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.71/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.71/0.96  
% 3.71/0.96  fof(f52,plain,(
% 3.71/0.96    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.71/0.96    inference(cnf_transformation,[],[f35])).
% 3.71/0.96  
% 3.71/0.96  fof(f4,axiom,(
% 3.71/0.96    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.96  
% 3.71/0.96  fof(f18,plain,(
% 3.71/0.96    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.71/0.96    inference(ennf_transformation,[],[f4])).
% 3.71/0.96  
% 3.71/0.96  fof(f40,plain,(
% 3.71/0.96    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.71/0.96    inference(nnf_transformation,[],[f18])).
% 3.71/0.96  
% 3.71/0.96  fof(f41,plain,(
% 3.71/0.96    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 3.71/0.96    introduced(choice_axiom,[])).
% 3.71/0.96  
% 3.71/0.96  fof(f42,plain,(
% 3.71/0.96    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 3.71/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 3.71/0.96  
% 3.71/0.96  fof(f58,plain,(
% 3.71/0.96    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 3.71/0.96    inference(cnf_transformation,[],[f42])).
% 3.71/0.96  
% 3.71/0.96  fof(f53,plain,(
% 3.71/0.96    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.71/0.96    inference(cnf_transformation,[],[f35])).
% 3.71/0.96  
% 3.71/0.96  fof(f82,plain,(
% 3.71/0.96    ( ! [X4] : (k1_funct_1(sK7,X4) = k1_funct_1(sK8,X4) | ~r2_hidden(X4,sK5)) )),
% 3.71/0.96    inference(cnf_transformation,[],[f51])).
% 3.71/0.96  
% 3.71/0.96  fof(f64,plain,(
% 3.71/0.96    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/0.96    inference(cnf_transformation,[],[f47])).
% 3.71/0.96  
% 3.71/0.96  fof(f10,axiom,(
% 3.71/0.96    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.71/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/0.96  
% 3.71/0.96  fof(f24,plain,(
% 3.71/0.96    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.71/0.96    inference(ennf_transformation,[],[f10])).
% 3.71/0.96  
% 3.71/0.96  fof(f67,plain,(
% 3.71/0.96    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.71/0.96    inference(cnf_transformation,[],[f24])).
% 3.71/0.96  
% 3.71/0.96  cnf(c_23,plain,
% 3.71/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.96      | k1_relset_1(X1,X2,X0) = X1
% 3.71/0.96      | k1_xboole_0 = X2 ),
% 3.71/0.96      inference(cnf_transformation,[],[f70]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_27,negated_conjecture,
% 3.71/0.96      ( v1_funct_2(sK8,sK5,sK6) ),
% 3.71/0.96      inference(cnf_transformation,[],[f80]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_516,plain,
% 3.71/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.96      | k1_relset_1(X1,X2,X0) = X1
% 3.71/0.96      | sK8 != X0
% 3.71/0.96      | sK6 != X2
% 3.71/0.96      | sK5 != X1
% 3.71/0.96      | k1_xboole_0 = X2 ),
% 3.71/0.96      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_517,plain,
% 3.71/0.96      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.71/0.96      | k1_relset_1(sK5,sK6,sK8) = sK5
% 3.71/0.96      | k1_xboole_0 = sK6 ),
% 3.71/0.96      inference(unflattening,[status(thm)],[c_516]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_26,negated_conjecture,
% 3.71/0.96      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.71/0.96      inference(cnf_transformation,[],[f81]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_519,plain,
% 3.71/0.96      ( k1_relset_1(sK5,sK6,sK8) = sK5 | k1_xboole_0 = sK6 ),
% 3.71/0.96      inference(global_propositional_subsumption,
% 3.71/0.96                [status(thm)],
% 3.71/0.96                [c_517,c_26]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_1839,plain,
% 3.71/0.96      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.71/0.96      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_16,plain,
% 3.71/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.96      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.71/0.96      inference(cnf_transformation,[],[f68]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_1841,plain,
% 3.71/0.96      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.71/0.96      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.71/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_2693,plain,
% 3.71/0.96      ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
% 3.71/0.96      inference(superposition,[status(thm)],[c_1839,c_1841]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_3049,plain,
% 3.71/0.96      ( k1_relat_1(sK8) = sK5 | sK6 = k1_xboole_0 ),
% 3.71/0.96      inference(superposition,[status(thm)],[c_519,c_2693]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_30,negated_conjecture,
% 3.71/0.96      ( v1_funct_2(sK7,sK5,sK6) ),
% 3.71/0.96      inference(cnf_transformation,[],[f77]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_527,plain,
% 3.71/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.96      | k1_relset_1(X1,X2,X0) = X1
% 3.71/0.96      | sK7 != X0
% 3.71/0.96      | sK6 != X2
% 3.71/0.96      | sK5 != X1
% 3.71/0.96      | k1_xboole_0 = X2 ),
% 3.71/0.96      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_528,plain,
% 3.71/0.96      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.71/0.96      | k1_relset_1(sK5,sK6,sK7) = sK5
% 3.71/0.96      | k1_xboole_0 = sK6 ),
% 3.71/0.96      inference(unflattening,[status(thm)],[c_527]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_29,negated_conjecture,
% 3.71/0.96      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.71/0.96      inference(cnf_transformation,[],[f78]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_530,plain,
% 3.71/0.96      ( k1_relset_1(sK5,sK6,sK7) = sK5 | k1_xboole_0 = sK6 ),
% 3.71/0.96      inference(global_propositional_subsumption,
% 3.71/0.96                [status(thm)],
% 3.71/0.96                [c_528,c_29]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_1837,plain,
% 3.71/0.96      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.71/0.96      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_2694,plain,
% 3.71/0.96      ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
% 3.71/0.96      inference(superposition,[status(thm)],[c_1837,c_1841]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_3122,plain,
% 3.71/0.96      ( k1_relat_1(sK7) = sK5 | sK6 = k1_xboole_0 ),
% 3.71/0.96      inference(superposition,[status(thm)],[c_530,c_2694]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_12,plain,
% 3.71/0.96      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
% 3.71/0.96      | ~ v1_funct_1(X1)
% 3.71/0.96      | ~ v1_funct_1(X0)
% 3.71/0.96      | ~ v1_relat_1(X1)
% 3.71/0.96      | ~ v1_relat_1(X0)
% 3.71/0.96      | X1 = X0
% 3.71/0.96      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 3.71/0.96      inference(cnf_transformation,[],[f63]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_1844,plain,
% 3.71/0.96      ( X0 = X1
% 3.71/0.96      | k1_relat_1(X1) != k1_relat_1(X0)
% 3.71/0.96      | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.71/0.96      | v1_funct_1(X0) != iProver_top
% 3.71/0.96      | v1_funct_1(X1) != iProver_top
% 3.71/0.96      | v1_relat_1(X1) != iProver_top
% 3.71/0.96      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_3710,plain,
% 3.71/0.96      ( k1_relat_1(X0) != sK5
% 3.71/0.96      | sK8 = X0
% 3.71/0.96      | sK6 = k1_xboole_0
% 3.71/0.96      | r2_hidden(sK4(sK8,X0),k1_relat_1(sK8)) = iProver_top
% 3.71/0.96      | v1_funct_1(X0) != iProver_top
% 3.71/0.96      | v1_funct_1(sK8) != iProver_top
% 3.71/0.96      | v1_relat_1(X0) != iProver_top
% 3.71/0.96      | v1_relat_1(sK8) != iProver_top ),
% 3.71/0.96      inference(superposition,[status(thm)],[c_3049,c_1844]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_28,negated_conjecture,
% 3.71/0.96      ( v1_funct_1(sK8) ),
% 3.71/0.96      inference(cnf_transformation,[],[f79]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_35,plain,
% 3.71/0.96      ( v1_funct_1(sK8) = iProver_top ),
% 3.71/0.96      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_37,plain,
% 3.71/0.96      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.71/0.96      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_13,plain,
% 3.71/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.96      | v1_relat_1(X0) ),
% 3.71/0.96      inference(cnf_transformation,[],[f65]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_2058,plain,
% 3.71/0.96      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.71/0.96      | v1_relat_1(sK8) ),
% 3.71/0.96      inference(instantiation,[status(thm)],[c_13]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_2059,plain,
% 3.71/0.96      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.71/0.96      | v1_relat_1(sK8) = iProver_top ),
% 3.71/0.96      inference(predicate_to_equality,[status(thm)],[c_2058]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_4754,plain,
% 3.71/0.96      ( v1_relat_1(X0) != iProver_top
% 3.71/0.96      | k1_relat_1(X0) != sK5
% 3.71/0.96      | sK8 = X0
% 3.71/0.96      | sK6 = k1_xboole_0
% 3.71/0.96      | r2_hidden(sK4(sK8,X0),k1_relat_1(sK8)) = iProver_top
% 3.71/0.96      | v1_funct_1(X0) != iProver_top ),
% 3.71/0.96      inference(global_propositional_subsumption,
% 3.71/0.96                [status(thm)],
% 3.71/0.96                [c_3710,c_35,c_37,c_2059]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_4755,plain,
% 3.71/0.96      ( k1_relat_1(X0) != sK5
% 3.71/0.96      | sK8 = X0
% 3.71/0.96      | sK6 = k1_xboole_0
% 3.71/0.96      | r2_hidden(sK4(sK8,X0),k1_relat_1(sK8)) = iProver_top
% 3.71/0.96      | v1_funct_1(X0) != iProver_top
% 3.71/0.96      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.96      inference(renaming,[status(thm)],[c_4754]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_4767,plain,
% 3.71/0.96      ( sK8 = sK7
% 3.71/0.96      | sK6 = k1_xboole_0
% 3.71/0.96      | r2_hidden(sK4(sK8,sK7),k1_relat_1(sK8)) = iProver_top
% 3.71/0.96      | v1_funct_1(sK7) != iProver_top
% 3.71/0.96      | v1_relat_1(sK7) != iProver_top ),
% 3.71/0.96      inference(superposition,[status(thm)],[c_3122,c_4755]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_31,negated_conjecture,
% 3.71/0.96      ( v1_funct_1(sK7) ),
% 3.71/0.96      inference(cnf_transformation,[],[f76]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_32,plain,
% 3.71/0.96      ( v1_funct_1(sK7) = iProver_top ),
% 3.71/0.96      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_34,plain,
% 3.71/0.96      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.71/0.96      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_8,plain,
% 3.71/0.96      ( m1_subset_1(sK3(X0),X0) ),
% 3.71/0.96      inference(cnf_transformation,[],[f60]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_17,plain,
% 3.71/0.96      ( r2_relset_1(X0,X1,X2,X2)
% 3.71/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.71/0.96      inference(cnf_transformation,[],[f69]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_24,negated_conjecture,
% 3.71/0.96      ( ~ r2_relset_1(sK5,sK6,sK7,sK8) ),
% 3.71/0.96      inference(cnf_transformation,[],[f83]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_352,plain,
% 3.71/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.96      | sK8 != X0
% 3.71/0.96      | sK7 != X0
% 3.71/0.96      | sK6 != X2
% 3.71/0.96      | sK5 != X1 ),
% 3.71/0.96      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_353,plain,
% 3.71/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.71/0.96      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.71/0.96      | sK7 != sK8 ),
% 3.71/0.96      inference(unflattening,[status(thm)],[c_352]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_357,plain,
% 3.71/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.71/0.96      | sK7 != sK8 ),
% 3.71/0.96      inference(global_propositional_subsumption,
% 3.71/0.96                [status(thm)],
% 3.71/0.96                [c_353,c_26]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_596,plain,
% 3.71/0.96      ( k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) != X0
% 3.71/0.96      | sK3(X0) != X1
% 3.71/0.96      | sK8 != sK7 ),
% 3.71/0.96      inference(resolution_lifted,[status(thm)],[c_8,c_357]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_597,plain,
% 3.71/0.96      ( sK8 != sK7 ),
% 3.71/0.96      inference(unflattening,[status(thm)],[c_596]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_2061,plain,
% 3.71/0.96      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.71/0.96      | v1_relat_1(sK7) ),
% 3.71/0.96      inference(instantiation,[status(thm)],[c_13]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_2062,plain,
% 3.71/0.96      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.71/0.96      | v1_relat_1(sK7) = iProver_top ),
% 3.71/0.96      inference(predicate_to_equality,[status(thm)],[c_2061]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_4780,plain,
% 3.71/0.96      ( sK6 = k1_xboole_0
% 3.71/0.96      | r2_hidden(sK4(sK8,sK7),k1_relat_1(sK8)) = iProver_top ),
% 3.71/0.96      inference(global_propositional_subsumption,
% 3.71/0.96                [status(thm)],
% 3.71/0.96                [c_4767,c_32,c_34,c_597,c_2062]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_14,plain,
% 3.71/0.96      ( v4_relat_1(X0,X1)
% 3.71/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.71/0.96      inference(cnf_transformation,[],[f66]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_10,plain,
% 3.71/0.96      ( ~ v4_relat_1(X0,X1)
% 3.71/0.96      | r1_tarski(k1_relat_1(X0),X1)
% 3.71/0.96      | ~ v1_relat_1(X0) ),
% 3.71/0.96      inference(cnf_transformation,[],[f61]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_373,plain,
% 3.71/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.96      | r1_tarski(k1_relat_1(X0),X1)
% 3.71/0.96      | ~ v1_relat_1(X0) ),
% 3.71/0.96      inference(resolution,[status(thm)],[c_14,c_10]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_377,plain,
% 3.71/0.96      ( r1_tarski(k1_relat_1(X0),X1)
% 3.71/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.71/0.96      inference(global_propositional_subsumption,
% 3.71/0.96                [status(thm)],
% 3.71/0.96                [c_373,c_13]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_378,plain,
% 3.71/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.96      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.71/0.96      inference(renaming,[status(thm)],[c_377]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_1834,plain,
% 3.71/0.96      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.71/0.96      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.71/0.96      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_2583,plain,
% 3.71/0.96      ( r1_tarski(k1_relat_1(sK8),sK5) = iProver_top ),
% 3.71/0.96      inference(superposition,[status(thm)],[c_1839,c_1834]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_4,plain,
% 3.71/0.96      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.71/0.96      inference(cnf_transformation,[],[f54]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_1850,plain,
% 3.71/0.96      ( r1_tarski(X0,X1) != iProver_top
% 3.71/0.96      | r2_hidden(X2,X0) != iProver_top
% 3.71/0.96      | r2_hidden(X2,X1) = iProver_top ),
% 3.71/0.96      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_3545,plain,
% 3.71/0.96      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.71/0.96      | r2_hidden(X0,sK5) = iProver_top ),
% 3.71/0.96      inference(superposition,[status(thm)],[c_2583,c_1850]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_4788,plain,
% 3.71/0.96      ( sK6 = k1_xboole_0 | r2_hidden(sK4(sK8,sK7),sK5) = iProver_top ),
% 3.71/0.96      inference(superposition,[status(thm)],[c_4780,c_3545]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_5,plain,
% 3.71/0.96      ( v1_xboole_0(k1_xboole_0) ),
% 3.71/0.96      inference(cnf_transformation,[],[f57]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_19,plain,
% 3.71/0.96      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.71/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.71/0.96      | k1_xboole_0 = X1
% 3.71/0.96      | k1_xboole_0 = X0 ),
% 3.71/0.96      inference(cnf_transformation,[],[f86]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_454,plain,
% 3.71/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.71/0.96      | sK8 != X0
% 3.71/0.96      | sK6 != k1_xboole_0
% 3.71/0.96      | sK5 != X1
% 3.71/0.96      | k1_xboole_0 = X0
% 3.71/0.96      | k1_xboole_0 = X1 ),
% 3.71/0.96      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_455,plain,
% 3.71/0.96      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)))
% 3.71/0.96      | sK6 != k1_xboole_0
% 3.71/0.96      | k1_xboole_0 = sK8
% 3.71/0.96      | k1_xboole_0 = sK5 ),
% 3.71/0.96      inference(unflattening,[status(thm)],[c_454]) ).
% 3.71/0.96  
% 3.71/0.96  cnf(c_749,plain,
% 3.71/0.96      ( k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.71/0.97      | sK8 != sK8
% 3.71/0.97      | sK8 = k1_xboole_0
% 3.71/0.97      | sK6 != k1_xboole_0
% 3.71/0.97      | sK5 = k1_xboole_0 ),
% 3.71/0.97      inference(resolution_lifted,[status(thm)],[c_26,c_455]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_470,plain,
% 3.71/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.71/0.97      | sK7 != X0
% 3.71/0.97      | sK6 != k1_xboole_0
% 3.71/0.97      | sK5 != X1
% 3.71/0.97      | k1_xboole_0 = X0
% 3.71/0.97      | k1_xboole_0 = X1 ),
% 3.71/0.97      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_471,plain,
% 3.71/0.97      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)))
% 3.71/0.97      | sK6 != k1_xboole_0
% 3.71/0.97      | k1_xboole_0 = sK7
% 3.71/0.97      | k1_xboole_0 = sK5 ),
% 3.71/0.97      inference(unflattening,[status(thm)],[c_470]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_783,plain,
% 3.71/0.97      ( k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))
% 3.71/0.97      | sK7 != sK7
% 3.71/0.97      | sK7 = k1_xboole_0
% 3.71/0.97      | sK6 != k1_xboole_0
% 3.71/0.97      | sK5 = k1_xboole_0 ),
% 3.71/0.97      inference(resolution_lifted,[status(thm)],[c_29,c_471]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_1375,plain,( X0 = X0 ),theory(equality) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_1396,plain,
% 3.71/0.97      ( k1_xboole_0 = k1_xboole_0 ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_1375]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_1376,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2086,plain,
% 3.71/0.97      ( sK8 != X0 | sK7 != X0 | sK7 = sK8 ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_1376]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2087,plain,
% 3.71/0.97      ( sK8 != k1_xboole_0 | sK7 = sK8 | sK7 != k1_xboole_0 ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_2086]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2211,plain,
% 3.71/0.97      ( sK8 = sK8 ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_1375]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2268,plain,
% 3.71/0.97      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.71/0.97      | sK7 != sK8 ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_357]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_3441,plain,
% 3.71/0.97      ( sK7 = sK7 ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_1375]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_1383,plain,
% 3.71/0.97      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 3.71/0.97      theory(equality) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2562,plain,
% 3.71/0.97      ( X0 != sK6
% 3.71/0.97      | X1 != sK5
% 3.71/0.97      | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK5,sK6) ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_1383]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_3525,plain,
% 3.71/0.97      ( X0 != sK6
% 3.71/0.97      | k2_zfmisc_1(sK5,X0) = k2_zfmisc_1(sK5,sK6)
% 3.71/0.97      | sK5 != sK5 ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_2562]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_3527,plain,
% 3.71/0.97      ( k2_zfmisc_1(sK5,k1_xboole_0) = k2_zfmisc_1(sK5,sK6)
% 3.71/0.97      | sK5 != sK5
% 3.71/0.97      | k1_xboole_0 != sK6 ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_3525]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_3526,plain,
% 3.71/0.97      ( sK5 = sK5 ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_1375]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_4284,plain,
% 3.71/0.97      ( X0 != X1 | X0 = sK6 | sK6 != X1 ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_1376]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_4285,plain,
% 3.71/0.97      ( sK6 != k1_xboole_0
% 3.71/0.97      | k1_xboole_0 = sK6
% 3.71/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_4284]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_1,plain,
% 3.71/0.97      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.71/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_1853,plain,
% 3.71/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.71/0.97      | v1_xboole_0(X1) != iProver_top ),
% 3.71/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_4787,plain,
% 3.71/0.97      ( sK6 = k1_xboole_0 | v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
% 3.71/0.97      inference(superposition,[status(thm)],[c_4780,c_1853]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_4880,plain,
% 3.71/0.97      ( sK6 = k1_xboole_0 | v1_xboole_0(sK5) != iProver_top ),
% 3.71/0.97      inference(superposition,[status(thm)],[c_3049,c_4787]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2136,plain,
% 3.71/0.97      ( r2_hidden(sK4(sK8,sK7),k1_relat_1(sK8))
% 3.71/0.97      | ~ v1_funct_1(sK8)
% 3.71/0.97      | ~ v1_funct_1(sK7)
% 3.71/0.97      | ~ v1_relat_1(sK8)
% 3.71/0.97      | ~ v1_relat_1(sK7)
% 3.71/0.97      | k1_relat_1(sK8) != k1_relat_1(sK7)
% 3.71/0.97      | sK7 = sK8 ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_12]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2137,plain,
% 3.71/0.97      ( k1_relat_1(sK8) != k1_relat_1(sK7)
% 3.71/0.97      | sK7 = sK8
% 3.71/0.97      | r2_hidden(sK4(sK8,sK7),k1_relat_1(sK8)) = iProver_top
% 3.71/0.97      | v1_funct_1(sK8) != iProver_top
% 3.71/0.97      | v1_funct_1(sK7) != iProver_top
% 3.71/0.97      | v1_relat_1(sK8) != iProver_top
% 3.71/0.97      | v1_relat_1(sK7) != iProver_top ),
% 3.71/0.97      inference(predicate_to_equality,[status(thm)],[c_2136]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_7,plain,
% 3.71/0.97      ( r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X1 = X0 ),
% 3.71/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2412,plain,
% 3.71/0.97      ( r2_hidden(sK2(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(sK8))
% 3.71/0.97      | r2_hidden(sK2(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(sK7))
% 3.71/0.97      | k1_relat_1(sK8) = k1_relat_1(sK7) ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2416,plain,
% 3.71/0.97      ( k1_relat_1(sK8) = k1_relat_1(sK7)
% 3.71/0.97      | r2_hidden(sK2(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(sK8)) = iProver_top
% 3.71/0.97      | r2_hidden(sK2(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(sK7)) = iProver_top ),
% 3.71/0.97      inference(predicate_to_equality,[status(thm)],[c_2412]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2750,plain,
% 3.71/0.97      ( ~ r2_hidden(sK2(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(sK8))
% 3.71/0.97      | ~ v1_xboole_0(k1_relat_1(sK8)) ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2751,plain,
% 3.71/0.97      ( r2_hidden(sK2(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(sK8)) != iProver_top
% 3.71/0.97      | v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
% 3.71/0.97      inference(predicate_to_equality,[status(thm)],[c_2750]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2773,plain,
% 3.71/0.97      ( ~ r2_hidden(sK4(sK8,sK7),k1_relat_1(sK8))
% 3.71/0.97      | ~ v1_xboole_0(k1_relat_1(sK8)) ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2774,plain,
% 3.71/0.97      ( r2_hidden(sK4(sK8,sK7),k1_relat_1(sK8)) != iProver_top
% 3.71/0.97      | v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
% 3.71/0.97      inference(predicate_to_equality,[status(thm)],[c_2773]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_4474,plain,
% 3.71/0.97      ( ~ r2_hidden(sK2(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(sK7))
% 3.71/0.97      | ~ v1_xboole_0(k1_relat_1(sK7)) ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_4475,plain,
% 3.71/0.97      ( r2_hidden(sK2(k1_relat_1(sK7),k1_relat_1(sK8)),k1_relat_1(sK7)) != iProver_top
% 3.71/0.97      | v1_xboole_0(k1_relat_1(sK7)) != iProver_top ),
% 3.71/0.97      inference(predicate_to_equality,[status(thm)],[c_4474]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_0,plain,
% 3.71/0.97      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.71/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_1854,plain,
% 3.71/0.97      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.71/0.97      | v1_xboole_0(X0) = iProver_top ),
% 3.71/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_3950,plain,
% 3.71/0.97      ( r2_hidden(sK0(k1_relat_1(sK8)),sK5) = iProver_top
% 3.71/0.97      | v1_xboole_0(k1_relat_1(sK8)) = iProver_top ),
% 3.71/0.97      inference(superposition,[status(thm)],[c_1854,c_3545]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_4971,plain,
% 3.71/0.97      ( v1_xboole_0(k1_relat_1(sK8)) = iProver_top
% 3.71/0.97      | v1_xboole_0(sK5) != iProver_top ),
% 3.71/0.97      inference(superposition,[status(thm)],[c_3950,c_1853]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2584,plain,
% 3.71/0.97      ( r1_tarski(k1_relat_1(sK7),sK5) = iProver_top ),
% 3.71/0.97      inference(superposition,[status(thm)],[c_1837,c_1834]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_3546,plain,
% 3.71/0.97      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.71/0.97      | r2_hidden(X0,sK5) = iProver_top ),
% 3.71/0.97      inference(superposition,[status(thm)],[c_2584,c_1850]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_4048,plain,
% 3.71/0.97      ( r2_hidden(sK0(k1_relat_1(sK7)),sK5) = iProver_top
% 3.71/0.97      | v1_xboole_0(k1_relat_1(sK7)) = iProver_top ),
% 3.71/0.97      inference(superposition,[status(thm)],[c_1854,c_3546]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_5076,plain,
% 3.71/0.97      ( v1_xboole_0(k1_relat_1(sK7)) = iProver_top
% 3.71/0.97      | v1_xboole_0(sK5) != iProver_top ),
% 3.71/0.97      inference(superposition,[status(thm)],[c_4048,c_1853]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_5245,plain,
% 3.71/0.97      ( v1_xboole_0(sK5) != iProver_top ),
% 3.71/0.97      inference(global_propositional_subsumption,
% 3.71/0.97                [status(thm)],
% 3.71/0.97                [c_4880,c_32,c_34,c_35,c_26,c_37,c_2059,c_2062,c_2137,
% 3.71/0.97                 c_2268,c_2416,c_2751,c_2774,c_4475,c_4971,c_5076]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_5247,plain,
% 3.71/0.97      ( ~ v1_xboole_0(sK5) ),
% 3.71/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_5245]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_1377,plain,
% 3.71/0.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.71/0.97      theory(equality) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_10395,plain,
% 3.71/0.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK5) | sK5 != X0 ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_1377]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_10397,plain,
% 3.71/0.97      ( v1_xboole_0(sK5)
% 3.71/0.97      | ~ v1_xboole_0(k1_xboole_0)
% 3.71/0.97      | sK5 != k1_xboole_0 ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_10395]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_1384,plain,
% 3.71/0.97      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.71/0.97      theory(equality) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2254,plain,
% 3.71/0.97      ( X0 != k2_zfmisc_1(sK5,sK6)
% 3.71/0.97      | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_1384]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2561,plain,
% 3.71/0.97      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK5,sK6)
% 3.71/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_2254]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_15233,plain,
% 3.71/0.97      ( k2_zfmisc_1(sK5,X0) != k2_zfmisc_1(sK5,sK6)
% 3.71/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK5,X0)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_2561]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_15234,plain,
% 3.71/0.97      ( k2_zfmisc_1(sK5,k1_xboole_0) != k2_zfmisc_1(sK5,sK6)
% 3.71/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_15233]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_17267,plain,
% 3.71/0.97      ( r2_hidden(sK4(sK8,sK7),sK5) = iProver_top ),
% 3.71/0.97      inference(global_propositional_subsumption,
% 3.71/0.97                [status(thm)],
% 3.71/0.97                [c_4788,c_26,c_5,c_749,c_783,c_1396,c_2087,c_2211,c_2268,
% 3.71/0.97                 c_3441,c_3527,c_3526,c_4285,c_5247,c_10397,c_15234]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_25,negated_conjecture,
% 3.71/0.97      ( ~ r2_hidden(X0,sK5) | k1_funct_1(sK7,X0) = k1_funct_1(sK8,X0) ),
% 3.71/0.97      inference(cnf_transformation,[],[f82]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_1840,plain,
% 3.71/0.97      ( k1_funct_1(sK7,X0) = k1_funct_1(sK8,X0)
% 3.71/0.97      | r2_hidden(X0,sK5) != iProver_top ),
% 3.71/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_17273,plain,
% 3.71/0.97      ( k1_funct_1(sK8,sK4(sK8,sK7)) = k1_funct_1(sK7,sK4(sK8,sK7)) ),
% 3.71/0.97      inference(superposition,[status(thm)],[c_17267,c_1840]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_11,plain,
% 3.71/0.97      ( ~ v1_funct_1(X0)
% 3.71/0.97      | ~ v1_funct_1(X1)
% 3.71/0.97      | ~ v1_relat_1(X0)
% 3.71/0.97      | ~ v1_relat_1(X1)
% 3.71/0.97      | X0 = X1
% 3.71/0.97      | k1_funct_1(X0,sK4(X1,X0)) != k1_funct_1(X1,sK4(X1,X0))
% 3.71/0.97      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.71/0.97      inference(cnf_transformation,[],[f64]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_1845,plain,
% 3.71/0.97      ( X0 = X1
% 3.71/0.97      | k1_funct_1(X0,sK4(X1,X0)) != k1_funct_1(X1,sK4(X1,X0))
% 3.71/0.97      | k1_relat_1(X1) != k1_relat_1(X0)
% 3.71/0.97      | v1_funct_1(X1) != iProver_top
% 3.71/0.97      | v1_funct_1(X0) != iProver_top
% 3.71/0.97      | v1_relat_1(X0) != iProver_top
% 3.71/0.97      | v1_relat_1(X1) != iProver_top ),
% 3.71/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_17538,plain,
% 3.71/0.97      ( k1_relat_1(sK7) != k1_relat_1(sK8)
% 3.71/0.97      | sK8 = sK7
% 3.71/0.97      | v1_funct_1(sK8) != iProver_top
% 3.71/0.97      | v1_funct_1(sK7) != iProver_top
% 3.71/0.97      | v1_relat_1(sK8) != iProver_top
% 3.71/0.97      | v1_relat_1(sK7) != iProver_top ),
% 3.71/0.97      inference(superposition,[status(thm)],[c_17273,c_1845]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_17890,plain,
% 3.71/0.97      ( k1_relat_1(sK7) != k1_relat_1(sK8) ),
% 3.71/0.97      inference(global_propositional_subsumption,
% 3.71/0.97                [status(thm)],
% 3.71/0.97                [c_17538,c_32,c_34,c_35,c_37,c_597,c_2059,c_2062]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_17893,plain,
% 3.71/0.97      ( k1_relat_1(sK7) != sK5 | sK6 = k1_xboole_0 ),
% 3.71/0.97      inference(superposition,[status(thm)],[c_3049,c_17890]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_17784,plain,
% 3.71/0.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK6) | sK6 != X0 ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_1377]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_17785,plain,
% 3.71/0.97      ( sK6 != X0
% 3.71/0.97      | v1_xboole_0(X0) != iProver_top
% 3.71/0.97      | v1_xboole_0(sK6) = iProver_top ),
% 3.71/0.97      inference(predicate_to_equality,[status(thm)],[c_17784]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_17787,plain,
% 3.71/0.97      ( sK6 != k1_xboole_0
% 3.71/0.97      | v1_xboole_0(sK6) = iProver_top
% 3.71/0.97      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_17785]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2948,plain,
% 3.71/0.97      ( ~ r2_hidden(sK2(sK8,X0),X0) | ~ v1_xboole_0(X0) ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_5018,plain,
% 3.71/0.97      ( ~ r2_hidden(sK2(sK8,sK7),sK7) | ~ v1_xboole_0(sK7) ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_2948]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_5019,plain,
% 3.71/0.97      ( r2_hidden(sK2(sK8,sK7),sK7) != iProver_top
% 3.71/0.97      | v1_xboole_0(sK7) != iProver_top ),
% 3.71/0.97      inference(predicate_to_equality,[status(thm)],[c_5018]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_15,plain,
% 3.71/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.97      | ~ v1_xboole_0(X2)
% 3.71/0.97      | v1_xboole_0(X0) ),
% 3.71/0.97      inference(cnf_transformation,[],[f67]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_1842,plain,
% 3.71/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.71/0.97      | v1_xboole_0(X2) != iProver_top
% 3.71/0.97      | v1_xboole_0(X0) = iProver_top ),
% 3.71/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_3378,plain,
% 3.71/0.97      ( v1_xboole_0(sK7) = iProver_top
% 3.71/0.97      | v1_xboole_0(sK6) != iProver_top ),
% 3.71/0.97      inference(superposition,[status(thm)],[c_1837,c_1842]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_3377,plain,
% 3.71/0.97      ( v1_xboole_0(sK8) = iProver_top
% 3.71/0.97      | v1_xboole_0(sK6) != iProver_top ),
% 3.71/0.97      inference(superposition,[status(thm)],[c_1839,c_1842]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2397,plain,
% 3.71/0.97      ( ~ r2_hidden(sK2(sK8,sK7),sK8) | ~ v1_xboole_0(sK8) ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2398,plain,
% 3.71/0.97      ( r2_hidden(sK2(sK8,sK7),sK8) != iProver_top
% 3.71/0.97      | v1_xboole_0(sK8) != iProver_top ),
% 3.71/0.97      inference(predicate_to_equality,[status(thm)],[c_2397]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2112,plain,
% 3.71/0.97      ( r2_hidden(sK2(sK8,sK7),sK8)
% 3.71/0.97      | r2_hidden(sK2(sK8,sK7),sK7)
% 3.71/0.97      | sK7 = sK8 ),
% 3.71/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_2113,plain,
% 3.71/0.97      ( sK7 = sK8
% 3.71/0.97      | r2_hidden(sK2(sK8,sK7),sK8) = iProver_top
% 3.71/0.97      | r2_hidden(sK2(sK8,sK7),sK7) = iProver_top ),
% 3.71/0.97      inference(predicate_to_equality,[status(thm)],[c_2112]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(c_94,plain,
% 3.71/0.97      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.71/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.71/0.97  
% 3.71/0.97  cnf(contradiction,plain,
% 3.71/0.97      ( $false ),
% 3.71/0.97      inference(minisat,
% 3.71/0.97                [status(thm)],
% 3.71/0.97                [c_17893,c_17787,c_5019,c_3378,c_3377,c_3122,c_2398,
% 3.71/0.97                 c_2268,c_2113,c_94,c_26]) ).
% 3.71/0.97  
% 3.71/0.97  
% 3.71/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/0.97  
% 3.71/0.97  ------                               Statistics
% 3.71/0.97  
% 3.71/0.97  ------ General
% 3.71/0.97  
% 3.71/0.97  abstr_ref_over_cycles:                  0
% 3.71/0.97  abstr_ref_under_cycles:                 0
% 3.71/0.97  gc_basic_clause_elim:                   0
% 3.71/0.97  forced_gc_time:                         0
% 3.71/0.97  parsing_time:                           0.01
% 3.71/0.97  unif_index_cands_time:                  0.
% 3.71/0.97  unif_index_add_time:                    0.
% 3.71/0.97  orderings_time:                         0.
% 3.71/0.97  out_proof_time:                         0.01
% 3.71/0.97  total_time:                             0.467
% 3.71/0.97  num_of_symbols:                         55
% 3.71/0.97  num_of_terms:                           10621
% 3.71/0.97  
% 3.71/0.97  ------ Preprocessing
% 3.71/0.97  
% 3.71/0.97  num_of_splits:                          0
% 3.71/0.97  num_of_split_atoms:                     0
% 3.71/0.97  num_of_reused_defs:                     0
% 3.71/0.97  num_eq_ax_congr_red:                    37
% 3.71/0.97  num_of_sem_filtered_clauses:            1
% 3.71/0.97  num_of_subtypes:                        0
% 3.71/0.97  monotx_restored_types:                  0
% 3.71/0.97  sat_num_of_epr_types:                   0
% 3.71/0.97  sat_num_of_non_cyclic_types:            0
% 3.71/0.97  sat_guarded_non_collapsed_types:        0
% 3.71/0.97  num_pure_diseq_elim:                    0
% 3.71/0.97  simp_replaced_by:                       0
% 3.71/0.97  res_preprocessed:                       136
% 3.71/0.97  prep_upred:                             0
% 3.71/0.97  prep_unflattend:                        89
% 3.71/0.97  smt_new_axioms:                         0
% 3.71/0.97  pred_elim_cands:                        6
% 3.71/0.97  pred_elim:                              3
% 3.71/0.97  pred_elim_cl:                           5
% 3.71/0.97  pred_elim_cycles:                       7
% 3.71/0.97  merged_defs:                            0
% 3.71/0.97  merged_defs_ncl:                        0
% 3.71/0.97  bin_hyper_res:                          0
% 3.71/0.97  prep_cycles:                            4
% 3.71/0.97  pred_elim_time:                         0.015
% 3.71/0.97  splitting_time:                         0.
% 3.71/0.97  sem_filter_time:                        0.
% 3.71/0.97  monotx_time:                            0.001
% 3.71/0.97  subtype_inf_time:                       0.
% 3.71/0.97  
% 3.71/0.97  ------ Problem properties
% 3.71/0.97  
% 3.71/0.97  clauses:                                27
% 3.71/0.97  conjectures:                            5
% 3.71/0.97  epr:                                    5
% 3.71/0.97  horn:                                   19
% 3.71/0.97  ground:                                 11
% 3.71/0.97  unary:                                  6
% 3.71/0.97  binary:                                 11
% 3.71/0.97  lits:                                   68
% 3.71/0.97  lits_eq:                                24
% 3.71/0.97  fd_pure:                                0
% 3.71/0.97  fd_pseudo:                              0
% 3.71/0.97  fd_cond:                                0
% 3.71/0.97  fd_pseudo_cond:                         4
% 3.71/0.97  ac_symbols:                             0
% 3.71/0.97  
% 3.71/0.97  ------ Propositional Solver
% 3.71/0.97  
% 3.71/0.97  prop_solver_calls:                      32
% 3.71/0.97  prop_fast_solver_calls:                 1462
% 3.71/0.97  smt_solver_calls:                       0
% 3.71/0.97  smt_fast_solver_calls:                  0
% 3.71/0.97  prop_num_of_clauses:                    5425
% 3.71/0.97  prop_preprocess_simplified:             8442
% 3.71/0.97  prop_fo_subsumed:                       52
% 3.71/0.97  prop_solver_time:                       0.
% 3.71/0.97  smt_solver_time:                        0.
% 3.71/0.97  smt_fast_solver_time:                   0.
% 3.71/0.97  prop_fast_solver_time:                  0.
% 3.71/0.97  prop_unsat_core_time:                   0.
% 3.71/0.97  
% 3.71/0.97  ------ QBF
% 3.71/0.97  
% 3.71/0.97  qbf_q_res:                              0
% 3.71/0.97  qbf_num_tautologies:                    0
% 3.71/0.97  qbf_prep_cycles:                        0
% 3.71/0.97  
% 3.71/0.97  ------ BMC1
% 3.71/0.97  
% 3.71/0.97  bmc1_current_bound:                     -1
% 3.71/0.97  bmc1_last_solved_bound:                 -1
% 3.71/0.97  bmc1_unsat_core_size:                   -1
% 3.71/0.97  bmc1_unsat_core_parents_size:           -1
% 3.71/0.97  bmc1_merge_next_fun:                    0
% 3.71/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.71/0.97  
% 3.71/0.97  ------ Instantiation
% 3.71/0.97  
% 3.71/0.97  inst_num_of_clauses:                    1294
% 3.71/0.97  inst_num_in_passive:                    645
% 3.71/0.97  inst_num_in_active:                     649
% 3.71/0.97  inst_num_in_unprocessed:                0
% 3.71/0.97  inst_num_of_loops:                      930
% 3.71/0.97  inst_num_of_learning_restarts:          0
% 3.71/0.97  inst_num_moves_active_passive:          275
% 3.71/0.97  inst_lit_activity:                      0
% 3.71/0.97  inst_lit_activity_moves:                0
% 3.71/0.97  inst_num_tautologies:                   0
% 3.71/0.97  inst_num_prop_implied:                  0
% 3.71/0.97  inst_num_existing_simplified:           0
% 3.71/0.97  inst_num_eq_res_simplified:             0
% 3.71/0.97  inst_num_child_elim:                    0
% 3.71/0.97  inst_num_of_dismatching_blockings:      762
% 3.71/0.97  inst_num_of_non_proper_insts:           1828
% 3.71/0.97  inst_num_of_duplicates:                 0
% 3.71/0.97  inst_inst_num_from_inst_to_res:         0
% 3.71/0.97  inst_dismatching_checking_time:         0.
% 3.71/0.97  
% 3.71/0.97  ------ Resolution
% 3.71/0.97  
% 3.71/0.97  res_num_of_clauses:                     0
% 3.71/0.97  res_num_in_passive:                     0
% 3.71/0.97  res_num_in_active:                      0
% 3.71/0.97  res_num_of_loops:                       140
% 3.71/0.97  res_forward_subset_subsumed:            270
% 3.71/0.97  res_backward_subset_subsumed:           0
% 3.71/0.97  res_forward_subsumed:                   0
% 3.71/0.97  res_backward_subsumed:                  0
% 3.71/0.97  res_forward_subsumption_resolution:     0
% 3.71/0.97  res_backward_subsumption_resolution:    0
% 3.71/0.97  res_clause_to_clause_subsumption:       2267
% 3.71/0.97  res_orphan_elimination:                 0
% 3.71/0.97  res_tautology_del:                      110
% 3.71/0.97  res_num_eq_res_simplified:              0
% 3.71/0.97  res_num_sel_changes:                    0
% 3.71/0.97  res_moves_from_active_to_pass:          0
% 3.71/0.97  
% 3.71/0.97  ------ Superposition
% 3.71/0.97  
% 3.71/0.97  sup_time_total:                         0.
% 3.71/0.97  sup_time_generating:                    0.
% 3.71/0.97  sup_time_sim_full:                      0.
% 3.71/0.97  sup_time_sim_immed:                     0.
% 3.71/0.97  
% 3.71/0.97  sup_num_of_clauses:                     519
% 3.71/0.97  sup_num_in_active:                      170
% 3.71/0.97  sup_num_in_passive:                     349
% 3.71/0.97  sup_num_of_loops:                       185
% 3.71/0.97  sup_fw_superposition:                   377
% 3.71/0.97  sup_bw_superposition:                   692
% 3.71/0.97  sup_immediate_simplified:               226
% 3.71/0.97  sup_given_eliminated:                   0
% 3.71/0.97  comparisons_done:                       0
% 3.71/0.97  comparisons_avoided:                    192
% 3.71/0.97  
% 3.71/0.97  ------ Simplifications
% 3.71/0.97  
% 3.71/0.97  
% 3.71/0.97  sim_fw_subset_subsumed:                 155
% 3.71/0.97  sim_bw_subset_subsumed:                 31
% 3.71/0.97  sim_fw_subsumed:                        52
% 3.71/0.97  sim_bw_subsumed:                        12
% 3.71/0.97  sim_fw_subsumption_res:                 4
% 3.71/0.97  sim_bw_subsumption_res:                 0
% 3.71/0.97  sim_tautology_del:                      17
% 3.71/0.97  sim_eq_tautology_del:                   154
% 3.71/0.97  sim_eq_res_simp:                        10
% 3.71/0.97  sim_fw_demodulated:                     0
% 3.71/0.97  sim_bw_demodulated:                     2
% 3.71/0.97  sim_light_normalised:                   8
% 3.71/0.97  sim_joinable_taut:                      0
% 3.71/0.97  sim_joinable_simp:                      0
% 3.71/0.97  sim_ac_normalised:                      0
% 3.71/0.97  sim_smt_subsumption:                    0
% 3.71/0.97  
%------------------------------------------------------------------------------
