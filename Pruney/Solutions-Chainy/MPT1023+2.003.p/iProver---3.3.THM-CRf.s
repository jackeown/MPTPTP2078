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
% DateTime   : Thu Dec  3 12:07:41 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  163 (1803 expanded)
%              Number of clauses        :   97 ( 575 expanded)
%              Number of leaves         :   20 ( 438 expanded)
%              Depth                    :   27
%              Number of atoms          :  531 (10750 expanded)
%              Number of equality atoms :  234 (2328 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f36])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f39,f48,f47])).

fof(f78,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f44])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4)
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_495,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_496,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_498,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_496,c_26])).

cnf(c_1130,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1132,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2792,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1130,c_1132])).

cnf(c_3206,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_498,c_2792])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_506,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_507,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_509,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_507,c_29])).

cnf(c_1128,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2793,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1128,c_1132])).

cnf(c_3237,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_509,c_2793])).

cnf(c_12,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1135,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3618,plain,
    ( k1_relat_1(X0) != sK2
    | sK4 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3237,c_1135])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_32,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1364,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1365,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1364])).

cnf(c_3974,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != sK2
    | sK4 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3618,c_32,c_34,c_1365])).

cnf(c_3975,plain,
    ( k1_relat_1(X0) != sK2
    | sK4 = X0
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3974])).

cnf(c_3986,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3206,c_3975])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_35,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1334,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ v1_xboole_0(sK4)
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1361,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1362,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1361])).

cnf(c_728,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1590,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_728])).

cnf(c_1592,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1590])).

cnf(c_1504,plain,
    ( r2_hidden(sK1(X0,sK4),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | X0 = sK4
    | k1_relat_1(sK4) != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1767,plain,
    ( r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4 ),
    inference(instantiation,[status(thm)],[c_1504])).

cnf(c_1768,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1767])).

cnf(c_733,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_1990,plain,
    ( k1_relat_1(sK4) = k1_relat_1(sK5)
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1133,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3332,plain,
    ( v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_1133])).

cnf(c_3369,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3332])).

cnf(c_3333,plain,
    ( v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1128,c_1133])).

cnf(c_3370,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3333])).

cnf(c_4661,plain,
    ( sK5 = sK4
    | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3986,c_32,c_34,c_35,c_37,c_0,c_1334,c_1362,c_1365,c_1592,c_1768,c_1990,c_3369,c_3370])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_14,c_9])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_363,c_14,c_13,c_9])).

cnf(c_1124,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_1547,plain,
    ( k7_relat_1(sK5,sK2) = sK5 ),
    inference(superposition,[status(thm)],[c_1130,c_1124])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_10,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_327,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X2)
    | X3 != X1
    | k1_relat_1(k7_relat_1(X2,X3)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_10])).

cnf(c_328,plain,
    ( m1_subset_1(k1_relat_1(k7_relat_1(X0,X1)),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_1126,plain,
    ( m1_subset_1(k1_relat_1(k7_relat_1(X0,X1)),k1_zfmisc_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_2167,plain,
    ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_1126])).

cnf(c_2320,plain,
    ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2167,c_37,c_1362])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1137,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3461,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | m1_subset_1(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2320,c_1137])).

cnf(c_4827,plain,
    ( sK5 = sK4
    | m1_subset_1(sK1(sK5,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4661,c_3461])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1131,plain,
    ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5709,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = k1_funct_1(sK4,sK1(sK5,sK4))
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_4827,c_1131])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1136,plain,
    ( X0 = X1
    | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5712,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5709,c_1136])).

cnf(c_5713,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5712])).

cnf(c_5754,plain,
    ( k1_relat_1(sK4) != k1_relat_1(sK5)
    | sK5 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5712,c_31,c_29,c_28,c_26,c_1361,c_1364,c_5713])).

cnf(c_5758,plain,
    ( k1_relat_1(sK4) != sK2
    | sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3206,c_5754])).

cnf(c_17,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_342,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != X0
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_26])).

cnf(c_5591,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_5759,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5758,c_26,c_0,c_1334,c_1592,c_3237,c_3369,c_3370,c_5591])).

cnf(c_5761,plain,
    ( sK5 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5759,c_26,c_0,c_1334,c_1592,c_3237,c_3369,c_3370,c_5591,c_5758])).

cnf(c_1125,plain,
    ( sK4 != sK5
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_5782,plain,
    ( sK4 != sK4
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5761,c_1125])).

cnf(c_5790,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5782])).

cnf(c_5794,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5790])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1354,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5614,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_5617,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5614])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5794,c_5617])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:50:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.97/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/0.98  
% 2.97/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/0.98  
% 2.97/0.98  ------  iProver source info
% 2.97/0.98  
% 2.97/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.97/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/0.98  git: non_committed_changes: false
% 2.97/0.98  git: last_make_outside_of_git: false
% 2.97/0.98  
% 2.97/0.98  ------ 
% 2.97/0.98  
% 2.97/0.98  ------ Input Options
% 2.97/0.98  
% 2.97/0.98  --out_options                           all
% 2.97/0.98  --tptp_safe_out                         true
% 2.97/0.98  --problem_path                          ""
% 2.97/0.98  --include_path                          ""
% 2.97/0.98  --clausifier                            res/vclausify_rel
% 2.97/0.98  --clausifier_options                    --mode clausify
% 2.97/0.98  --stdin                                 false
% 2.97/0.98  --stats_out                             all
% 2.97/0.98  
% 2.97/0.98  ------ General Options
% 2.97/0.98  
% 2.97/0.98  --fof                                   false
% 2.97/0.98  --time_out_real                         305.
% 2.97/0.98  --time_out_virtual                      -1.
% 2.97/0.98  --symbol_type_check                     false
% 2.97/0.98  --clausify_out                          false
% 2.97/0.98  --sig_cnt_out                           false
% 2.97/0.98  --trig_cnt_out                          false
% 2.97/0.98  --trig_cnt_out_tolerance                1.
% 2.97/0.98  --trig_cnt_out_sk_spl                   false
% 2.97/0.98  --abstr_cl_out                          false
% 2.97/0.98  
% 2.97/0.98  ------ Global Options
% 2.97/0.98  
% 2.97/0.98  --schedule                              default
% 2.97/0.98  --add_important_lit                     false
% 2.97/0.98  --prop_solver_per_cl                    1000
% 2.97/0.98  --min_unsat_core                        false
% 2.97/0.98  --soft_assumptions                      false
% 2.97/0.98  --soft_lemma_size                       3
% 2.97/0.98  --prop_impl_unit_size                   0
% 2.97/0.98  --prop_impl_unit                        []
% 2.97/0.98  --share_sel_clauses                     true
% 2.97/0.98  --reset_solvers                         false
% 2.97/0.98  --bc_imp_inh                            [conj_cone]
% 2.97/0.98  --conj_cone_tolerance                   3.
% 2.97/0.98  --extra_neg_conj                        none
% 2.97/0.98  --large_theory_mode                     true
% 2.97/0.98  --prolific_symb_bound                   200
% 2.97/0.98  --lt_threshold                          2000
% 2.97/0.98  --clause_weak_htbl                      true
% 2.97/0.98  --gc_record_bc_elim                     false
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing Options
% 2.97/0.98  
% 2.97/0.98  --preprocessing_flag                    true
% 2.97/0.98  --time_out_prep_mult                    0.1
% 2.97/0.98  --splitting_mode                        input
% 2.97/0.98  --splitting_grd                         true
% 2.97/0.98  --splitting_cvd                         false
% 2.97/0.98  --splitting_cvd_svl                     false
% 2.97/0.98  --splitting_nvd                         32
% 2.97/0.98  --sub_typing                            true
% 2.97/0.98  --prep_gs_sim                           true
% 2.97/0.98  --prep_unflatten                        true
% 2.97/0.98  --prep_res_sim                          true
% 2.97/0.98  --prep_upred                            true
% 2.97/0.98  --prep_sem_filter                       exhaustive
% 2.97/0.98  --prep_sem_filter_out                   false
% 2.97/0.98  --pred_elim                             true
% 2.97/0.98  --res_sim_input                         true
% 2.97/0.98  --eq_ax_congr_red                       true
% 2.97/0.98  --pure_diseq_elim                       true
% 2.97/0.98  --brand_transform                       false
% 2.97/0.98  --non_eq_to_eq                          false
% 2.97/0.98  --prep_def_merge                        true
% 2.97/0.98  --prep_def_merge_prop_impl              false
% 2.97/0.98  --prep_def_merge_mbd                    true
% 2.97/0.98  --prep_def_merge_tr_red                 false
% 2.97/0.98  --prep_def_merge_tr_cl                  false
% 2.97/0.98  --smt_preprocessing                     true
% 2.97/0.98  --smt_ac_axioms                         fast
% 2.97/0.98  --preprocessed_out                      false
% 2.97/0.98  --preprocessed_stats                    false
% 2.97/0.98  
% 2.97/0.98  ------ Abstraction refinement Options
% 2.97/0.98  
% 2.97/0.98  --abstr_ref                             []
% 2.97/0.98  --abstr_ref_prep                        false
% 2.97/0.98  --abstr_ref_until_sat                   false
% 2.97/0.98  --abstr_ref_sig_restrict                funpre
% 2.97/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.98  --abstr_ref_under                       []
% 2.97/0.98  
% 2.97/0.98  ------ SAT Options
% 2.97/0.98  
% 2.97/0.98  --sat_mode                              false
% 2.97/0.98  --sat_fm_restart_options                ""
% 2.97/0.98  --sat_gr_def                            false
% 2.97/0.98  --sat_epr_types                         true
% 2.97/0.98  --sat_non_cyclic_types                  false
% 2.97/0.98  --sat_finite_models                     false
% 2.97/0.98  --sat_fm_lemmas                         false
% 2.97/0.98  --sat_fm_prep                           false
% 2.97/0.98  --sat_fm_uc_incr                        true
% 2.97/0.98  --sat_out_model                         small
% 2.97/0.98  --sat_out_clauses                       false
% 2.97/0.98  
% 2.97/0.98  ------ QBF Options
% 2.97/0.98  
% 2.97/0.98  --qbf_mode                              false
% 2.97/0.98  --qbf_elim_univ                         false
% 2.97/0.98  --qbf_dom_inst                          none
% 2.97/0.98  --qbf_dom_pre_inst                      false
% 2.97/0.98  --qbf_sk_in                             false
% 2.97/0.98  --qbf_pred_elim                         true
% 2.97/0.98  --qbf_split                             512
% 2.97/0.98  
% 2.97/0.98  ------ BMC1 Options
% 2.97/0.98  
% 2.97/0.98  --bmc1_incremental                      false
% 2.97/0.98  --bmc1_axioms                           reachable_all
% 2.97/0.98  --bmc1_min_bound                        0
% 2.97/0.98  --bmc1_max_bound                        -1
% 2.97/0.98  --bmc1_max_bound_default                -1
% 2.97/0.98  --bmc1_symbol_reachability              true
% 2.97/0.98  --bmc1_property_lemmas                  false
% 2.97/0.98  --bmc1_k_induction                      false
% 2.97/0.98  --bmc1_non_equiv_states                 false
% 2.97/0.98  --bmc1_deadlock                         false
% 2.97/0.98  --bmc1_ucm                              false
% 2.97/0.98  --bmc1_add_unsat_core                   none
% 2.97/0.98  --bmc1_unsat_core_children              false
% 2.97/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.98  --bmc1_out_stat                         full
% 2.97/0.98  --bmc1_ground_init                      false
% 2.97/0.98  --bmc1_pre_inst_next_state              false
% 2.97/0.98  --bmc1_pre_inst_state                   false
% 2.97/0.98  --bmc1_pre_inst_reach_state             false
% 2.97/0.98  --bmc1_out_unsat_core                   false
% 2.97/0.98  --bmc1_aig_witness_out                  false
% 2.97/0.98  --bmc1_verbose                          false
% 2.97/0.98  --bmc1_dump_clauses_tptp                false
% 2.97/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.98  --bmc1_dump_file                        -
% 2.97/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.98  --bmc1_ucm_extend_mode                  1
% 2.97/0.98  --bmc1_ucm_init_mode                    2
% 2.97/0.98  --bmc1_ucm_cone_mode                    none
% 2.97/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.98  --bmc1_ucm_relax_model                  4
% 2.97/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.98  --bmc1_ucm_layered_model                none
% 2.97/0.98  --bmc1_ucm_max_lemma_size               10
% 2.97/0.98  
% 2.97/0.98  ------ AIG Options
% 2.97/0.98  
% 2.97/0.98  --aig_mode                              false
% 2.97/0.98  
% 2.97/0.98  ------ Instantiation Options
% 2.97/0.98  
% 2.97/0.98  --instantiation_flag                    true
% 2.97/0.98  --inst_sos_flag                         false
% 2.97/0.98  --inst_sos_phase                        true
% 2.97/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.98  --inst_lit_sel_side                     num_symb
% 2.97/0.98  --inst_solver_per_active                1400
% 2.97/0.98  --inst_solver_calls_frac                1.
% 2.97/0.98  --inst_passive_queue_type               priority_queues
% 2.97/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.98  --inst_passive_queues_freq              [25;2]
% 2.97/0.98  --inst_dismatching                      true
% 2.97/0.98  --inst_eager_unprocessed_to_passive     true
% 2.97/0.98  --inst_prop_sim_given                   true
% 2.97/0.98  --inst_prop_sim_new                     false
% 2.97/0.98  --inst_subs_new                         false
% 2.97/0.98  --inst_eq_res_simp                      false
% 2.97/0.98  --inst_subs_given                       false
% 2.97/0.98  --inst_orphan_elimination               true
% 2.97/0.98  --inst_learning_loop_flag               true
% 2.97/0.98  --inst_learning_start                   3000
% 2.97/0.98  --inst_learning_factor                  2
% 2.97/0.98  --inst_start_prop_sim_after_learn       3
% 2.97/0.98  --inst_sel_renew                        solver
% 2.97/0.98  --inst_lit_activity_flag                true
% 2.97/0.98  --inst_restr_to_given                   false
% 2.97/0.98  --inst_activity_threshold               500
% 2.97/0.98  --inst_out_proof                        true
% 2.97/0.98  
% 2.97/0.98  ------ Resolution Options
% 2.97/0.98  
% 2.97/0.98  --resolution_flag                       true
% 2.97/0.98  --res_lit_sel                           adaptive
% 2.97/0.98  --res_lit_sel_side                      none
% 2.97/0.98  --res_ordering                          kbo
% 2.97/0.98  --res_to_prop_solver                    active
% 2.97/0.98  --res_prop_simpl_new                    false
% 2.97/0.98  --res_prop_simpl_given                  true
% 2.97/0.98  --res_passive_queue_type                priority_queues
% 2.97/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.98  --res_passive_queues_freq               [15;5]
% 2.97/0.98  --res_forward_subs                      full
% 2.97/0.98  --res_backward_subs                     full
% 2.97/0.98  --res_forward_subs_resolution           true
% 2.97/0.98  --res_backward_subs_resolution          true
% 2.97/0.98  --res_orphan_elimination                true
% 2.97/0.98  --res_time_limit                        2.
% 2.97/0.98  --res_out_proof                         true
% 2.97/0.98  
% 2.97/0.98  ------ Superposition Options
% 2.97/0.98  
% 2.97/0.98  --superposition_flag                    true
% 2.97/0.98  --sup_passive_queue_type                priority_queues
% 2.97/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.98  --demod_completeness_check              fast
% 2.97/0.98  --demod_use_ground                      true
% 2.97/0.98  --sup_to_prop_solver                    passive
% 2.97/0.98  --sup_prop_simpl_new                    true
% 2.97/0.98  --sup_prop_simpl_given                  true
% 2.97/0.98  --sup_fun_splitting                     false
% 2.97/0.98  --sup_smt_interval                      50000
% 2.97/0.98  
% 2.97/0.98  ------ Superposition Simplification Setup
% 2.97/0.98  
% 2.97/0.98  --sup_indices_passive                   []
% 2.97/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_full_bw                           [BwDemod]
% 2.97/0.98  --sup_immed_triv                        [TrivRules]
% 2.97/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_immed_bw_main                     []
% 2.97/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.98  
% 2.97/0.98  ------ Combination Options
% 2.97/0.98  
% 2.97/0.98  --comb_res_mult                         3
% 2.97/0.98  --comb_sup_mult                         2
% 2.97/0.98  --comb_inst_mult                        10
% 2.97/0.98  
% 2.97/0.98  ------ Debug Options
% 2.97/0.98  
% 2.97/0.98  --dbg_backtrace                         false
% 2.97/0.98  --dbg_dump_prop_clauses                 false
% 2.97/0.98  --dbg_dump_prop_clauses_file            -
% 2.97/0.98  --dbg_out_stat                          false
% 2.97/0.98  ------ Parsing...
% 2.97/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/0.98  ------ Proving...
% 2.97/0.98  ------ Problem Properties 
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  clauses                                 27
% 2.97/0.98  conjectures                             5
% 2.97/0.98  EPR                                     4
% 2.97/0.98  Horn                                    21
% 2.97/0.98  unary                                   9
% 2.97/0.98  binary                                  8
% 2.97/0.98  lits                                    65
% 2.97/0.98  lits eq                                 29
% 2.97/0.98  fd_pure                                 0
% 2.97/0.98  fd_pseudo                               0
% 2.97/0.98  fd_cond                                 1
% 2.97/0.98  fd_pseudo_cond                          3
% 2.97/0.98  AC symbols                              0
% 2.97/0.98  
% 2.97/0.98  ------ Schedule dynamic 5 is on 
% 2.97/0.98  
% 2.97/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  ------ 
% 2.97/0.98  Current options:
% 2.97/0.98  ------ 
% 2.97/0.98  
% 2.97/0.98  ------ Input Options
% 2.97/0.98  
% 2.97/0.98  --out_options                           all
% 2.97/0.98  --tptp_safe_out                         true
% 2.97/0.98  --problem_path                          ""
% 2.97/0.98  --include_path                          ""
% 2.97/0.98  --clausifier                            res/vclausify_rel
% 2.97/0.98  --clausifier_options                    --mode clausify
% 2.97/0.98  --stdin                                 false
% 2.97/0.98  --stats_out                             all
% 2.97/0.98  
% 2.97/0.98  ------ General Options
% 2.97/0.98  
% 2.97/0.98  --fof                                   false
% 2.97/0.98  --time_out_real                         305.
% 2.97/0.98  --time_out_virtual                      -1.
% 2.97/0.98  --symbol_type_check                     false
% 2.97/0.98  --clausify_out                          false
% 2.97/0.98  --sig_cnt_out                           false
% 2.97/0.98  --trig_cnt_out                          false
% 2.97/0.98  --trig_cnt_out_tolerance                1.
% 2.97/0.98  --trig_cnt_out_sk_spl                   false
% 2.97/0.98  --abstr_cl_out                          false
% 2.97/0.98  
% 2.97/0.98  ------ Global Options
% 2.97/0.98  
% 2.97/0.98  --schedule                              default
% 2.97/0.98  --add_important_lit                     false
% 2.97/0.98  --prop_solver_per_cl                    1000
% 2.97/0.98  --min_unsat_core                        false
% 2.97/0.98  --soft_assumptions                      false
% 2.97/0.98  --soft_lemma_size                       3
% 2.97/0.98  --prop_impl_unit_size                   0
% 2.97/0.98  --prop_impl_unit                        []
% 2.97/0.98  --share_sel_clauses                     true
% 2.97/0.98  --reset_solvers                         false
% 2.97/0.98  --bc_imp_inh                            [conj_cone]
% 2.97/0.98  --conj_cone_tolerance                   3.
% 2.97/0.98  --extra_neg_conj                        none
% 2.97/0.98  --large_theory_mode                     true
% 2.97/0.98  --prolific_symb_bound                   200
% 2.97/0.98  --lt_threshold                          2000
% 2.97/0.98  --clause_weak_htbl                      true
% 2.97/0.98  --gc_record_bc_elim                     false
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing Options
% 2.97/0.98  
% 2.97/0.98  --preprocessing_flag                    true
% 2.97/0.98  --time_out_prep_mult                    0.1
% 2.97/0.98  --splitting_mode                        input
% 2.97/0.98  --splitting_grd                         true
% 2.97/0.98  --splitting_cvd                         false
% 2.97/0.98  --splitting_cvd_svl                     false
% 2.97/0.98  --splitting_nvd                         32
% 2.97/0.98  --sub_typing                            true
% 2.97/0.98  --prep_gs_sim                           true
% 2.97/0.98  --prep_unflatten                        true
% 2.97/0.98  --prep_res_sim                          true
% 2.97/0.98  --prep_upred                            true
% 2.97/0.98  --prep_sem_filter                       exhaustive
% 2.97/0.98  --prep_sem_filter_out                   false
% 2.97/0.98  --pred_elim                             true
% 2.97/0.98  --res_sim_input                         true
% 2.97/0.98  --eq_ax_congr_red                       true
% 2.97/0.98  --pure_diseq_elim                       true
% 2.97/0.98  --brand_transform                       false
% 2.97/0.98  --non_eq_to_eq                          false
% 2.97/0.98  --prep_def_merge                        true
% 2.97/0.98  --prep_def_merge_prop_impl              false
% 2.97/0.98  --prep_def_merge_mbd                    true
% 2.97/0.98  --prep_def_merge_tr_red                 false
% 2.97/0.98  --prep_def_merge_tr_cl                  false
% 2.97/0.98  --smt_preprocessing                     true
% 2.97/0.98  --smt_ac_axioms                         fast
% 2.97/0.98  --preprocessed_out                      false
% 2.97/0.98  --preprocessed_stats                    false
% 2.97/0.98  
% 2.97/0.98  ------ Abstraction refinement Options
% 2.97/0.98  
% 2.97/0.98  --abstr_ref                             []
% 2.97/0.98  --abstr_ref_prep                        false
% 2.97/0.98  --abstr_ref_until_sat                   false
% 2.97/0.98  --abstr_ref_sig_restrict                funpre
% 2.97/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.98  --abstr_ref_under                       []
% 2.97/0.98  
% 2.97/0.98  ------ SAT Options
% 2.97/0.98  
% 2.97/0.98  --sat_mode                              false
% 2.97/0.98  --sat_fm_restart_options                ""
% 2.97/0.98  --sat_gr_def                            false
% 2.97/0.98  --sat_epr_types                         true
% 2.97/0.98  --sat_non_cyclic_types                  false
% 2.97/0.98  --sat_finite_models                     false
% 2.97/0.98  --sat_fm_lemmas                         false
% 2.97/0.98  --sat_fm_prep                           false
% 2.97/0.98  --sat_fm_uc_incr                        true
% 2.97/0.98  --sat_out_model                         small
% 2.97/0.98  --sat_out_clauses                       false
% 2.97/0.98  
% 2.97/0.98  ------ QBF Options
% 2.97/0.98  
% 2.97/0.98  --qbf_mode                              false
% 2.97/0.98  --qbf_elim_univ                         false
% 2.97/0.98  --qbf_dom_inst                          none
% 2.97/0.98  --qbf_dom_pre_inst                      false
% 2.97/0.98  --qbf_sk_in                             false
% 2.97/0.98  --qbf_pred_elim                         true
% 2.97/0.98  --qbf_split                             512
% 2.97/0.98  
% 2.97/0.98  ------ BMC1 Options
% 2.97/0.98  
% 2.97/0.98  --bmc1_incremental                      false
% 2.97/0.98  --bmc1_axioms                           reachable_all
% 2.97/0.98  --bmc1_min_bound                        0
% 2.97/0.98  --bmc1_max_bound                        -1
% 2.97/0.98  --bmc1_max_bound_default                -1
% 2.97/0.98  --bmc1_symbol_reachability              true
% 2.97/0.98  --bmc1_property_lemmas                  false
% 2.97/0.98  --bmc1_k_induction                      false
% 2.97/0.98  --bmc1_non_equiv_states                 false
% 2.97/0.98  --bmc1_deadlock                         false
% 2.97/0.98  --bmc1_ucm                              false
% 2.97/0.98  --bmc1_add_unsat_core                   none
% 2.97/0.98  --bmc1_unsat_core_children              false
% 2.97/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.98  --bmc1_out_stat                         full
% 2.97/0.98  --bmc1_ground_init                      false
% 2.97/0.98  --bmc1_pre_inst_next_state              false
% 2.97/0.98  --bmc1_pre_inst_state                   false
% 2.97/0.98  --bmc1_pre_inst_reach_state             false
% 2.97/0.98  --bmc1_out_unsat_core                   false
% 2.97/0.98  --bmc1_aig_witness_out                  false
% 2.97/0.98  --bmc1_verbose                          false
% 2.97/0.98  --bmc1_dump_clauses_tptp                false
% 2.97/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.98  --bmc1_dump_file                        -
% 2.97/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.98  --bmc1_ucm_extend_mode                  1
% 2.97/0.98  --bmc1_ucm_init_mode                    2
% 2.97/0.98  --bmc1_ucm_cone_mode                    none
% 2.97/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.98  --bmc1_ucm_relax_model                  4
% 2.97/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.98  --bmc1_ucm_layered_model                none
% 2.97/0.98  --bmc1_ucm_max_lemma_size               10
% 2.97/0.98  
% 2.97/0.98  ------ AIG Options
% 2.97/0.98  
% 2.97/0.98  --aig_mode                              false
% 2.97/0.98  
% 2.97/0.98  ------ Instantiation Options
% 2.97/0.98  
% 2.97/0.98  --instantiation_flag                    true
% 2.97/0.98  --inst_sos_flag                         false
% 2.97/0.98  --inst_sos_phase                        true
% 2.97/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.98  --inst_lit_sel_side                     none
% 2.97/0.98  --inst_solver_per_active                1400
% 2.97/0.98  --inst_solver_calls_frac                1.
% 2.97/0.98  --inst_passive_queue_type               priority_queues
% 2.97/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.98  --inst_passive_queues_freq              [25;2]
% 2.97/0.98  --inst_dismatching                      true
% 2.97/0.98  --inst_eager_unprocessed_to_passive     true
% 2.97/0.98  --inst_prop_sim_given                   true
% 2.97/0.98  --inst_prop_sim_new                     false
% 2.97/0.98  --inst_subs_new                         false
% 2.97/0.98  --inst_eq_res_simp                      false
% 2.97/0.98  --inst_subs_given                       false
% 2.97/0.98  --inst_orphan_elimination               true
% 2.97/0.98  --inst_learning_loop_flag               true
% 2.97/0.98  --inst_learning_start                   3000
% 2.97/0.98  --inst_learning_factor                  2
% 2.97/0.98  --inst_start_prop_sim_after_learn       3
% 2.97/0.98  --inst_sel_renew                        solver
% 2.97/0.98  --inst_lit_activity_flag                true
% 2.97/0.98  --inst_restr_to_given                   false
% 2.97/0.98  --inst_activity_threshold               500
% 2.97/0.98  --inst_out_proof                        true
% 2.97/0.98  
% 2.97/0.98  ------ Resolution Options
% 2.97/0.98  
% 2.97/0.98  --resolution_flag                       false
% 2.97/0.98  --res_lit_sel                           adaptive
% 2.97/0.98  --res_lit_sel_side                      none
% 2.97/0.98  --res_ordering                          kbo
% 2.97/0.98  --res_to_prop_solver                    active
% 2.97/0.98  --res_prop_simpl_new                    false
% 2.97/0.98  --res_prop_simpl_given                  true
% 2.97/0.98  --res_passive_queue_type                priority_queues
% 2.97/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.98  --res_passive_queues_freq               [15;5]
% 2.97/0.98  --res_forward_subs                      full
% 2.97/0.98  --res_backward_subs                     full
% 2.97/0.98  --res_forward_subs_resolution           true
% 2.97/0.98  --res_backward_subs_resolution          true
% 2.97/0.98  --res_orphan_elimination                true
% 2.97/0.98  --res_time_limit                        2.
% 2.97/0.98  --res_out_proof                         true
% 2.97/0.98  
% 2.97/0.98  ------ Superposition Options
% 2.97/0.98  
% 2.97/0.98  --superposition_flag                    true
% 2.97/0.98  --sup_passive_queue_type                priority_queues
% 2.97/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.98  --demod_completeness_check              fast
% 2.97/0.98  --demod_use_ground                      true
% 2.97/0.98  --sup_to_prop_solver                    passive
% 2.97/0.98  --sup_prop_simpl_new                    true
% 2.97/0.98  --sup_prop_simpl_given                  true
% 2.97/0.98  --sup_fun_splitting                     false
% 2.97/0.98  --sup_smt_interval                      50000
% 2.97/0.98  
% 2.97/0.98  ------ Superposition Simplification Setup
% 2.97/0.98  
% 2.97/0.98  --sup_indices_passive                   []
% 2.97/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_full_bw                           [BwDemod]
% 2.97/0.98  --sup_immed_triv                        [TrivRules]
% 2.97/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_immed_bw_main                     []
% 2.97/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.98  
% 2.97/0.98  ------ Combination Options
% 2.97/0.98  
% 2.97/0.98  --comb_res_mult                         3
% 2.97/0.98  --comb_sup_mult                         2
% 2.97/0.98  --comb_inst_mult                        10
% 2.97/0.98  
% 2.97/0.98  ------ Debug Options
% 2.97/0.98  
% 2.97/0.98  --dbg_backtrace                         false
% 2.97/0.98  --dbg_dump_prop_clauses                 false
% 2.97/0.98  --dbg_dump_prop_clauses_file            -
% 2.97/0.98  --dbg_out_stat                          false
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  ------ Proving...
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  % SZS status Theorem for theBenchmark.p
% 2.97/0.98  
% 2.97/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/0.98  
% 2.97/0.98  fof(f16,axiom,(
% 2.97/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.97/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f36,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(ennf_transformation,[],[f16])).
% 2.97/0.98  
% 2.97/0.98  fof(f37,plain,(
% 2.97/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(flattening,[],[f36])).
% 2.97/0.98  
% 2.97/0.98  fof(f46,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(nnf_transformation,[],[f37])).
% 2.97/0.98  
% 2.97/0.98  fof(f68,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f46])).
% 2.97/0.98  
% 2.97/0.98  fof(f17,conjecture,(
% 2.97/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.97/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f18,negated_conjecture,(
% 2.97/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.97/0.98    inference(negated_conjecture,[],[f17])).
% 2.97/0.98  
% 2.97/0.98  fof(f38,plain,(
% 2.97/0.98    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.97/0.98    inference(ennf_transformation,[],[f18])).
% 2.97/0.98  
% 2.97/0.98  fof(f39,plain,(
% 2.97/0.98    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.97/0.98    inference(flattening,[],[f38])).
% 2.97/0.98  
% 2.97/0.98  fof(f48,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK5) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(X2,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 2.97/0.98    introduced(choice_axiom,[])).
% 2.97/0.98  
% 2.97/0.98  fof(f47,plain,(
% 2.97/0.98    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.97/0.98    introduced(choice_axiom,[])).
% 2.97/0.98  
% 2.97/0.98  fof(f49,plain,(
% 2.97/0.98    (~r2_relset_1(sK2,sK3,sK4,sK5) & ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.97/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f39,f48,f47])).
% 2.97/0.98  
% 2.97/0.98  fof(f78,plain,(
% 2.97/0.98    v1_funct_2(sK5,sK2,sK3)),
% 2.97/0.98    inference(cnf_transformation,[],[f49])).
% 2.97/0.98  
% 2.97/0.98  fof(f79,plain,(
% 2.97/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.97/0.98    inference(cnf_transformation,[],[f49])).
% 2.97/0.98  
% 2.97/0.98  fof(f14,axiom,(
% 2.97/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.97/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f33,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(ennf_transformation,[],[f14])).
% 2.97/0.98  
% 2.97/0.98  fof(f66,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f33])).
% 2.97/0.98  
% 2.97/0.98  fof(f75,plain,(
% 2.97/0.98    v1_funct_2(sK4,sK2,sK3)),
% 2.97/0.98    inference(cnf_transformation,[],[f49])).
% 2.97/0.98  
% 2.97/0.98  fof(f76,plain,(
% 2.97/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.97/0.98    inference(cnf_transformation,[],[f49])).
% 2.97/0.98  
% 2.97/0.98  fof(f10,axiom,(
% 2.97/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 2.97/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f28,plain,(
% 2.97/0.98    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.97/0.98    inference(ennf_transformation,[],[f10])).
% 2.97/0.98  
% 2.97/0.98  fof(f29,plain,(
% 2.97/0.98    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.97/0.98    inference(flattening,[],[f28])).
% 2.97/0.98  
% 2.97/0.98  fof(f44,plain,(
% 2.97/0.98    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))),
% 2.97/0.98    introduced(choice_axiom,[])).
% 2.97/0.98  
% 2.97/0.98  fof(f45,plain,(
% 2.97/0.98    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.97/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f44])).
% 2.97/0.98  
% 2.97/0.98  fof(f61,plain,(
% 2.97/0.98    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f45])).
% 2.97/0.98  
% 2.97/0.98  fof(f74,plain,(
% 2.97/0.98    v1_funct_1(sK4)),
% 2.97/0.98    inference(cnf_transformation,[],[f49])).
% 2.97/0.98  
% 2.97/0.98  fof(f11,axiom,(
% 2.97/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.97/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f30,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(ennf_transformation,[],[f11])).
% 2.97/0.98  
% 2.97/0.98  fof(f63,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f30])).
% 2.97/0.98  
% 2.97/0.98  fof(f77,plain,(
% 2.97/0.98    v1_funct_1(sK5)),
% 2.97/0.98    inference(cnf_transformation,[],[f49])).
% 2.97/0.98  
% 2.97/0.98  fof(f1,axiom,(
% 2.97/0.98    v1_xboole_0(k1_xboole_0)),
% 2.97/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f50,plain,(
% 2.97/0.98    v1_xboole_0(k1_xboole_0)),
% 2.97/0.98    inference(cnf_transformation,[],[f1])).
% 2.97/0.98  
% 2.97/0.98  fof(f2,axiom,(
% 2.97/0.98    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.97/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f21,plain,(
% 2.97/0.98    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.97/0.98    inference(ennf_transformation,[],[f2])).
% 2.97/0.98  
% 2.97/0.98  fof(f51,plain,(
% 2.97/0.98    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f21])).
% 2.97/0.98  
% 2.97/0.98  fof(f13,axiom,(
% 2.97/0.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.97/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f32,plain,(
% 2.97/0.98    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.97/0.98    inference(ennf_transformation,[],[f13])).
% 2.97/0.98  
% 2.97/0.98  fof(f65,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f32])).
% 2.97/0.98  
% 2.97/0.98  fof(f12,axiom,(
% 2.97/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.97/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f20,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.97/0.98    inference(pure_predicate_removal,[],[f12])).
% 2.97/0.98  
% 2.97/0.98  fof(f31,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(ennf_transformation,[],[f20])).
% 2.97/0.98  
% 2.97/0.98  fof(f64,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f31])).
% 2.97/0.98  
% 2.97/0.98  fof(f8,axiom,(
% 2.97/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.97/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f25,plain,(
% 2.97/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.97/0.98    inference(ennf_transformation,[],[f8])).
% 2.97/0.98  
% 2.97/0.98  fof(f26,plain,(
% 2.97/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.97/0.98    inference(flattening,[],[f25])).
% 2.97/0.98  
% 2.97/0.98  fof(f59,plain,(
% 2.97/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f26])).
% 2.97/0.98  
% 2.97/0.98  fof(f6,axiom,(
% 2.97/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.97/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f19,plain,(
% 2.97/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.97/0.98    inference(unused_predicate_definition_removal,[],[f6])).
% 2.97/0.98  
% 2.97/0.98  fof(f22,plain,(
% 2.97/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 2.97/0.98    inference(ennf_transformation,[],[f19])).
% 2.97/0.98  
% 2.97/0.98  fof(f57,plain,(
% 2.97/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f22])).
% 2.97/0.98  
% 2.97/0.98  fof(f9,axiom,(
% 2.97/0.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.97/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f27,plain,(
% 2.97/0.98    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.97/0.98    inference(ennf_transformation,[],[f9])).
% 2.97/0.98  
% 2.97/0.98  fof(f60,plain,(
% 2.97/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f27])).
% 2.97/0.98  
% 2.97/0.98  fof(f7,axiom,(
% 2.97/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.97/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f23,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.97/0.98    inference(ennf_transformation,[],[f7])).
% 2.97/0.98  
% 2.97/0.98  fof(f24,plain,(
% 2.97/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.97/0.98    inference(flattening,[],[f23])).
% 2.97/0.98  
% 2.97/0.98  fof(f58,plain,(
% 2.97/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f24])).
% 2.97/0.98  
% 2.97/0.98  fof(f80,plain,(
% 2.97/0.98    ( ! [X4] : (k1_funct_1(sK4,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK2)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f49])).
% 2.97/0.98  
% 2.97/0.98  fof(f62,plain,(
% 2.97/0.98    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK1(X0,X1)) != k1_funct_1(X1,sK1(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.97/0.98    inference(cnf_transformation,[],[f45])).
% 2.97/0.98  
% 2.97/0.98  fof(f15,axiom,(
% 2.97/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.97/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f34,plain,(
% 2.97/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.97/0.98    inference(ennf_transformation,[],[f15])).
% 2.97/0.98  
% 2.97/0.98  fof(f35,plain,(
% 2.97/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.98    inference(flattening,[],[f34])).
% 2.97/0.98  
% 2.97/0.98  fof(f67,plain,(
% 2.97/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f35])).
% 2.97/0.98  
% 2.97/0.98  fof(f81,plain,(
% 2.97/0.98    ~r2_relset_1(sK2,sK3,sK4,sK5)),
% 2.97/0.98    inference(cnf_transformation,[],[f49])).
% 2.97/0.98  
% 2.97/0.98  fof(f5,axiom,(
% 2.97/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.97/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.98  
% 2.97/0.98  fof(f56,plain,(
% 2.97/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.97/0.98    inference(cnf_transformation,[],[f5])).
% 2.97/0.98  
% 2.97/0.98  cnf(c_23,plain,
% 2.97/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.97/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.97/0.98      | k1_xboole_0 = X2 ),
% 2.97/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_27,negated_conjecture,
% 2.97/0.98      ( v1_funct_2(sK5,sK2,sK3) ),
% 2.97/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_495,plain,
% 2.97/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.97/0.98      | sK5 != X0
% 2.97/0.98      | sK3 != X2
% 2.97/0.98      | sK2 != X1
% 2.97/0.98      | k1_xboole_0 = X2 ),
% 2.97/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_496,plain,
% 2.97/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.97/0.98      | k1_relset_1(sK2,sK3,sK5) = sK2
% 2.97/0.98      | k1_xboole_0 = sK3 ),
% 2.97/0.98      inference(unflattening,[status(thm)],[c_495]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_26,negated_conjecture,
% 2.97/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.97/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_498,plain,
% 2.97/0.98      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 2.97/0.98      inference(global_propositional_subsumption,
% 2.97/0.98                [status(thm)],
% 2.97/0.98                [c_496,c_26]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1130,plain,
% 2.97/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_16,plain,
% 2.97/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.97/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1132,plain,
% 2.97/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.97/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_2792,plain,
% 2.97/0.98      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_1130,c_1132]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_3206,plain,
% 2.97/0.98      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_498,c_2792]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_30,negated_conjecture,
% 2.97/0.98      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.97/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_506,plain,
% 2.97/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.97/0.98      | sK4 != X0
% 2.97/0.98      | sK3 != X2
% 2.97/0.98      | sK2 != X1
% 2.97/0.98      | k1_xboole_0 = X2 ),
% 2.97/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_507,plain,
% 2.97/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.97/0.98      | k1_relset_1(sK2,sK3,sK4) = sK2
% 2.97/0.98      | k1_xboole_0 = sK3 ),
% 2.97/0.98      inference(unflattening,[status(thm)],[c_506]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_29,negated_conjecture,
% 2.97/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.97/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_509,plain,
% 2.97/0.98      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.97/0.98      inference(global_propositional_subsumption,
% 2.97/0.98                [status(thm)],
% 2.97/0.98                [c_507,c_29]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1128,plain,
% 2.97/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_2793,plain,
% 2.97/0.98      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_1128,c_1132]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_3237,plain,
% 2.97/0.98      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_509,c_2793]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_12,plain,
% 2.97/0.98      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 2.97/0.98      | ~ v1_funct_1(X1)
% 2.97/0.98      | ~ v1_funct_1(X0)
% 2.97/0.98      | ~ v1_relat_1(X1)
% 2.97/0.98      | ~ v1_relat_1(X0)
% 2.97/0.98      | X0 = X1
% 2.97/0.98      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 2.97/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1135,plain,
% 2.97/0.98      ( X0 = X1
% 2.97/0.98      | k1_relat_1(X1) != k1_relat_1(X0)
% 2.97/0.98      | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) = iProver_top
% 2.97/0.98      | v1_funct_1(X1) != iProver_top
% 2.97/0.98      | v1_funct_1(X0) != iProver_top
% 2.97/0.98      | v1_relat_1(X0) != iProver_top
% 2.97/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_3618,plain,
% 2.97/0.98      ( k1_relat_1(X0) != sK2
% 2.97/0.98      | sK4 = X0
% 2.97/0.98      | sK3 = k1_xboole_0
% 2.97/0.98      | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
% 2.97/0.98      | v1_funct_1(X0) != iProver_top
% 2.97/0.98      | v1_funct_1(sK4) != iProver_top
% 2.97/0.98      | v1_relat_1(X0) != iProver_top
% 2.97/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_3237,c_1135]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_31,negated_conjecture,
% 2.97/0.98      ( v1_funct_1(sK4) ),
% 2.97/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_32,plain,
% 2.97/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_34,plain,
% 2.97/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_13,plain,
% 2.97/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.98      | v1_relat_1(X0) ),
% 2.97/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1364,plain,
% 2.97/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.97/0.98      | v1_relat_1(sK4) ),
% 2.97/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1365,plain,
% 2.97/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.97/0.98      | v1_relat_1(sK4) = iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_1364]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_3974,plain,
% 2.97/0.98      ( v1_relat_1(X0) != iProver_top
% 2.97/0.98      | k1_relat_1(X0) != sK2
% 2.97/0.98      | sK4 = X0
% 2.97/0.98      | sK3 = k1_xboole_0
% 2.97/0.98      | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
% 2.97/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.97/0.98      inference(global_propositional_subsumption,
% 2.97/0.98                [status(thm)],
% 2.97/0.98                [c_3618,c_32,c_34,c_1365]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_3975,plain,
% 2.97/0.98      ( k1_relat_1(X0) != sK2
% 2.97/0.98      | sK4 = X0
% 2.97/0.98      | sK3 = k1_xboole_0
% 2.97/0.98      | r2_hidden(sK1(X0,sK4),k1_relat_1(X0)) = iProver_top
% 2.97/0.98      | v1_funct_1(X0) != iProver_top
% 2.97/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.97/0.98      inference(renaming,[status(thm)],[c_3974]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_3986,plain,
% 2.97/0.98      ( sK5 = sK4
% 2.97/0.98      | sK3 = k1_xboole_0
% 2.97/0.98      | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top
% 2.97/0.98      | v1_funct_1(sK5) != iProver_top
% 2.97/0.98      | v1_relat_1(sK5) != iProver_top ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_3206,c_3975]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_28,negated_conjecture,
% 2.97/0.98      ( v1_funct_1(sK5) ),
% 2.97/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_35,plain,
% 2.97/0.98      ( v1_funct_1(sK5) = iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_37,plain,
% 2.97/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_0,plain,
% 2.97/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.97/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1,plain,
% 2.97/0.98      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.97/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1334,plain,
% 2.97/0.98      ( ~ v1_xboole_0(sK5) | ~ v1_xboole_0(sK4) | sK4 = sK5 ),
% 2.97/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1361,plain,
% 2.97/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.97/0.98      | v1_relat_1(sK5) ),
% 2.97/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1362,plain,
% 2.97/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.97/0.98      | v1_relat_1(sK5) = iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_1361]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_728,plain,
% 2.97/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.97/0.98      theory(equality) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1590,plain,
% 2.97/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 2.97/0.98      inference(instantiation,[status(thm)],[c_728]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1592,plain,
% 2.97/0.98      ( v1_xboole_0(sK3)
% 2.97/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 2.97/0.98      | sK3 != k1_xboole_0 ),
% 2.97/0.98      inference(instantiation,[status(thm)],[c_1590]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1504,plain,
% 2.97/0.98      ( r2_hidden(sK1(X0,sK4),k1_relat_1(X0))
% 2.97/0.98      | ~ v1_funct_1(X0)
% 2.97/0.98      | ~ v1_funct_1(sK4)
% 2.97/0.98      | ~ v1_relat_1(X0)
% 2.97/0.98      | ~ v1_relat_1(sK4)
% 2.97/0.98      | X0 = sK4
% 2.97/0.98      | k1_relat_1(sK4) != k1_relat_1(X0) ),
% 2.97/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1767,plain,
% 2.97/0.98      ( r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5))
% 2.97/0.98      | ~ v1_funct_1(sK5)
% 2.97/0.98      | ~ v1_funct_1(sK4)
% 2.97/0.98      | ~ v1_relat_1(sK5)
% 2.97/0.98      | ~ v1_relat_1(sK4)
% 2.97/0.98      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.97/0.98      | sK5 = sK4 ),
% 2.97/0.98      inference(instantiation,[status(thm)],[c_1504]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1768,plain,
% 2.97/0.98      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.97/0.98      | sK5 = sK4
% 2.97/0.98      | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top
% 2.97/0.98      | v1_funct_1(sK5) != iProver_top
% 2.97/0.98      | v1_funct_1(sK4) != iProver_top
% 2.97/0.98      | v1_relat_1(sK5) != iProver_top
% 2.97/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_1767]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_733,plain,
% 2.97/0.98      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 2.97/0.98      theory(equality) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1990,plain,
% 2.97/0.98      ( k1_relat_1(sK4) = k1_relat_1(sK5) | sK4 != sK5 ),
% 2.97/0.98      inference(instantiation,[status(thm)],[c_733]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_15,plain,
% 2.97/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.98      | ~ v1_xboole_0(X2)
% 2.97/0.98      | v1_xboole_0(X0) ),
% 2.97/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1133,plain,
% 2.97/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.97/0.98      | v1_xboole_0(X2) != iProver_top
% 2.97/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_3332,plain,
% 2.97/0.98      ( v1_xboole_0(sK5) = iProver_top
% 2.97/0.98      | v1_xboole_0(sK3) != iProver_top ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_1130,c_1133]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_3369,plain,
% 2.97/0.98      ( v1_xboole_0(sK5) | ~ v1_xboole_0(sK3) ),
% 2.97/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3332]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_3333,plain,
% 2.97/0.98      ( v1_xboole_0(sK4) = iProver_top
% 2.97/0.98      | v1_xboole_0(sK3) != iProver_top ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_1128,c_1133]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_3370,plain,
% 2.97/0.98      ( v1_xboole_0(sK4) | ~ v1_xboole_0(sK3) ),
% 2.97/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3333]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_4661,plain,
% 2.97/0.98      ( sK5 = sK4
% 2.97/0.98      | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top ),
% 2.97/0.98      inference(global_propositional_subsumption,
% 2.97/0.98                [status(thm)],
% 2.97/0.98                [c_3986,c_32,c_34,c_35,c_37,c_0,c_1334,c_1362,c_1365,
% 2.97/0.98                 c_1592,c_1768,c_1990,c_3369,c_3370]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_14,plain,
% 2.97/0.98      ( v4_relat_1(X0,X1)
% 2.97/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.97/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_9,plain,
% 2.97/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.97/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_363,plain,
% 2.97/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.98      | ~ v1_relat_1(X0)
% 2.97/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.97/0.98      inference(resolution,[status(thm)],[c_14,c_9]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_367,plain,
% 2.97/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.97/0.98      inference(global_propositional_subsumption,
% 2.97/0.98                [status(thm)],
% 2.97/0.98                [c_363,c_14,c_13,c_9]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1124,plain,
% 2.97/0.98      ( k7_relat_1(X0,X1) = X0
% 2.97/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1547,plain,
% 2.97/0.98      ( k7_relat_1(sK5,sK2) = sK5 ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_1130,c_1124]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_7,plain,
% 2.97/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.97/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_10,plain,
% 2.97/0.98      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 2.97/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_327,plain,
% 2.97/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/0.98      | ~ v1_relat_1(X2)
% 2.97/0.98      | X3 != X1
% 2.97/0.98      | k1_relat_1(k7_relat_1(X2,X3)) != X0 ),
% 2.97/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_10]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_328,plain,
% 2.97/0.98      ( m1_subset_1(k1_relat_1(k7_relat_1(X0,X1)),k1_zfmisc_1(X1))
% 2.97/0.98      | ~ v1_relat_1(X0) ),
% 2.97/0.98      inference(unflattening,[status(thm)],[c_327]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1126,plain,
% 2.97/0.98      ( m1_subset_1(k1_relat_1(k7_relat_1(X0,X1)),k1_zfmisc_1(X1)) = iProver_top
% 2.97/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_2167,plain,
% 2.97/0.98      ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top
% 2.97/0.98      | v1_relat_1(sK5) != iProver_top ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_1547,c_1126]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_2320,plain,
% 2.97/0.98      ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK2)) = iProver_top ),
% 2.97/0.98      inference(global_propositional_subsumption,
% 2.97/0.98                [status(thm)],
% 2.97/0.98                [c_2167,c_37,c_1362]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_8,plain,
% 2.97/0.98      ( ~ r2_hidden(X0,X1)
% 2.97/0.98      | m1_subset_1(X0,X2)
% 2.97/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.97/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1137,plain,
% 2.97/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.97/0.98      | m1_subset_1(X0,X2) = iProver_top
% 2.97/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_3461,plain,
% 2.97/0.98      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.97/0.98      | m1_subset_1(X0,sK2) = iProver_top ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_2320,c_1137]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_4827,plain,
% 2.97/0.98      ( sK5 = sK4 | m1_subset_1(sK1(sK5,sK4),sK2) = iProver_top ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_4661,c_3461]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_25,negated_conjecture,
% 2.97/0.98      ( ~ m1_subset_1(X0,sK2) | k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0) ),
% 2.97/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1131,plain,
% 2.97/0.98      ( k1_funct_1(sK4,X0) = k1_funct_1(sK5,X0)
% 2.97/0.98      | m1_subset_1(X0,sK2) != iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_5709,plain,
% 2.97/0.98      ( k1_funct_1(sK5,sK1(sK5,sK4)) = k1_funct_1(sK4,sK1(sK5,sK4))
% 2.97/0.98      | sK5 = sK4 ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_4827,c_1131]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_11,plain,
% 2.97/0.98      ( ~ v1_funct_1(X0)
% 2.97/0.98      | ~ v1_funct_1(X1)
% 2.97/0.98      | ~ v1_relat_1(X0)
% 2.97/0.98      | ~ v1_relat_1(X1)
% 2.97/0.98      | X1 = X0
% 2.97/0.98      | k1_funct_1(X0,sK1(X1,X0)) != k1_funct_1(X1,sK1(X1,X0))
% 2.97/0.98      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 2.97/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1136,plain,
% 2.97/0.98      ( X0 = X1
% 2.97/0.98      | k1_funct_1(X1,sK1(X0,X1)) != k1_funct_1(X0,sK1(X0,X1))
% 2.97/0.98      | k1_relat_1(X1) != k1_relat_1(X0)
% 2.97/0.98      | v1_funct_1(X0) != iProver_top
% 2.97/0.98      | v1_funct_1(X1) != iProver_top
% 2.97/0.98      | v1_relat_1(X1) != iProver_top
% 2.97/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_5712,plain,
% 2.97/0.98      ( k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.97/0.98      | sK5 = sK4
% 2.97/0.98      | v1_funct_1(sK5) != iProver_top
% 2.97/0.98      | v1_funct_1(sK4) != iProver_top
% 2.97/0.98      | v1_relat_1(sK5) != iProver_top
% 2.97/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_5709,c_1136]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_5713,plain,
% 2.97/0.98      ( ~ v1_funct_1(sK5)
% 2.97/0.98      | ~ v1_funct_1(sK4)
% 2.97/0.98      | ~ v1_relat_1(sK5)
% 2.97/0.98      | ~ v1_relat_1(sK4)
% 2.97/0.98      | k1_relat_1(sK4) != k1_relat_1(sK5)
% 2.97/0.98      | sK5 = sK4 ),
% 2.97/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_5712]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_5754,plain,
% 2.97/0.98      ( k1_relat_1(sK4) != k1_relat_1(sK5) | sK5 = sK4 ),
% 2.97/0.98      inference(global_propositional_subsumption,
% 2.97/0.98                [status(thm)],
% 2.97/0.98                [c_5712,c_31,c_29,c_28,c_26,c_1361,c_1364,c_5713]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_5758,plain,
% 2.97/0.98      ( k1_relat_1(sK4) != sK2 | sK5 = sK4 | sK3 = k1_xboole_0 ),
% 2.97/0.98      inference(superposition,[status(thm)],[c_3206,c_5754]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_17,plain,
% 2.97/0.98      ( r2_relset_1(X0,X1,X2,X2)
% 2.97/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.97/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.97/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_24,negated_conjecture,
% 2.97/0.98      ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
% 2.97/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_342,plain,
% 2.97/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.98      | sK5 != X0
% 2.97/0.98      | sK4 != X0
% 2.97/0.98      | sK3 != X2
% 2.97/0.98      | sK2 != X1 ),
% 2.97/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_343,plain,
% 2.97/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.97/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.97/0.98      | sK4 != sK5 ),
% 2.97/0.98      inference(unflattening,[status(thm)],[c_342]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_347,plain,
% 2.97/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.97/0.98      | sK4 != sK5 ),
% 2.97/0.98      inference(global_propositional_subsumption,
% 2.97/0.98                [status(thm)],
% 2.97/0.98                [c_343,c_26]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_5591,plain,
% 2.97/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.97/0.98      | sK4 != sK5 ),
% 2.97/0.98      inference(instantiation,[status(thm)],[c_347]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_5759,plain,
% 2.97/0.98      ( sK5 = sK4 | sK3 = k1_xboole_0 ),
% 2.97/0.98      inference(global_propositional_subsumption,
% 2.97/0.98                [status(thm)],
% 2.97/0.98                [c_5758,c_26,c_0,c_1334,c_1592,c_3237,c_3369,c_3370,
% 2.97/0.98                 c_5591]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_5761,plain,
% 2.97/0.98      ( sK5 = sK4 ),
% 2.97/0.98      inference(global_propositional_subsumption,
% 2.97/0.98                [status(thm)],
% 2.97/0.98                [c_5759,c_26,c_0,c_1334,c_1592,c_3237,c_3369,c_3370,
% 2.97/0.98                 c_5591,c_5758]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1125,plain,
% 2.97/0.98      ( sK4 != sK5
% 2.97/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_347]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_5782,plain,
% 2.97/0.98      ( sK4 != sK4
% 2.97/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 2.97/0.98      inference(demodulation,[status(thm)],[c_5761,c_1125]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_5790,plain,
% 2.97/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 2.97/0.98      inference(equality_resolution_simp,[status(thm)],[c_5782]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_5794,plain,
% 2.97/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 2.97/0.98      inference(instantiation,[status(thm)],[c_5790]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_6,plain,
% 2.97/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.97/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_1354,plain,
% 2.97/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.97/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_5614,plain,
% 2.97/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.97/0.98      inference(instantiation,[status(thm)],[c_1354]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(c_5617,plain,
% 2.97/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.97/0.98      inference(predicate_to_equality,[status(thm)],[c_5614]) ).
% 2.97/0.98  
% 2.97/0.98  cnf(contradiction,plain,
% 2.97/0.98      ( $false ),
% 2.97/0.98      inference(minisat,[status(thm)],[c_5794,c_5617]) ).
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/0.98  
% 2.97/0.98  ------                               Statistics
% 2.97/0.98  
% 2.97/0.98  ------ General
% 2.97/0.98  
% 2.97/0.98  abstr_ref_over_cycles:                  0
% 2.97/0.98  abstr_ref_under_cycles:                 0
% 2.97/0.98  gc_basic_clause_elim:                   0
% 2.97/0.98  forced_gc_time:                         0
% 2.97/0.98  parsing_time:                           0.009
% 2.97/0.98  unif_index_cands_time:                  0.
% 2.97/0.98  unif_index_add_time:                    0.
% 2.97/0.98  orderings_time:                         0.
% 2.97/0.98  out_proof_time:                         0.014
% 2.97/0.98  total_time:                             0.199
% 2.97/0.98  num_of_symbols:                         53
% 2.97/0.98  num_of_terms:                           5800
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing
% 2.97/0.98  
% 2.97/0.98  num_of_splits:                          0
% 2.97/0.98  num_of_split_atoms:                     0
% 2.97/0.98  num_of_reused_defs:                     0
% 2.97/0.98  num_eq_ax_congr_red:                    23
% 2.97/0.98  num_of_sem_filtered_clauses:            1
% 2.97/0.98  num_of_subtypes:                        0
% 2.97/0.98  monotx_restored_types:                  0
% 2.97/0.98  sat_num_of_epr_types:                   0
% 2.97/0.98  sat_num_of_non_cyclic_types:            0
% 2.97/0.98  sat_guarded_non_collapsed_types:        0
% 2.97/0.98  num_pure_diseq_elim:                    0
% 2.97/0.98  simp_replaced_by:                       0
% 2.97/0.98  res_preprocessed:                       136
% 2.97/0.98  prep_upred:                             0
% 2.97/0.98  prep_unflattend:                        43
% 2.97/0.98  smt_new_axioms:                         0
% 2.97/0.98  pred_elim_cands:                        5
% 2.97/0.98  pred_elim:                              4
% 2.97/0.98  pred_elim_cl:                           5
% 2.97/0.98  pred_elim_cycles:                       7
% 2.97/0.98  merged_defs:                            0
% 2.97/0.98  merged_defs_ncl:                        0
% 2.97/0.98  bin_hyper_res:                          0
% 2.97/0.98  prep_cycles:                            4
% 2.97/0.98  pred_elim_time:                         0.006
% 2.97/0.98  splitting_time:                         0.
% 2.97/0.98  sem_filter_time:                        0.
% 2.97/0.98  monotx_time:                            0.
% 2.97/0.98  subtype_inf_time:                       0.
% 2.97/0.98  
% 2.97/0.98  ------ Problem properties
% 2.97/0.98  
% 2.97/0.98  clauses:                                27
% 2.97/0.98  conjectures:                            5
% 2.97/0.98  epr:                                    4
% 2.97/0.98  horn:                                   21
% 2.97/0.98  ground:                                 11
% 2.97/0.98  unary:                                  9
% 2.97/0.98  binary:                                 8
% 2.97/0.98  lits:                                   65
% 2.97/0.98  lits_eq:                                29
% 2.97/0.98  fd_pure:                                0
% 2.97/0.98  fd_pseudo:                              0
% 2.97/0.98  fd_cond:                                1
% 2.97/0.98  fd_pseudo_cond:                         3
% 2.97/0.98  ac_symbols:                             0
% 2.97/0.98  
% 2.97/0.98  ------ Propositional Solver
% 2.97/0.98  
% 2.97/0.98  prop_solver_calls:                      27
% 2.97/0.98  prop_fast_solver_calls:                 957
% 2.97/0.98  smt_solver_calls:                       0
% 2.97/0.98  smt_fast_solver_calls:                  0
% 2.97/0.98  prop_num_of_clauses:                    2227
% 2.97/0.98  prop_preprocess_simplified:             6077
% 2.97/0.98  prop_fo_subsumed:                       27
% 2.97/0.98  prop_solver_time:                       0.
% 2.97/0.98  smt_solver_time:                        0.
% 2.97/0.98  smt_fast_solver_time:                   0.
% 2.97/0.98  prop_fast_solver_time:                  0.
% 2.97/0.98  prop_unsat_core_time:                   0.
% 2.97/0.98  
% 2.97/0.98  ------ QBF
% 2.97/0.98  
% 2.97/0.98  qbf_q_res:                              0
% 2.97/0.98  qbf_num_tautologies:                    0
% 2.97/0.98  qbf_prep_cycles:                        0
% 2.97/0.98  
% 2.97/0.98  ------ BMC1
% 2.97/0.98  
% 2.97/0.98  bmc1_current_bound:                     -1
% 2.97/0.98  bmc1_last_solved_bound:                 -1
% 2.97/0.98  bmc1_unsat_core_size:                   -1
% 2.97/0.98  bmc1_unsat_core_parents_size:           -1
% 2.97/0.98  bmc1_merge_next_fun:                    0
% 2.97/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.97/0.98  
% 2.97/0.98  ------ Instantiation
% 2.97/0.98  
% 2.97/0.98  inst_num_of_clauses:                    720
% 2.97/0.98  inst_num_in_passive:                    386
% 2.97/0.98  inst_num_in_active:                     323
% 2.97/0.98  inst_num_in_unprocessed:                11
% 2.97/0.98  inst_num_of_loops:                      400
% 2.97/0.98  inst_num_of_learning_restarts:          0
% 2.97/0.98  inst_num_moves_active_passive:          74
% 2.97/0.98  inst_lit_activity:                      0
% 2.97/0.98  inst_lit_activity_moves:                0
% 2.97/0.98  inst_num_tautologies:                   0
% 2.97/0.98  inst_num_prop_implied:                  0
% 2.97/0.98  inst_num_existing_simplified:           0
% 2.97/0.98  inst_num_eq_res_simplified:             0
% 2.97/0.98  inst_num_child_elim:                    0
% 2.97/0.98  inst_num_of_dismatching_blockings:      273
% 2.97/0.98  inst_num_of_non_proper_insts:           863
% 2.97/0.98  inst_num_of_duplicates:                 0
% 2.97/0.98  inst_inst_num_from_inst_to_res:         0
% 2.97/0.98  inst_dismatching_checking_time:         0.
% 2.97/0.98  
% 2.97/0.98  ------ Resolution
% 2.97/0.98  
% 2.97/0.98  res_num_of_clauses:                     0
% 2.97/0.98  res_num_in_passive:                     0
% 2.97/0.98  res_num_in_active:                      0
% 2.97/0.98  res_num_of_loops:                       140
% 2.97/0.98  res_forward_subset_subsumed:            37
% 2.97/0.98  res_backward_subset_subsumed:           0
% 2.97/0.98  res_forward_subsumed:                   0
% 2.97/0.98  res_backward_subsumed:                  0
% 2.97/0.98  res_forward_subsumption_resolution:     0
% 2.97/0.98  res_backward_subsumption_resolution:    0
% 2.97/0.98  res_clause_to_clause_subsumption:       163
% 2.97/0.98  res_orphan_elimination:                 0
% 2.97/0.98  res_tautology_del:                      44
% 2.97/0.98  res_num_eq_res_simplified:              0
% 2.97/0.98  res_num_sel_changes:                    0
% 2.97/0.98  res_moves_from_active_to_pass:          0
% 2.97/0.98  
% 2.97/0.98  ------ Superposition
% 2.97/0.98  
% 2.97/0.98  sup_time_total:                         0.
% 2.97/0.98  sup_time_generating:                    0.
% 2.97/0.98  sup_time_sim_full:                      0.
% 2.97/0.98  sup_time_sim_immed:                     0.
% 2.97/0.98  
% 2.97/0.98  sup_num_of_clauses:                     114
% 2.97/0.98  sup_num_in_active:                      51
% 2.97/0.98  sup_num_in_passive:                     63
% 2.97/0.98  sup_num_of_loops:                       79
% 2.97/0.98  sup_fw_superposition:                   94
% 2.97/0.98  sup_bw_superposition:                   54
% 2.97/0.98  sup_immediate_simplified:               32
% 2.97/0.98  sup_given_eliminated:                   0
% 2.97/0.98  comparisons_done:                       0
% 2.97/0.98  comparisons_avoided:                    18
% 2.97/0.98  
% 2.97/0.98  ------ Simplifications
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  sim_fw_subset_subsumed:                 2
% 2.97/0.98  sim_bw_subset_subsumed:                 6
% 2.97/0.98  sim_fw_subsumed:                        6
% 2.97/0.98  sim_bw_subsumed:                        4
% 2.97/0.98  sim_fw_subsumption_res:                 0
% 2.97/0.98  sim_bw_subsumption_res:                 0
% 2.97/0.98  sim_tautology_del:                      0
% 2.97/0.98  sim_eq_tautology_del:                   12
% 2.97/0.98  sim_eq_res_simp:                        1
% 2.97/0.98  sim_fw_demodulated:                     12
% 2.97/0.98  sim_bw_demodulated:                     23
% 2.97/0.98  sim_light_normalised:                   16
% 2.97/0.98  sim_joinable_taut:                      0
% 2.97/0.98  sim_joinable_simp:                      0
% 2.97/0.98  sim_ac_normalised:                      0
% 2.97/0.98  sim_smt_subsumption:                    0
% 2.97/0.98  
%------------------------------------------------------------------------------
