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
% DateTime   : Thu Dec  3 12:05:06 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  204 (4134 expanded)
%              Number of clauses        :  111 (1017 expanded)
%              Number of leaves         :   25 ( 968 expanded)
%              Depth                    :   29
%              Number of atoms          :  531 (9827 expanded)
%              Number of equality atoms :  290 (4544 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f26])).

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

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f62,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)
      & k1_xboole_0 != sK4
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
      & v1_funct_2(sK5,k1_tarski(sK3),sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
    & v1_funct_2(sK5,k1_tarski(sK3),sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f48,f62])).

fof(f102,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) ),
    inference(cnf_transformation,[],[f63])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f105,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f106,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f71,f105])).

fof(f111,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(definition_unfolding,[],[f102,f106])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f76,f106])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f86,f106,f106])).

fof(f100,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f104,plain,(
    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f110,plain,(
    k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(definition_unfolding,[],[f104,f106,f106])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f84,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f22,axiom,(
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

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f101,plain,(
    v1_funct_2(sK5,k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f112,plain,(
    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f101,f106])).

fof(f103,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f63])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f56])).

fof(f59,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
        & r2_hidden(sK2(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK2(X1,X2),X6),X2)
            & r2_hidden(sK2(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f57,f59,f58])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f85,f106,f106])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1427,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1418,plain,
    ( k11_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1408,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1413,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1980,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1408,c_1413])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1420,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3080,plain,
    ( k9_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1980,c_1420])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1419,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2217,plain,
    ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1980,c_1419])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_405,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0)))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_37])).

cnf(c_406,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k2_enumset1(X0,X0,X0,X0))) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_1406,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_40,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_407,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_1639,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1640,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1639])).

cnf(c_1693,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k2_enumset1(X0,X0,X0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1406,c_40,c_407,c_1640])).

cnf(c_1694,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1693])).

cnf(c_2565,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k9_relat_1(sK5,k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2217,c_1694])).

cnf(c_3194,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3080,c_2565])).

cnf(c_3799,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
    | k11_relat_1(sK5,X0) = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1418,c_3194])).

cnf(c_8740,plain,
    ( k11_relat_1(sK5,X0) = k1_xboole_0
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3799,c_40,c_1640])).

cnf(c_8741,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
    | k11_relat_1(sK5,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8740])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1412,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2975,plain,
    ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1408,c_1412])).

cnf(c_33,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_3089,plain,
    ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_2975,c_33])).

cnf(c_8747,plain,
    ( k11_relat_1(sK5,sK3) != k2_relat_1(sK5)
    | k11_relat_1(sK5,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8741,c_3089])).

cnf(c_22,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_22,c_13])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_22,c_21,c_13])).

cnf(c_1407,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_1711,plain,
    ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = sK5 ),
    inference(superposition,[status(thm)],[c_1408,c_1407])).

cnf(c_2569,plain,
    ( k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1711,c_2217])).

cnf(c_3218,plain,
    ( k11_relat_1(sK5,sK3) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2569,c_3080])).

cnf(c_8750,plain,
    ( k11_relat_1(sK5,sK3) = k1_xboole_0
    | k2_relat_1(sK5) != k2_relat_1(sK5) ),
    inference(light_normalisation,[status(thm)],[c_8747,c_3218])).

cnf(c_8751,plain,
    ( k11_relat_1(sK5,sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8750])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1416,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2820,plain,
    ( k7_relat_1(sK5,X0) = k1_xboole_0
    | k9_relat_1(sK5,X0) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_1416])).

cnf(c_3251,plain,
    ( k7_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
    | k11_relat_1(sK5,X0) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK5,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3080,c_2820])).

cnf(c_9475,plain,
    ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8751,c_3251])).

cnf(c_9478,plain,
    ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9475,c_1711])).

cnf(c_9479,plain,
    ( sK5 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9478,c_1711])).

cnf(c_3252,plain,
    ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k1_xboole_0
    | k2_relat_1(sK5) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2569,c_2820])).

cnf(c_3256,plain,
    ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k1_xboole_0
    | k2_relat_1(sK5) != k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3252,c_1711])).

cnf(c_3257,plain,
    ( k2_relat_1(sK5) != k1_xboole_0
    | sK5 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3256,c_1711])).

cnf(c_3390,plain,
    ( sK5 = k1_xboole_0
    | k2_relat_1(sK5) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3257,c_40,c_1640])).

cnf(c_3391,plain,
    ( k2_relat_1(sK5) != k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3390])).

cnf(c_9472,plain,
    ( k2_relat_1(sK5) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8751,c_3218])).

cnf(c_9556,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9479,c_3391,c_9472])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_620,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK3,sK3,sK3,sK3) != X1
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X2
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_36])).

cnf(c_621,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
    | k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_623,plain,
    ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_621,c_35,c_34])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k4_tarski(X3,sK1(X0,X3)),X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1411,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3688,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_1411])).

cnf(c_4054,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3688,c_40])).

cnf(c_9606,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9556,c_4054])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1422,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1979,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_1413])).

cnf(c_3079,plain,
    ( k9_relat_1(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1979,c_1420])).

cnf(c_2216,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1979,c_1419])).

cnf(c_14,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1910,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1422,c_1407])).

cnf(c_2221,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2216,c_14,c_1910])).

cnf(c_3084,plain,
    ( k11_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3079,c_2221])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1417,plain,
    ( k11_relat_1(X0,X1) != k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4777,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3084,c_1417])).

cnf(c_15,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4778,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4777,c_15])).

cnf(c_1631,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1633,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1631])).

cnf(c_1632,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1635,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1632])).

cnf(c_4922,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4778,c_1633,c_1635])).

cnf(c_10172,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9606,c_4922])).

cnf(c_10176,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1427,c_10172])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1423,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1425,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3785,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_1425])).

cnf(c_10398,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10176,c_3785])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_420,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_37])).

cnf(c_421,plain,
    ( ~ v1_relat_1(sK5)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_1405,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_1669,plain,
    ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1405,c_35,c_421,c_1639])).

cnf(c_1670,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
    | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
    inference(renaming,[status(thm)],[c_1669])).

cnf(c_9618,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(k1_xboole_0)
    | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_9556,c_1670])).

cnf(c_9633,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
    | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9618,c_14,c_15])).

cnf(c_10915,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10398,c_9633])).

cnf(c_9612,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) != k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_9556,c_3089])).

cnf(c_9642,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9612,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10915,c_9642])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:06:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.45/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.45/0.99  
% 3.45/0.99  ------  iProver source info
% 3.45/0.99  
% 3.45/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.45/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.45/0.99  git: non_committed_changes: false
% 3.45/0.99  git: last_make_outside_of_git: false
% 3.45/0.99  
% 3.45/0.99  ------ 
% 3.45/0.99  
% 3.45/0.99  ------ Input Options
% 3.45/0.99  
% 3.45/0.99  --out_options                           all
% 3.45/0.99  --tptp_safe_out                         true
% 3.45/0.99  --problem_path                          ""
% 3.45/0.99  --include_path                          ""
% 3.45/0.99  --clausifier                            res/vclausify_rel
% 3.45/0.99  --clausifier_options                    --mode clausify
% 3.45/0.99  --stdin                                 false
% 3.45/0.99  --stats_out                             all
% 3.45/0.99  
% 3.45/0.99  ------ General Options
% 3.45/0.99  
% 3.45/0.99  --fof                                   false
% 3.45/0.99  --time_out_real                         305.
% 3.45/0.99  --time_out_virtual                      -1.
% 3.45/0.99  --symbol_type_check                     false
% 3.45/0.99  --clausify_out                          false
% 3.45/0.99  --sig_cnt_out                           false
% 3.45/0.99  --trig_cnt_out                          false
% 3.45/0.99  --trig_cnt_out_tolerance                1.
% 3.45/0.99  --trig_cnt_out_sk_spl                   false
% 3.45/0.99  --abstr_cl_out                          false
% 3.45/0.99  
% 3.45/0.99  ------ Global Options
% 3.45/0.99  
% 3.45/0.99  --schedule                              default
% 3.45/0.99  --add_important_lit                     false
% 3.45/0.99  --prop_solver_per_cl                    1000
% 3.45/0.99  --min_unsat_core                        false
% 3.45/0.99  --soft_assumptions                      false
% 3.45/0.99  --soft_lemma_size                       3
% 3.45/0.99  --prop_impl_unit_size                   0
% 3.45/0.99  --prop_impl_unit                        []
% 3.45/0.99  --share_sel_clauses                     true
% 3.45/0.99  --reset_solvers                         false
% 3.45/0.99  --bc_imp_inh                            [conj_cone]
% 3.45/0.99  --conj_cone_tolerance                   3.
% 3.45/0.99  --extra_neg_conj                        none
% 3.45/0.99  --large_theory_mode                     true
% 3.45/0.99  --prolific_symb_bound                   200
% 3.45/0.99  --lt_threshold                          2000
% 3.45/0.99  --clause_weak_htbl                      true
% 3.45/0.99  --gc_record_bc_elim                     false
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing Options
% 3.45/0.99  
% 3.45/0.99  --preprocessing_flag                    true
% 3.45/0.99  --time_out_prep_mult                    0.1
% 3.45/0.99  --splitting_mode                        input
% 3.45/0.99  --splitting_grd                         true
% 3.45/0.99  --splitting_cvd                         false
% 3.45/0.99  --splitting_cvd_svl                     false
% 3.45/0.99  --splitting_nvd                         32
% 3.45/0.99  --sub_typing                            true
% 3.45/0.99  --prep_gs_sim                           true
% 3.45/0.99  --prep_unflatten                        true
% 3.45/0.99  --prep_res_sim                          true
% 3.45/0.99  --prep_upred                            true
% 3.45/0.99  --prep_sem_filter                       exhaustive
% 3.45/0.99  --prep_sem_filter_out                   false
% 3.45/0.99  --pred_elim                             true
% 3.45/0.99  --res_sim_input                         true
% 3.45/0.99  --eq_ax_congr_red                       true
% 3.45/0.99  --pure_diseq_elim                       true
% 3.45/0.99  --brand_transform                       false
% 3.45/0.99  --non_eq_to_eq                          false
% 3.45/0.99  --prep_def_merge                        true
% 3.45/0.99  --prep_def_merge_prop_impl              false
% 3.45/0.99  --prep_def_merge_mbd                    true
% 3.45/0.99  --prep_def_merge_tr_red                 false
% 3.45/0.99  --prep_def_merge_tr_cl                  false
% 3.45/0.99  --smt_preprocessing                     true
% 3.45/0.99  --smt_ac_axioms                         fast
% 3.45/0.99  --preprocessed_out                      false
% 3.45/0.99  --preprocessed_stats                    false
% 3.45/0.99  
% 3.45/0.99  ------ Abstraction refinement Options
% 3.45/0.99  
% 3.45/0.99  --abstr_ref                             []
% 3.45/0.99  --abstr_ref_prep                        false
% 3.45/0.99  --abstr_ref_until_sat                   false
% 3.45/0.99  --abstr_ref_sig_restrict                funpre
% 3.45/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/0.99  --abstr_ref_under                       []
% 3.45/0.99  
% 3.45/0.99  ------ SAT Options
% 3.45/0.99  
% 3.45/0.99  --sat_mode                              false
% 3.45/0.99  --sat_fm_restart_options                ""
% 3.45/0.99  --sat_gr_def                            false
% 3.45/0.99  --sat_epr_types                         true
% 3.45/0.99  --sat_non_cyclic_types                  false
% 3.45/0.99  --sat_finite_models                     false
% 3.45/0.99  --sat_fm_lemmas                         false
% 3.45/0.99  --sat_fm_prep                           false
% 3.45/0.99  --sat_fm_uc_incr                        true
% 3.45/0.99  --sat_out_model                         small
% 3.45/0.99  --sat_out_clauses                       false
% 3.45/0.99  
% 3.45/0.99  ------ QBF Options
% 3.45/0.99  
% 3.45/0.99  --qbf_mode                              false
% 3.45/0.99  --qbf_elim_univ                         false
% 3.45/0.99  --qbf_dom_inst                          none
% 3.45/0.99  --qbf_dom_pre_inst                      false
% 3.45/0.99  --qbf_sk_in                             false
% 3.45/0.99  --qbf_pred_elim                         true
% 3.45/0.99  --qbf_split                             512
% 3.45/0.99  
% 3.45/0.99  ------ BMC1 Options
% 3.45/0.99  
% 3.45/0.99  --bmc1_incremental                      false
% 3.45/0.99  --bmc1_axioms                           reachable_all
% 3.45/0.99  --bmc1_min_bound                        0
% 3.45/0.99  --bmc1_max_bound                        -1
% 3.45/0.99  --bmc1_max_bound_default                -1
% 3.45/0.99  --bmc1_symbol_reachability              true
% 3.45/0.99  --bmc1_property_lemmas                  false
% 3.45/0.99  --bmc1_k_induction                      false
% 3.45/0.99  --bmc1_non_equiv_states                 false
% 3.45/0.99  --bmc1_deadlock                         false
% 3.45/0.99  --bmc1_ucm                              false
% 3.45/0.99  --bmc1_add_unsat_core                   none
% 3.45/0.99  --bmc1_unsat_core_children              false
% 3.45/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/0.99  --bmc1_out_stat                         full
% 3.45/0.99  --bmc1_ground_init                      false
% 3.45/0.99  --bmc1_pre_inst_next_state              false
% 3.45/0.99  --bmc1_pre_inst_state                   false
% 3.45/0.99  --bmc1_pre_inst_reach_state             false
% 3.45/0.99  --bmc1_out_unsat_core                   false
% 3.45/0.99  --bmc1_aig_witness_out                  false
% 3.45/0.99  --bmc1_verbose                          false
% 3.45/0.99  --bmc1_dump_clauses_tptp                false
% 3.45/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.45/0.99  --bmc1_dump_file                        -
% 3.45/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.45/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.45/0.99  --bmc1_ucm_extend_mode                  1
% 3.45/0.99  --bmc1_ucm_init_mode                    2
% 3.45/0.99  --bmc1_ucm_cone_mode                    none
% 3.45/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.45/0.99  --bmc1_ucm_relax_model                  4
% 3.45/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.45/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/0.99  --bmc1_ucm_layered_model                none
% 3.45/0.99  --bmc1_ucm_max_lemma_size               10
% 3.45/0.99  
% 3.45/0.99  ------ AIG Options
% 3.45/0.99  
% 3.45/0.99  --aig_mode                              false
% 3.45/0.99  
% 3.45/0.99  ------ Instantiation Options
% 3.45/0.99  
% 3.45/0.99  --instantiation_flag                    true
% 3.45/0.99  --inst_sos_flag                         false
% 3.45/0.99  --inst_sos_phase                        true
% 3.45/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel_side                     num_symb
% 3.45/0.99  --inst_solver_per_active                1400
% 3.45/0.99  --inst_solver_calls_frac                1.
% 3.45/0.99  --inst_passive_queue_type               priority_queues
% 3.45/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/0.99  --inst_passive_queues_freq              [25;2]
% 3.45/0.99  --inst_dismatching                      true
% 3.45/0.99  --inst_eager_unprocessed_to_passive     true
% 3.45/0.99  --inst_prop_sim_given                   true
% 3.45/0.99  --inst_prop_sim_new                     false
% 3.45/0.99  --inst_subs_new                         false
% 3.45/0.99  --inst_eq_res_simp                      false
% 3.45/0.99  --inst_subs_given                       false
% 3.45/0.99  --inst_orphan_elimination               true
% 3.45/0.99  --inst_learning_loop_flag               true
% 3.45/0.99  --inst_learning_start                   3000
% 3.45/0.99  --inst_learning_factor                  2
% 3.45/0.99  --inst_start_prop_sim_after_learn       3
% 3.45/0.99  --inst_sel_renew                        solver
% 3.45/0.99  --inst_lit_activity_flag                true
% 3.45/0.99  --inst_restr_to_given                   false
% 3.45/0.99  --inst_activity_threshold               500
% 3.45/0.99  --inst_out_proof                        true
% 3.45/0.99  
% 3.45/0.99  ------ Resolution Options
% 3.45/0.99  
% 3.45/0.99  --resolution_flag                       true
% 3.45/0.99  --res_lit_sel                           adaptive
% 3.45/0.99  --res_lit_sel_side                      none
% 3.45/0.99  --res_ordering                          kbo
% 3.45/0.99  --res_to_prop_solver                    active
% 3.45/0.99  --res_prop_simpl_new                    false
% 3.45/0.99  --res_prop_simpl_given                  true
% 3.45/0.99  --res_passive_queue_type                priority_queues
% 3.45/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/0.99  --res_passive_queues_freq               [15;5]
% 3.45/0.99  --res_forward_subs                      full
% 3.45/0.99  --res_backward_subs                     full
% 3.45/0.99  --res_forward_subs_resolution           true
% 3.45/0.99  --res_backward_subs_resolution          true
% 3.45/0.99  --res_orphan_elimination                true
% 3.45/0.99  --res_time_limit                        2.
% 3.45/0.99  --res_out_proof                         true
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Options
% 3.45/0.99  
% 3.45/0.99  --superposition_flag                    true
% 3.45/0.99  --sup_passive_queue_type                priority_queues
% 3.45/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.45/0.99  --demod_completeness_check              fast
% 3.45/0.99  --demod_use_ground                      true
% 3.45/0.99  --sup_to_prop_solver                    passive
% 3.45/0.99  --sup_prop_simpl_new                    true
% 3.45/0.99  --sup_prop_simpl_given                  true
% 3.45/0.99  --sup_fun_splitting                     false
% 3.45/0.99  --sup_smt_interval                      50000
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Simplification Setup
% 3.45/0.99  
% 3.45/0.99  --sup_indices_passive                   []
% 3.45/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_full_bw                           [BwDemod]
% 3.45/0.99  --sup_immed_triv                        [TrivRules]
% 3.45/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_immed_bw_main                     []
% 3.45/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/0.99  
% 3.45/0.99  ------ Combination Options
% 3.45/0.99  
% 3.45/0.99  --comb_res_mult                         3
% 3.45/0.99  --comb_sup_mult                         2
% 3.45/0.99  --comb_inst_mult                        10
% 3.45/0.99  
% 3.45/0.99  ------ Debug Options
% 3.45/0.99  
% 3.45/0.99  --dbg_backtrace                         false
% 3.45/0.99  --dbg_dump_prop_clauses                 false
% 3.45/0.99  --dbg_dump_prop_clauses_file            -
% 3.45/0.99  --dbg_out_stat                          false
% 3.45/0.99  ------ Parsing...
% 3.45/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/0.99  ------ Proving...
% 3.45/0.99  ------ Problem Properties 
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  clauses                                 31
% 3.45/0.99  conjectures                             3
% 3.45/0.99  EPR                                     6
% 3.45/0.99  Horn                                    27
% 3.45/0.99  unary                                   9
% 3.45/0.99  binary                                  8
% 3.45/0.99  lits                                    69
% 3.45/0.99  lits eq                                 27
% 3.45/0.99  fd_pure                                 0
% 3.45/0.99  fd_pseudo                               0
% 3.45/0.99  fd_cond                                 2
% 3.45/0.99  fd_pseudo_cond                          1
% 3.45/0.99  AC symbols                              0
% 3.45/0.99  
% 3.45/0.99  ------ Schedule dynamic 5 is on 
% 3.45/0.99  
% 3.45/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  ------ 
% 3.45/0.99  Current options:
% 3.45/0.99  ------ 
% 3.45/0.99  
% 3.45/0.99  ------ Input Options
% 3.45/0.99  
% 3.45/0.99  --out_options                           all
% 3.45/0.99  --tptp_safe_out                         true
% 3.45/0.99  --problem_path                          ""
% 3.45/0.99  --include_path                          ""
% 3.45/0.99  --clausifier                            res/vclausify_rel
% 3.45/0.99  --clausifier_options                    --mode clausify
% 3.45/0.99  --stdin                                 false
% 3.45/0.99  --stats_out                             all
% 3.45/0.99  
% 3.45/0.99  ------ General Options
% 3.45/0.99  
% 3.45/0.99  --fof                                   false
% 3.45/0.99  --time_out_real                         305.
% 3.45/0.99  --time_out_virtual                      -1.
% 3.45/0.99  --symbol_type_check                     false
% 3.45/0.99  --clausify_out                          false
% 3.45/0.99  --sig_cnt_out                           false
% 3.45/0.99  --trig_cnt_out                          false
% 3.45/0.99  --trig_cnt_out_tolerance                1.
% 3.45/0.99  --trig_cnt_out_sk_spl                   false
% 3.45/0.99  --abstr_cl_out                          false
% 3.45/0.99  
% 3.45/0.99  ------ Global Options
% 3.45/0.99  
% 3.45/0.99  --schedule                              default
% 3.45/0.99  --add_important_lit                     false
% 3.45/0.99  --prop_solver_per_cl                    1000
% 3.45/0.99  --min_unsat_core                        false
% 3.45/0.99  --soft_assumptions                      false
% 3.45/0.99  --soft_lemma_size                       3
% 3.45/0.99  --prop_impl_unit_size                   0
% 3.45/0.99  --prop_impl_unit                        []
% 3.45/0.99  --share_sel_clauses                     true
% 3.45/0.99  --reset_solvers                         false
% 3.45/0.99  --bc_imp_inh                            [conj_cone]
% 3.45/0.99  --conj_cone_tolerance                   3.
% 3.45/0.99  --extra_neg_conj                        none
% 3.45/0.99  --large_theory_mode                     true
% 3.45/0.99  --prolific_symb_bound                   200
% 3.45/0.99  --lt_threshold                          2000
% 3.45/0.99  --clause_weak_htbl                      true
% 3.45/0.99  --gc_record_bc_elim                     false
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing Options
% 3.45/0.99  
% 3.45/0.99  --preprocessing_flag                    true
% 3.45/0.99  --time_out_prep_mult                    0.1
% 3.45/0.99  --splitting_mode                        input
% 3.45/0.99  --splitting_grd                         true
% 3.45/0.99  --splitting_cvd                         false
% 3.45/0.99  --splitting_cvd_svl                     false
% 3.45/0.99  --splitting_nvd                         32
% 3.45/0.99  --sub_typing                            true
% 3.45/0.99  --prep_gs_sim                           true
% 3.45/0.99  --prep_unflatten                        true
% 3.45/0.99  --prep_res_sim                          true
% 3.45/0.99  --prep_upred                            true
% 3.45/0.99  --prep_sem_filter                       exhaustive
% 3.45/0.99  --prep_sem_filter_out                   false
% 3.45/0.99  --pred_elim                             true
% 3.45/0.99  --res_sim_input                         true
% 3.45/0.99  --eq_ax_congr_red                       true
% 3.45/0.99  --pure_diseq_elim                       true
% 3.45/0.99  --brand_transform                       false
% 3.45/0.99  --non_eq_to_eq                          false
% 3.45/0.99  --prep_def_merge                        true
% 3.45/0.99  --prep_def_merge_prop_impl              false
% 3.45/0.99  --prep_def_merge_mbd                    true
% 3.45/0.99  --prep_def_merge_tr_red                 false
% 3.45/0.99  --prep_def_merge_tr_cl                  false
% 3.45/0.99  --smt_preprocessing                     true
% 3.45/0.99  --smt_ac_axioms                         fast
% 3.45/0.99  --preprocessed_out                      false
% 3.45/0.99  --preprocessed_stats                    false
% 3.45/0.99  
% 3.45/0.99  ------ Abstraction refinement Options
% 3.45/0.99  
% 3.45/0.99  --abstr_ref                             []
% 3.45/0.99  --abstr_ref_prep                        false
% 3.45/0.99  --abstr_ref_until_sat                   false
% 3.45/0.99  --abstr_ref_sig_restrict                funpre
% 3.45/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/0.99  --abstr_ref_under                       []
% 3.45/0.99  
% 3.45/0.99  ------ SAT Options
% 3.45/0.99  
% 3.45/0.99  --sat_mode                              false
% 3.45/0.99  --sat_fm_restart_options                ""
% 3.45/0.99  --sat_gr_def                            false
% 3.45/0.99  --sat_epr_types                         true
% 3.45/0.99  --sat_non_cyclic_types                  false
% 3.45/0.99  --sat_finite_models                     false
% 3.45/0.99  --sat_fm_lemmas                         false
% 3.45/0.99  --sat_fm_prep                           false
% 3.45/0.99  --sat_fm_uc_incr                        true
% 3.45/0.99  --sat_out_model                         small
% 3.45/0.99  --sat_out_clauses                       false
% 3.45/0.99  
% 3.45/0.99  ------ QBF Options
% 3.45/0.99  
% 3.45/0.99  --qbf_mode                              false
% 3.45/0.99  --qbf_elim_univ                         false
% 3.45/0.99  --qbf_dom_inst                          none
% 3.45/0.99  --qbf_dom_pre_inst                      false
% 3.45/0.99  --qbf_sk_in                             false
% 3.45/0.99  --qbf_pred_elim                         true
% 3.45/0.99  --qbf_split                             512
% 3.45/0.99  
% 3.45/0.99  ------ BMC1 Options
% 3.45/0.99  
% 3.45/0.99  --bmc1_incremental                      false
% 3.45/0.99  --bmc1_axioms                           reachable_all
% 3.45/0.99  --bmc1_min_bound                        0
% 3.45/0.99  --bmc1_max_bound                        -1
% 3.45/0.99  --bmc1_max_bound_default                -1
% 3.45/0.99  --bmc1_symbol_reachability              true
% 3.45/0.99  --bmc1_property_lemmas                  false
% 3.45/0.99  --bmc1_k_induction                      false
% 3.45/0.99  --bmc1_non_equiv_states                 false
% 3.45/0.99  --bmc1_deadlock                         false
% 3.45/0.99  --bmc1_ucm                              false
% 3.45/0.99  --bmc1_add_unsat_core                   none
% 3.45/0.99  --bmc1_unsat_core_children              false
% 3.45/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/0.99  --bmc1_out_stat                         full
% 3.45/0.99  --bmc1_ground_init                      false
% 3.45/0.99  --bmc1_pre_inst_next_state              false
% 3.45/0.99  --bmc1_pre_inst_state                   false
% 3.45/0.99  --bmc1_pre_inst_reach_state             false
% 3.45/0.99  --bmc1_out_unsat_core                   false
% 3.45/0.99  --bmc1_aig_witness_out                  false
% 3.45/0.99  --bmc1_verbose                          false
% 3.45/0.99  --bmc1_dump_clauses_tptp                false
% 3.45/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.45/0.99  --bmc1_dump_file                        -
% 3.45/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.45/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.45/0.99  --bmc1_ucm_extend_mode                  1
% 3.45/0.99  --bmc1_ucm_init_mode                    2
% 3.45/0.99  --bmc1_ucm_cone_mode                    none
% 3.45/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.45/0.99  --bmc1_ucm_relax_model                  4
% 3.45/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.45/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/0.99  --bmc1_ucm_layered_model                none
% 3.45/0.99  --bmc1_ucm_max_lemma_size               10
% 3.45/0.99  
% 3.45/0.99  ------ AIG Options
% 3.45/0.99  
% 3.45/0.99  --aig_mode                              false
% 3.45/0.99  
% 3.45/0.99  ------ Instantiation Options
% 3.45/0.99  
% 3.45/0.99  --instantiation_flag                    true
% 3.45/0.99  --inst_sos_flag                         false
% 3.45/0.99  --inst_sos_phase                        true
% 3.45/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel_side                     none
% 3.45/0.99  --inst_solver_per_active                1400
% 3.45/0.99  --inst_solver_calls_frac                1.
% 3.45/0.99  --inst_passive_queue_type               priority_queues
% 3.45/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/0.99  --inst_passive_queues_freq              [25;2]
% 3.45/0.99  --inst_dismatching                      true
% 3.45/0.99  --inst_eager_unprocessed_to_passive     true
% 3.45/0.99  --inst_prop_sim_given                   true
% 3.45/0.99  --inst_prop_sim_new                     false
% 3.45/0.99  --inst_subs_new                         false
% 3.45/0.99  --inst_eq_res_simp                      false
% 3.45/0.99  --inst_subs_given                       false
% 3.45/0.99  --inst_orphan_elimination               true
% 3.45/0.99  --inst_learning_loop_flag               true
% 3.45/0.99  --inst_learning_start                   3000
% 3.45/0.99  --inst_learning_factor                  2
% 3.45/0.99  --inst_start_prop_sim_after_learn       3
% 3.45/0.99  --inst_sel_renew                        solver
% 3.45/0.99  --inst_lit_activity_flag                true
% 3.45/0.99  --inst_restr_to_given                   false
% 3.45/0.99  --inst_activity_threshold               500
% 3.45/0.99  --inst_out_proof                        true
% 3.45/0.99  
% 3.45/0.99  ------ Resolution Options
% 3.45/0.99  
% 3.45/0.99  --resolution_flag                       false
% 3.45/0.99  --res_lit_sel                           adaptive
% 3.45/0.99  --res_lit_sel_side                      none
% 3.45/0.99  --res_ordering                          kbo
% 3.45/0.99  --res_to_prop_solver                    active
% 3.45/0.99  --res_prop_simpl_new                    false
% 3.45/0.99  --res_prop_simpl_given                  true
% 3.45/0.99  --res_passive_queue_type                priority_queues
% 3.45/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/0.99  --res_passive_queues_freq               [15;5]
% 3.45/0.99  --res_forward_subs                      full
% 3.45/0.99  --res_backward_subs                     full
% 3.45/0.99  --res_forward_subs_resolution           true
% 3.45/0.99  --res_backward_subs_resolution          true
% 3.45/0.99  --res_orphan_elimination                true
% 3.45/0.99  --res_time_limit                        2.
% 3.45/0.99  --res_out_proof                         true
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Options
% 3.45/0.99  
% 3.45/0.99  --superposition_flag                    true
% 3.45/0.99  --sup_passive_queue_type                priority_queues
% 3.45/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.45/0.99  --demod_completeness_check              fast
% 3.45/0.99  --demod_use_ground                      true
% 3.45/0.99  --sup_to_prop_solver                    passive
% 3.45/0.99  --sup_prop_simpl_new                    true
% 3.45/0.99  --sup_prop_simpl_given                  true
% 3.45/0.99  --sup_fun_splitting                     false
% 3.45/0.99  --sup_smt_interval                      50000
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Simplification Setup
% 3.45/0.99  
% 3.45/0.99  --sup_indices_passive                   []
% 3.45/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_full_bw                           [BwDemod]
% 3.45/0.99  --sup_immed_triv                        [TrivRules]
% 3.45/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_immed_bw_main                     []
% 3.45/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/0.99  
% 3.45/0.99  ------ Combination Options
% 3.45/0.99  
% 3.45/0.99  --comb_res_mult                         3
% 3.45/0.99  --comb_sup_mult                         2
% 3.45/0.99  --comb_inst_mult                        10
% 3.45/0.99  
% 3.45/0.99  ------ Debug Options
% 3.45/0.99  
% 3.45/0.99  --dbg_backtrace                         false
% 3.45/0.99  --dbg_dump_prop_clauses                 false
% 3.45/0.99  --dbg_dump_prop_clauses_file            -
% 3.45/0.99  --dbg_out_stat                          false
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  ------ Proving...
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  % SZS status Theorem for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  fof(f1,axiom,(
% 3.45/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f26,plain,(
% 3.45/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.45/0.99    inference(ennf_transformation,[],[f1])).
% 3.45/0.99  
% 3.45/0.99  fof(f49,plain,(
% 3.45/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.45/0.99    inference(nnf_transformation,[],[f26])).
% 3.45/0.99  
% 3.45/0.99  fof(f50,plain,(
% 3.45/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.45/0.99    inference(rectify,[],[f49])).
% 3.45/0.99  
% 3.45/0.99  fof(f51,plain,(
% 3.45/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f52,plain,(
% 3.45/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).
% 3.45/0.99  
% 3.45/0.99  fof(f65,plain,(
% 3.45/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f52])).
% 3.45/0.99  
% 3.45/0.99  fof(f11,axiom,(
% 3.45/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f31,plain,(
% 3.45/0.99    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.45/0.99    inference(ennf_transformation,[],[f11])).
% 3.45/0.99  
% 3.45/0.99  fof(f55,plain,(
% 3.45/0.99    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 3.45/0.99    inference(nnf_transformation,[],[f31])).
% 3.45/0.99  
% 3.45/0.99  fof(f79,plain,(
% 3.45/0.99    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f55])).
% 3.45/0.99  
% 3.45/0.99  fof(f23,conjecture,(
% 3.45/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.45/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f24,negated_conjecture,(
% 3.45/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.45/0.99    inference(negated_conjecture,[],[f23])).
% 3.45/0.99  
% 3.45/0.99  fof(f47,plain,(
% 3.45/0.99    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.45/0.99    inference(ennf_transformation,[],[f24])).
% 3.45/0.99  
% 3.45/0.99  fof(f48,plain,(
% 3.45/0.99    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.45/1.00    inference(flattening,[],[f47])).
% 3.45/1.00  
% 3.45/1.00  fof(f62,plain,(
% 3.45/1.00    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5))),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f63,plain,(
% 3.45/1.00    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5)),
% 3.45/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f48,f62])).
% 3.45/1.00  
% 3.45/1.00  fof(f102,plain,(
% 3.45/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 3.45/1.00    inference(cnf_transformation,[],[f63])).
% 3.45/1.00  
% 3.45/1.00  fof(f4,axiom,(
% 3.45/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f71,plain,(
% 3.45/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f4])).
% 3.45/1.00  
% 3.45/1.00  fof(f5,axiom,(
% 3.45/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f72,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f5])).
% 3.45/1.00  
% 3.45/1.00  fof(f6,axiom,(
% 3.45/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f73,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f6])).
% 3.45/1.00  
% 3.45/1.00  fof(f105,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.45/1.00    inference(definition_unfolding,[],[f72,f73])).
% 3.45/1.00  
% 3.45/1.00  fof(f106,plain,(
% 3.45/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.45/1.00    inference(definition_unfolding,[],[f71,f105])).
% 3.45/1.00  
% 3.45/1.00  fof(f111,plain,(
% 3.45/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))),
% 3.45/1.00    inference(definition_unfolding,[],[f102,f106])).
% 3.45/1.00  
% 3.45/1.00  fof(f18,axiom,(
% 3.45/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f41,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.00    inference(ennf_transformation,[],[f18])).
% 3.45/1.00  
% 3.45/1.00  fof(f88,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f41])).
% 3.45/1.00  
% 3.45/1.00  fof(f9,axiom,(
% 3.45/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f29,plain,(
% 3.45/1.00    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.45/1.00    inference(ennf_transformation,[],[f9])).
% 3.45/1.00  
% 3.45/1.00  fof(f76,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f29])).
% 3.45/1.00  
% 3.45/1.00  fof(f107,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 3.45/1.00    inference(definition_unfolding,[],[f76,f106])).
% 3.45/1.00  
% 3.45/1.00  fof(f10,axiom,(
% 3.45/1.00    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f30,plain,(
% 3.45/1.00    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.45/1.00    inference(ennf_transformation,[],[f10])).
% 3.45/1.00  
% 3.45/1.00  fof(f77,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f30])).
% 3.45/1.00  
% 3.45/1.00  fof(f16,axiom,(
% 3.45/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f38,plain,(
% 3.45/1.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.45/1.00    inference(ennf_transformation,[],[f16])).
% 3.45/1.00  
% 3.45/1.00  fof(f39,plain,(
% 3.45/1.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.45/1.00    inference(flattening,[],[f38])).
% 3.45/1.00  
% 3.45/1.00  fof(f86,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f39])).
% 3.45/1.00  
% 3.45/1.00  fof(f109,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.45/1.00    inference(definition_unfolding,[],[f86,f106,f106])).
% 3.45/1.00  
% 3.45/1.00  fof(f100,plain,(
% 3.45/1.00    v1_funct_1(sK5)),
% 3.45/1.00    inference(cnf_transformation,[],[f63])).
% 3.45/1.00  
% 3.45/1.00  fof(f20,axiom,(
% 3.45/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f43,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.00    inference(ennf_transformation,[],[f20])).
% 3.45/1.00  
% 3.45/1.00  fof(f90,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f43])).
% 3.45/1.00  
% 3.45/1.00  fof(f104,plain,(
% 3.45/1.00    k1_tarski(k1_funct_1(sK5,sK3)) != k2_relset_1(k1_tarski(sK3),sK4,sK5)),
% 3.45/1.00    inference(cnf_transformation,[],[f63])).
% 3.45/1.00  
% 3.45/1.00  fof(f110,plain,(
% 3.45/1.00    k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5)),
% 3.45/1.00    inference(definition_unfolding,[],[f104,f106,f106])).
% 3.45/1.00  
% 3.45/1.00  fof(f19,axiom,(
% 3.45/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f25,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.45/1.00    inference(pure_predicate_removal,[],[f19])).
% 3.45/1.00  
% 3.45/1.00  fof(f42,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.00    inference(ennf_transformation,[],[f25])).
% 3.45/1.00  
% 3.45/1.00  fof(f89,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f42])).
% 3.45/1.00  
% 3.45/1.00  fof(f12,axiom,(
% 3.45/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f32,plain,(
% 3.45/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.45/1.00    inference(ennf_transformation,[],[f12])).
% 3.45/1.00  
% 3.45/1.00  fof(f33,plain,(
% 3.45/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.45/1.00    inference(flattening,[],[f32])).
% 3.45/1.00  
% 3.45/1.00  fof(f80,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f33])).
% 3.45/1.00  
% 3.45/1.00  fof(f14,axiom,(
% 3.45/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f34,plain,(
% 3.45/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.45/1.00    inference(ennf_transformation,[],[f14])).
% 3.45/1.00  
% 3.45/1.00  fof(f35,plain,(
% 3.45/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.45/1.00    inference(flattening,[],[f34])).
% 3.45/1.00  
% 3.45/1.00  fof(f84,plain,(
% 3.45/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f35])).
% 3.45/1.00  
% 3.45/1.00  fof(f22,axiom,(
% 3.45/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f45,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.00    inference(ennf_transformation,[],[f22])).
% 3.45/1.00  
% 3.45/1.00  fof(f46,plain,(
% 3.45/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.00    inference(flattening,[],[f45])).
% 3.45/1.00  
% 3.45/1.00  fof(f61,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.45/1.00    inference(nnf_transformation,[],[f46])).
% 3.45/1.00  
% 3.45/1.00  fof(f94,plain,(
% 3.45/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f61])).
% 3.45/1.00  
% 3.45/1.00  fof(f101,plain,(
% 3.45/1.00    v1_funct_2(sK5,k1_tarski(sK3),sK4)),
% 3.45/1.00    inference(cnf_transformation,[],[f63])).
% 3.45/1.00  
% 3.45/1.00  fof(f112,plain,(
% 3.45/1.00    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 3.45/1.00    inference(definition_unfolding,[],[f101,f106])).
% 3.45/1.00  
% 3.45/1.00  fof(f103,plain,(
% 3.45/1.00    k1_xboole_0 != sK4),
% 3.45/1.00    inference(cnf_transformation,[],[f63])).
% 3.45/1.00  
% 3.45/1.00  fof(f21,axiom,(
% 3.45/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f44,plain,(
% 3.45/1.00    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.45/1.00    inference(ennf_transformation,[],[f21])).
% 3.45/1.00  
% 3.45/1.00  fof(f56,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.45/1.00    inference(nnf_transformation,[],[f44])).
% 3.45/1.00  
% 3.45/1.00  fof(f57,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.45/1.00    inference(rectify,[],[f56])).
% 3.45/1.00  
% 3.45/1.00  fof(f59,plain,(
% 3.45/1.00    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f58,plain,(
% 3.45/1.00    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2))),
% 3.45/1.00    introduced(choice_axiom,[])).
% 3.45/1.00  
% 3.45/1.00  fof(f60,plain,(
% 3.45/1.00    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK2(X1,X2),X6),X2) & r2_hidden(sK2(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.45/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f57,f59,f58])).
% 3.45/1.00  
% 3.45/1.00  fof(f93,plain,(
% 3.45/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f60])).
% 3.45/1.00  
% 3.45/1.00  fof(f7,axiom,(
% 3.45/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f74,plain,(
% 3.45/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.45/1.00    inference(cnf_transformation,[],[f7])).
% 3.45/1.00  
% 3.45/1.00  fof(f13,axiom,(
% 3.45/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f82,plain,(
% 3.45/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.45/1.00    inference(cnf_transformation,[],[f13])).
% 3.45/1.00  
% 3.45/1.00  fof(f78,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f55])).
% 3.45/1.00  
% 3.45/1.00  fof(f81,plain,(
% 3.45/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.45/1.00    inference(cnf_transformation,[],[f13])).
% 3.45/1.00  
% 3.45/1.00  fof(f3,axiom,(
% 3.45/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f70,plain,(
% 3.45/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f3])).
% 3.45/1.00  
% 3.45/1.00  fof(f2,axiom,(
% 3.45/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f53,plain,(
% 3.45/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.45/1.00    inference(nnf_transformation,[],[f2])).
% 3.45/1.00  
% 3.45/1.00  fof(f54,plain,(
% 3.45/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.45/1.00    inference(flattening,[],[f53])).
% 3.45/1.00  
% 3.45/1.00  fof(f69,plain,(
% 3.45/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f54])).
% 3.45/1.00  
% 3.45/1.00  fof(f15,axiom,(
% 3.45/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.45/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.45/1.00  
% 3.45/1.00  fof(f36,plain,(
% 3.45/1.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.45/1.00    inference(ennf_transformation,[],[f15])).
% 3.45/1.00  
% 3.45/1.00  fof(f37,plain,(
% 3.45/1.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.45/1.00    inference(flattening,[],[f36])).
% 3.45/1.00  
% 3.45/1.00  fof(f85,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.45/1.00    inference(cnf_transformation,[],[f37])).
% 3.45/1.00  
% 3.45/1.00  fof(f108,plain,(
% 3.45/1.00    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.45/1.00    inference(definition_unfolding,[],[f85,f106,f106])).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1,plain,
% 3.45/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1427,plain,
% 3.45/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.45/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_11,plain,
% 3.45/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 3.45/1.00      | ~ v1_relat_1(X1)
% 3.45/1.00      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1418,plain,
% 3.45/1.00      ( k11_relat_1(X0,X1) = k1_xboole_0
% 3.45/1.00      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 3.45/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_35,negated_conjecture,
% 3.45/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
% 3.45/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1408,plain,
% 3.45/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_21,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | v1_relat_1(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1413,plain,
% 3.45/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.45/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1980,plain,
% 3.45/1.00      ( v1_relat_1(sK5) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1408,c_1413]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_9,plain,
% 3.45/1.00      ( ~ v1_relat_1(X0)
% 3.45/1.00      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1420,plain,
% 3.45/1.00      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 3.45/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3080,plain,
% 3.45/1.00      ( k9_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK5,X0) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1980,c_1420]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_10,plain,
% 3.45/1.00      ( ~ v1_relat_1(X0)
% 3.45/1.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.45/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1419,plain,
% 3.45/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.45/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2217,plain,
% 3.45/1.00      ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1980,c_1419]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_19,plain,
% 3.45/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.45/1.00      | ~ v1_funct_1(X1)
% 3.45/1.00      | ~ v1_relat_1(X1)
% 3.45/1.00      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))) ),
% 3.45/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_37,negated_conjecture,
% 3.45/1.00      ( v1_funct_1(sK5) ),
% 3.45/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_405,plain,
% 3.45/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.45/1.00      | ~ v1_relat_1(X1)
% 3.45/1.00      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0)))
% 3.45/1.00      | sK5 != X1 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_37]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_406,plain,
% 3.45/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 3.45/1.00      | ~ v1_relat_1(sK5)
% 3.45/1.00      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k2_enumset1(X0,X0,X0,X0))) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_405]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1406,plain,
% 3.45/1.00      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)))
% 3.45/1.00      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.45/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_40,plain,
% 3.45/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_407,plain,
% 3.45/1.00      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)))
% 3.45/1.00      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.45/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1639,plain,
% 3.45/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 3.45/1.00      | v1_relat_1(sK5) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1640,plain,
% 3.45/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
% 3.45/1.00      | v1_relat_1(sK5) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1639]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1693,plain,
% 3.45/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.45/1.00      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k2_enumset1(X0,X0,X0,X0))) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_1406,c_40,c_407,c_1640]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1694,plain,
% 3.45/1.00      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(k7_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)))
% 3.45/1.00      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_1693]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2565,plain,
% 3.45/1.00      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k9_relat_1(sK5,k2_enumset1(X0,X0,X0,X0))
% 3.45/1.00      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_2217,c_1694]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3194,plain,
% 3.45/1.00      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
% 3.45/1.00      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_3080,c_2565]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3799,plain,
% 3.45/1.00      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
% 3.45/1.00      | k11_relat_1(sK5,X0) = k1_xboole_0
% 3.45/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1418,c_3194]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8740,plain,
% 3.45/1.00      ( k11_relat_1(sK5,X0) = k1_xboole_0
% 3.45/1.00      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_3799,c_40,c_1640]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8741,plain,
% 3.45/1.00      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k11_relat_1(sK5,X0)
% 3.45/1.00      | k11_relat_1(sK5,X0) = k1_xboole_0 ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_8740]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_23,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1412,plain,
% 3.45/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.45/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2975,plain,
% 3.45/1.00      ( k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_relat_1(sK5) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1408,c_1412]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_33,negated_conjecture,
% 3.45/1.00      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) ),
% 3.45/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3089,plain,
% 3.45/1.00      ( k2_enumset1(k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3),k1_funct_1(sK5,sK3)) != k2_relat_1(sK5) ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_2975,c_33]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8747,plain,
% 3.45/1.00      ( k11_relat_1(sK5,sK3) != k2_relat_1(sK5)
% 3.45/1.00      | k11_relat_1(sK5,sK3) = k1_xboole_0 ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_8741,c_3089]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_22,plain,
% 3.45/1.00      ( v4_relat_1(X0,X1)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.45/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_13,plain,
% 3.45/1.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_385,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | ~ v1_relat_1(X0)
% 3.45/1.00      | k7_relat_1(X0,X1) = X0 ),
% 3.45/1.00      inference(resolution,[status(thm)],[c_22,c_13]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_389,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | k7_relat_1(X0,X1) = X0 ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_385,c_22,c_21,c_13]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1407,plain,
% 3.45/1.00      ( k7_relat_1(X0,X1) = X0
% 3.45/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1711,plain,
% 3.45/1.00      ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = sK5 ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1408,c_1407]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2569,plain,
% 3.45/1.00      ( k9_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k2_relat_1(sK5) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1711,c_2217]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3218,plain,
% 3.45/1.00      ( k11_relat_1(sK5,sK3) = k2_relat_1(sK5) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_2569,c_3080]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8750,plain,
% 3.45/1.00      ( k11_relat_1(sK5,sK3) = k1_xboole_0
% 3.45/1.00      | k2_relat_1(sK5) != k2_relat_1(sK5) ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_8747,c_3218]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_8751,plain,
% 3.45/1.00      ( k11_relat_1(sK5,sK3) = k1_xboole_0 ),
% 3.45/1.00      inference(equality_resolution_simp,[status(thm)],[c_8750]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_16,plain,
% 3.45/1.00      ( ~ v1_relat_1(X0)
% 3.45/1.00      | k2_relat_1(X0) != k1_xboole_0
% 3.45/1.00      | k1_xboole_0 = X0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1416,plain,
% 3.45/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 3.45/1.00      | k1_xboole_0 = X0
% 3.45/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2820,plain,
% 3.45/1.00      ( k7_relat_1(sK5,X0) = k1_xboole_0
% 3.45/1.00      | k9_relat_1(sK5,X0) != k1_xboole_0
% 3.45/1.00      | v1_relat_1(k7_relat_1(sK5,X0)) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_2217,c_1416]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3251,plain,
% 3.45/1.00      ( k7_relat_1(sK5,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0
% 3.45/1.00      | k11_relat_1(sK5,X0) != k1_xboole_0
% 3.45/1.00      | v1_relat_1(k7_relat_1(sK5,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_3080,c_2820]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_9475,plain,
% 3.45/1.00      ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k1_xboole_0
% 3.45/1.00      | v1_relat_1(k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3))) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_8751,c_3251]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_9478,plain,
% 3.45/1.00      ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k1_xboole_0
% 3.45/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_9475,c_1711]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_9479,plain,
% 3.45/1.00      ( sK5 = k1_xboole_0 | v1_relat_1(sK5) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_9478,c_1711]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3252,plain,
% 3.45/1.00      ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k1_xboole_0
% 3.45/1.00      | k2_relat_1(sK5) != k1_xboole_0
% 3.45/1.00      | v1_relat_1(k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3))) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_2569,c_2820]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3256,plain,
% 3.45/1.00      ( k7_relat_1(sK5,k2_enumset1(sK3,sK3,sK3,sK3)) = k1_xboole_0
% 3.45/1.00      | k2_relat_1(sK5) != k1_xboole_0
% 3.45/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_3252,c_1711]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3257,plain,
% 3.45/1.00      ( k2_relat_1(sK5) != k1_xboole_0
% 3.45/1.00      | sK5 = k1_xboole_0
% 3.45/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_3256,c_1711]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3390,plain,
% 3.45/1.00      ( sK5 = k1_xboole_0 | k2_relat_1(sK5) != k1_xboole_0 ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_3257,c_40,c_1640]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3391,plain,
% 3.45/1.00      ( k2_relat_1(sK5) != k1_xboole_0 | sK5 = k1_xboole_0 ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_3390]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_9472,plain,
% 3.45/1.00      ( k2_relat_1(sK5) = k1_xboole_0 ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_8751,c_3218]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_9556,plain,
% 3.45/1.00      ( sK5 = k1_xboole_0 ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_9479,c_3391,c_9472]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_32,plain,
% 3.45/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.45/1.00      | k1_xboole_0 = X2 ),
% 3.45/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_36,negated_conjecture,
% 3.45/1.00      ( v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 3.45/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_620,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | k2_enumset1(sK3,sK3,sK3,sK3) != X1
% 3.45/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.45/1.00      | sK4 != X2
% 3.45/1.00      | sK5 != X0
% 3.45/1.00      | k1_xboole_0 = X2 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_32,c_36]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_621,plain,
% 3.45/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))
% 3.45/1.00      | k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3)
% 3.45/1.00      | k1_xboole_0 = sK4 ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_620]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_34,negated_conjecture,
% 3.45/1.00      ( k1_xboole_0 != sK4 ),
% 3.45/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_623,plain,
% 3.45/1.00      ( k1_relset_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_621,c_35,c_34]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_24,plain,
% 3.45/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.45/1.00      | ~ r2_hidden(X3,X1)
% 3.45/1.00      | r2_hidden(k4_tarski(X3,sK1(X0,X3)),X0)
% 3.45/1.00      | k1_relset_1(X1,X2,X0) != X1 ),
% 3.45/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1411,plain,
% 3.45/1.00      ( k1_relset_1(X0,X1,X2) != X0
% 3.45/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.45/1.00      | r2_hidden(X3,X0) != iProver_top
% 3.45/1.00      | r2_hidden(k4_tarski(X3,sK1(X2,X3)),X2) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3688,plain,
% 3.45/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) != iProver_top
% 3.45/1.00      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 3.45/1.00      | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_623,c_1411]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4054,plain,
% 3.45/1.00      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 3.45/1.00      | r2_hidden(k4_tarski(X0,sK1(sK5,X0)),sK5) = iProver_top ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_3688,c_40]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_9606,plain,
% 3.45/1.00      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 3.45/1.00      | r2_hidden(k4_tarski(X0,sK1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_9556,c_4054]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_7,plain,
% 3.45/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.45/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1422,plain,
% 3.45/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1979,plain,
% 3.45/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1422,c_1413]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3079,plain,
% 3.45/1.00      ( k9_relat_1(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(k1_xboole_0,X0) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1979,c_1420]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2216,plain,
% 3.45/1.00      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1979,c_1419]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_14,plain,
% 3.45/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1910,plain,
% 3.45/1.00      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1422,c_1407]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_2221,plain,
% 3.45/1.00      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_2216,c_14,c_1910]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3084,plain,
% 3.45/1.00      ( k11_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_3079,c_2221]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_12,plain,
% 3.45/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.45/1.00      | ~ v1_relat_1(X1)
% 3.45/1.00      | k11_relat_1(X1,X0) != k1_xboole_0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1417,plain,
% 3.45/1.00      ( k11_relat_1(X0,X1) != k1_xboole_0
% 3.45/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.45/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4777,plain,
% 3.45/1.00      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 3.45/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_3084,c_1417]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_15,plain,
% 3.45/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4778,plain,
% 3.45/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.45/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_4777,c_15]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1631,plain,
% 3.45/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.45/1.00      | v1_relat_1(k1_xboole_0) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1633,plain,
% 3.45/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.45/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1631]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1632,plain,
% 3.45/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.45/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1635,plain,
% 3.45/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_1632]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_4922,plain,
% 3.45/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_4778,c_1633,c_1635]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_10172,plain,
% 3.45/1.00      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 3.45/1.00      inference(forward_subsumption_resolution,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_9606,c_4922]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_10176,plain,
% 3.45/1.00      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),X0) = iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1427,c_10172]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_6,plain,
% 3.45/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1423,plain,
% 3.45/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3,plain,
% 3.45/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.45/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1425,plain,
% 3.45/1.00      ( X0 = X1
% 3.45/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.45/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_3785,plain,
% 3.45/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_1423,c_1425]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_10398,plain,
% 3.45/1.00      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_10176,c_3785]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_18,plain,
% 3.45/1.00      ( ~ v1_funct_1(X0)
% 3.45/1.00      | ~ v1_relat_1(X0)
% 3.45/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.45/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 3.45/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_420,plain,
% 3.45/1.00      ( ~ v1_relat_1(X0)
% 3.45/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.45/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 3.45/1.00      | sK5 != X0 ),
% 3.45/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_37]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_421,plain,
% 3.45/1.00      ( ~ v1_relat_1(sK5)
% 3.45/1.00      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 3.45/1.00      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 3.45/1.00      inference(unflattening,[status(thm)],[c_420]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1405,plain,
% 3.45/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 3.45/1.00      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 3.45/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.45/1.00      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1669,plain,
% 3.45/1.00      ( k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5)
% 3.45/1.00      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5) ),
% 3.45/1.00      inference(global_propositional_subsumption,
% 3.45/1.00                [status(thm)],
% 3.45/1.00                [c_1405,c_35,c_421,c_1639]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_1670,plain,
% 3.45/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK5)
% 3.45/1.00      | k2_enumset1(k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0),k1_funct_1(sK5,X0)) = k2_relat_1(sK5) ),
% 3.45/1.00      inference(renaming,[status(thm)],[c_1669]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_9618,plain,
% 3.45/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(k1_xboole_0)
% 3.45/1.00      | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k2_relat_1(k1_xboole_0) ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_9556,c_1670]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_9633,plain,
% 3.45/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
% 3.45/1.00      | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_9618,c_14,c_15]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_10915,plain,
% 3.45/1.00      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) = k1_xboole_0 ),
% 3.45/1.00      inference(superposition,[status(thm)],[c_10398,c_9633]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_9612,plain,
% 3.45/1.00      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) != k2_relat_1(k1_xboole_0) ),
% 3.45/1.00      inference(demodulation,[status(thm)],[c_9556,c_3089]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(c_9642,plain,
% 3.45/1.00      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3),k1_funct_1(k1_xboole_0,sK3)) != k1_xboole_0 ),
% 3.45/1.00      inference(light_normalisation,[status(thm)],[c_9612,c_14]) ).
% 3.45/1.00  
% 3.45/1.00  cnf(contradiction,plain,
% 3.45/1.00      ( $false ),
% 3.45/1.00      inference(minisat,[status(thm)],[c_10915,c_9642]) ).
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/1.00  
% 3.45/1.00  ------                               Statistics
% 3.45/1.00  
% 3.45/1.00  ------ General
% 3.45/1.00  
% 3.45/1.00  abstr_ref_over_cycles:                  0
% 3.45/1.00  abstr_ref_under_cycles:                 0
% 3.45/1.00  gc_basic_clause_elim:                   0
% 3.45/1.00  forced_gc_time:                         0
% 3.45/1.00  parsing_time:                           0.011
% 3.45/1.00  unif_index_cands_time:                  0.
% 3.45/1.00  unif_index_add_time:                    0.
% 3.45/1.00  orderings_time:                         0.
% 3.45/1.00  out_proof_time:                         0.011
% 3.45/1.00  total_time:                             0.331
% 3.45/1.00  num_of_symbols:                         57
% 3.45/1.00  num_of_terms:                           9614
% 3.45/1.00  
% 3.45/1.00  ------ Preprocessing
% 3.45/1.00  
% 3.45/1.00  num_of_splits:                          0
% 3.45/1.00  num_of_split_atoms:                     0
% 3.45/1.00  num_of_reused_defs:                     0
% 3.45/1.00  num_eq_ax_congr_red:                    36
% 3.45/1.00  num_of_sem_filtered_clauses:            1
% 3.45/1.00  num_of_subtypes:                        0
% 3.45/1.00  monotx_restored_types:                  0
% 3.45/1.00  sat_num_of_epr_types:                   0
% 3.45/1.00  sat_num_of_non_cyclic_types:            0
% 3.45/1.00  sat_guarded_non_collapsed_types:        0
% 3.45/1.00  num_pure_diseq_elim:                    0
% 3.45/1.00  simp_replaced_by:                       0
% 3.45/1.00  res_preprocessed:                       165
% 3.45/1.00  prep_upred:                             0
% 3.45/1.00  prep_unflattend:                        37
% 3.45/1.00  smt_new_axioms:                         0
% 3.45/1.00  pred_elim_cands:                        4
% 3.45/1.00  pred_elim:                              3
% 3.45/1.00  pred_elim_cl:                           6
% 3.45/1.00  pred_elim_cycles:                       6
% 3.45/1.00  merged_defs:                            0
% 3.45/1.00  merged_defs_ncl:                        0
% 3.45/1.00  bin_hyper_res:                          0
% 3.45/1.00  prep_cycles:                            4
% 3.45/1.00  pred_elim_time:                         0.008
% 3.45/1.00  splitting_time:                         0.
% 3.45/1.00  sem_filter_time:                        0.
% 3.45/1.00  monotx_time:                            0.
% 3.45/1.00  subtype_inf_time:                       0.
% 3.45/1.00  
% 3.45/1.00  ------ Problem properties
% 3.45/1.00  
% 3.45/1.00  clauses:                                31
% 3.45/1.00  conjectures:                            3
% 3.45/1.00  epr:                                    6
% 3.45/1.00  horn:                                   27
% 3.45/1.00  ground:                                 8
% 3.45/1.00  unary:                                  9
% 3.45/1.00  binary:                                 8
% 3.45/1.00  lits:                                   69
% 3.45/1.00  lits_eq:                                27
% 3.45/1.00  fd_pure:                                0
% 3.45/1.00  fd_pseudo:                              0
% 3.45/1.00  fd_cond:                                2
% 3.45/1.00  fd_pseudo_cond:                         1
% 3.45/1.00  ac_symbols:                             0
% 3.45/1.00  
% 3.45/1.00  ------ Propositional Solver
% 3.45/1.00  
% 3.45/1.00  prop_solver_calls:                      28
% 3.45/1.00  prop_fast_solver_calls:                 1418
% 3.45/1.00  smt_solver_calls:                       0
% 3.45/1.00  smt_fast_solver_calls:                  0
% 3.45/1.00  prop_num_of_clauses:                    3833
% 3.45/1.00  prop_preprocess_simplified:             10646
% 3.45/1.00  prop_fo_subsumed:                       99
% 3.45/1.00  prop_solver_time:                       0.
% 3.45/1.00  smt_solver_time:                        0.
% 3.45/1.00  smt_fast_solver_time:                   0.
% 3.45/1.00  prop_fast_solver_time:                  0.
% 3.45/1.00  prop_unsat_core_time:                   0.
% 3.45/1.00  
% 3.45/1.00  ------ QBF
% 3.45/1.00  
% 3.45/1.00  qbf_q_res:                              0
% 3.45/1.00  qbf_num_tautologies:                    0
% 3.45/1.00  qbf_prep_cycles:                        0
% 3.45/1.00  
% 3.45/1.00  ------ BMC1
% 3.45/1.00  
% 3.45/1.00  bmc1_current_bound:                     -1
% 3.45/1.00  bmc1_last_solved_bound:                 -1
% 3.45/1.00  bmc1_unsat_core_size:                   -1
% 3.45/1.00  bmc1_unsat_core_parents_size:           -1
% 3.45/1.00  bmc1_merge_next_fun:                    0
% 3.45/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.45/1.00  
% 3.45/1.00  ------ Instantiation
% 3.45/1.00  
% 3.45/1.00  inst_num_of_clauses:                    1172
% 3.45/1.00  inst_num_in_passive:                    300
% 3.45/1.00  inst_num_in_active:                     513
% 3.45/1.00  inst_num_in_unprocessed:                359
% 3.45/1.00  inst_num_of_loops:                      650
% 3.45/1.00  inst_num_of_learning_restarts:          0
% 3.45/1.00  inst_num_moves_active_passive:          135
% 3.45/1.00  inst_lit_activity:                      0
% 3.45/1.00  inst_lit_activity_moves:                0
% 3.45/1.00  inst_num_tautologies:                   0
% 3.45/1.00  inst_num_prop_implied:                  0
% 3.45/1.00  inst_num_existing_simplified:           0
% 3.45/1.00  inst_num_eq_res_simplified:             0
% 3.45/1.00  inst_num_child_elim:                    0
% 3.45/1.00  inst_num_of_dismatching_blockings:      335
% 3.45/1.00  inst_num_of_non_proper_insts:           1090
% 3.45/1.00  inst_num_of_duplicates:                 0
% 3.45/1.00  inst_inst_num_from_inst_to_res:         0
% 3.45/1.00  inst_dismatching_checking_time:         0.
% 3.45/1.00  
% 3.45/1.00  ------ Resolution
% 3.45/1.00  
% 3.45/1.00  res_num_of_clauses:                     0
% 3.45/1.00  res_num_in_passive:                     0
% 3.45/1.00  res_num_in_active:                      0
% 3.45/1.00  res_num_of_loops:                       169
% 3.45/1.00  res_forward_subset_subsumed:            99
% 3.45/1.00  res_backward_subset_subsumed:           2
% 3.45/1.00  res_forward_subsumed:                   0
% 3.45/1.00  res_backward_subsumed:                  0
% 3.45/1.00  res_forward_subsumption_resolution:     0
% 3.45/1.00  res_backward_subsumption_resolution:    0
% 3.45/1.00  res_clause_to_clause_subsumption:       917
% 3.45/1.00  res_orphan_elimination:                 0
% 3.45/1.00  res_tautology_del:                      83
% 3.45/1.00  res_num_eq_res_simplified:              0
% 3.45/1.00  res_num_sel_changes:                    0
% 3.45/1.00  res_moves_from_active_to_pass:          0
% 3.45/1.00  
% 3.45/1.00  ------ Superposition
% 3.45/1.00  
% 3.45/1.00  sup_time_total:                         0.
% 3.45/1.00  sup_time_generating:                    0.
% 3.45/1.00  sup_time_sim_full:                      0.
% 3.45/1.00  sup_time_sim_immed:                     0.
% 3.45/1.00  
% 3.45/1.00  sup_num_of_clauses:                     107
% 3.45/1.00  sup_num_in_active:                      52
% 3.45/1.00  sup_num_in_passive:                     55
% 3.45/1.00  sup_num_of_loops:                       129
% 3.45/1.00  sup_fw_superposition:                   108
% 3.45/1.00  sup_bw_superposition:                   123
% 3.45/1.00  sup_immediate_simplified:               49
% 3.45/1.00  sup_given_eliminated:                   1
% 3.45/1.00  comparisons_done:                       0
% 3.45/1.00  comparisons_avoided:                    4
% 3.45/1.00  
% 3.45/1.00  ------ Simplifications
% 3.45/1.00  
% 3.45/1.00  
% 3.45/1.00  sim_fw_subset_subsumed:                 18
% 3.45/1.00  sim_bw_subset_subsumed:                 30
% 3.45/1.00  sim_fw_subsumed:                        23
% 3.45/1.00  sim_bw_subsumed:                        0
% 3.45/1.00  sim_fw_subsumption_res:                 8
% 3.45/1.00  sim_bw_subsumption_res:                 0
% 3.45/1.00  sim_tautology_del:                      1
% 3.45/1.00  sim_eq_tautology_del:                   11
% 3.45/1.00  sim_eq_res_simp:                        3
% 3.45/1.00  sim_fw_demodulated:                     15
% 3.45/1.00  sim_bw_demodulated:                     78
% 3.45/1.00  sim_light_normalised:                   30
% 3.45/1.00  sim_joinable_taut:                      0
% 3.45/1.00  sim_joinable_simp:                      0
% 3.45/1.00  sim_ac_normalised:                      0
% 3.45/1.00  sim_smt_subsumption:                    0
% 3.45/1.00  
%------------------------------------------------------------------------------
