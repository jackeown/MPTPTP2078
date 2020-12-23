%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:03 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 310 expanded)
%              Number of clauses        :   70 (  99 expanded)
%              Number of leaves         :   20 (  61 expanded)
%              Depth                    :   19
%              Number of atoms          :  469 (1084 expanded)
%              Number of equality atoms :  204 ( 367 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f49,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK5,sK4) != sK3
      & r2_hidden(sK4,sK2)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_2(sK5,sK2,k1_tarski(sK3))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( k1_funct_1(sK5,sK4) != sK3
    & r2_hidden(sK4,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f36,f49])).

fof(f85,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f50])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(nnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f99,plain,(
    v1_funct_2(sK5,sK2,k1_enumset1(sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f83,f87])).

fof(f84,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f98,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f84,f87])).

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

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f41])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f59,f64])).

fof(f103,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f95])).

fof(f104,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f103])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f53,f87])).

fof(f102,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f86,plain,(
    k1_funct_1(sK5,sK4) != sK3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1278,plain,
    ( r2_hidden(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK5,sK2,k1_enumset1(sK3,sK3,sK3)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_632,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_enumset1(sK3,sK3,sK3) != X2
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_633,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3))))
    | k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = sK2
    | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_635,plain,
    ( k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = sK2
    | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_633,c_31])).

cnf(c_1277,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1279,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2554,plain,
    ( k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1277,c_1279])).

cnf(c_3037,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k1_xboole_0
    | k1_relat_1(sK5) = sK2 ),
    inference(superposition,[status(thm)],[c_635,c_2554])).

cnf(c_9,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1284,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3107,plain,
    ( k1_relat_1(sK5) = sK2
    | r2_hidden(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3037,c_1284])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_528,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_529,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_1272,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_4512,plain,
    ( k1_relat_1(sK5) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3107,c_1272])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_457,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_33])).

cnf(c_458,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X3),k2_relat_1(sK5))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_458])).

cnf(c_498,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X2),k2_relat_1(sK5)) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_831,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_498])).

cnf(c_1276,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_36,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_833,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_498])).

cnf(c_864,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_868,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_832,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_498])).

cnf(c_1466,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3))))
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_1467,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1466])).

cnf(c_1587,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1276,c_36,c_864,c_868,c_1467])).

cnf(c_1588,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1587])).

cnf(c_4515,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4512,c_1588])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_259,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_260,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_259])).

cnf(c_21,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_17,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_21,c_17])).

cnf(c_480,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_20])).

cnf(c_481,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_480])).

cnf(c_558,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | X4 != X1
    | k2_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_260,c_481])).

cnf(c_559,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X2)) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_1269,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_559])).

cnf(c_1685,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k1_enumset1(sK3,sK3,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_1269])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1280,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2773,plain,
    ( m1_subset_1(X0,k1_enumset1(sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1685,c_1280])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1281,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3435,plain,
    ( r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | v1_xboole_0(k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2773,c_1281])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1292,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1789,plain,
    ( v1_xboole_0(k1_enumset1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_1292])).

cnf(c_5555,plain,
    ( r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3435,c_1789])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1288,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5561,plain,
    ( sK3 = X0
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5555,c_1288])).

cnf(c_6107,plain,
    ( k1_funct_1(sK5,X0) = sK3
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4515,c_5561])).

cnf(c_8902,plain,
    ( k1_funct_1(sK5,sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_1278,c_6107])).

cnf(c_29,negated_conjecture,
    ( k1_funct_1(sK5,sK4) != sK3 ),
    inference(cnf_transformation,[],[f86])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8902,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.29/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.00  
% 3.29/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.29/1.00  
% 3.29/1.00  ------  iProver source info
% 3.29/1.00  
% 3.29/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.29/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.29/1.00  git: non_committed_changes: false
% 3.29/1.00  git: last_make_outside_of_git: false
% 3.29/1.00  
% 3.29/1.00  ------ 
% 3.29/1.00  
% 3.29/1.00  ------ Input Options
% 3.29/1.00  
% 3.29/1.00  --out_options                           all
% 3.29/1.00  --tptp_safe_out                         true
% 3.29/1.00  --problem_path                          ""
% 3.29/1.00  --include_path                          ""
% 3.29/1.00  --clausifier                            res/vclausify_rel
% 3.29/1.00  --clausifier_options                    --mode clausify
% 3.29/1.00  --stdin                                 false
% 3.29/1.00  --stats_out                             all
% 3.29/1.00  
% 3.29/1.00  ------ General Options
% 3.29/1.00  
% 3.29/1.00  --fof                                   false
% 3.29/1.00  --time_out_real                         305.
% 3.29/1.00  --time_out_virtual                      -1.
% 3.29/1.00  --symbol_type_check                     false
% 3.29/1.00  --clausify_out                          false
% 3.29/1.00  --sig_cnt_out                           false
% 3.29/1.00  --trig_cnt_out                          false
% 3.29/1.00  --trig_cnt_out_tolerance                1.
% 3.29/1.00  --trig_cnt_out_sk_spl                   false
% 3.29/1.00  --abstr_cl_out                          false
% 3.29/1.00  
% 3.29/1.00  ------ Global Options
% 3.29/1.00  
% 3.29/1.00  --schedule                              default
% 3.29/1.00  --add_important_lit                     false
% 3.29/1.00  --prop_solver_per_cl                    1000
% 3.29/1.00  --min_unsat_core                        false
% 3.29/1.00  --soft_assumptions                      false
% 3.29/1.00  --soft_lemma_size                       3
% 3.29/1.00  --prop_impl_unit_size                   0
% 3.29/1.00  --prop_impl_unit                        []
% 3.29/1.00  --share_sel_clauses                     true
% 3.29/1.00  --reset_solvers                         false
% 3.29/1.00  --bc_imp_inh                            [conj_cone]
% 3.29/1.00  --conj_cone_tolerance                   3.
% 3.29/1.00  --extra_neg_conj                        none
% 3.29/1.00  --large_theory_mode                     true
% 3.29/1.00  --prolific_symb_bound                   200
% 3.29/1.00  --lt_threshold                          2000
% 3.29/1.00  --clause_weak_htbl                      true
% 3.29/1.00  --gc_record_bc_elim                     false
% 3.29/1.00  
% 3.29/1.00  ------ Preprocessing Options
% 3.29/1.00  
% 3.29/1.00  --preprocessing_flag                    true
% 3.29/1.00  --time_out_prep_mult                    0.1
% 3.29/1.00  --splitting_mode                        input
% 3.29/1.00  --splitting_grd                         true
% 3.29/1.00  --splitting_cvd                         false
% 3.29/1.00  --splitting_cvd_svl                     false
% 3.29/1.00  --splitting_nvd                         32
% 3.29/1.00  --sub_typing                            true
% 3.29/1.00  --prep_gs_sim                           true
% 3.29/1.00  --prep_unflatten                        true
% 3.29/1.00  --prep_res_sim                          true
% 3.29/1.00  --prep_upred                            true
% 3.29/1.00  --prep_sem_filter                       exhaustive
% 3.29/1.00  --prep_sem_filter_out                   false
% 3.29/1.00  --pred_elim                             true
% 3.29/1.00  --res_sim_input                         true
% 3.29/1.00  --eq_ax_congr_red                       true
% 3.29/1.00  --pure_diseq_elim                       true
% 3.29/1.00  --brand_transform                       false
% 3.29/1.00  --non_eq_to_eq                          false
% 3.29/1.00  --prep_def_merge                        true
% 3.29/1.00  --prep_def_merge_prop_impl              false
% 3.29/1.00  --prep_def_merge_mbd                    true
% 3.29/1.00  --prep_def_merge_tr_red                 false
% 3.29/1.00  --prep_def_merge_tr_cl                  false
% 3.29/1.00  --smt_preprocessing                     true
% 3.29/1.00  --smt_ac_axioms                         fast
% 3.29/1.00  --preprocessed_out                      false
% 3.29/1.00  --preprocessed_stats                    false
% 3.29/1.00  
% 3.29/1.00  ------ Abstraction refinement Options
% 3.29/1.00  
% 3.29/1.00  --abstr_ref                             []
% 3.29/1.00  --abstr_ref_prep                        false
% 3.29/1.00  --abstr_ref_until_sat                   false
% 3.29/1.00  --abstr_ref_sig_restrict                funpre
% 3.29/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.29/1.00  --abstr_ref_under                       []
% 3.29/1.00  
% 3.29/1.00  ------ SAT Options
% 3.29/1.00  
% 3.29/1.00  --sat_mode                              false
% 3.29/1.00  --sat_fm_restart_options                ""
% 3.29/1.00  --sat_gr_def                            false
% 3.29/1.00  --sat_epr_types                         true
% 3.29/1.00  --sat_non_cyclic_types                  false
% 3.29/1.00  --sat_finite_models                     false
% 3.29/1.00  --sat_fm_lemmas                         false
% 3.29/1.00  --sat_fm_prep                           false
% 3.29/1.00  --sat_fm_uc_incr                        true
% 3.29/1.00  --sat_out_model                         small
% 3.29/1.00  --sat_out_clauses                       false
% 3.29/1.00  
% 3.29/1.00  ------ QBF Options
% 3.29/1.00  
% 3.29/1.00  --qbf_mode                              false
% 3.29/1.00  --qbf_elim_univ                         false
% 3.29/1.00  --qbf_dom_inst                          none
% 3.29/1.00  --qbf_dom_pre_inst                      false
% 3.29/1.00  --qbf_sk_in                             false
% 3.29/1.00  --qbf_pred_elim                         true
% 3.29/1.00  --qbf_split                             512
% 3.29/1.00  
% 3.29/1.00  ------ BMC1 Options
% 3.29/1.00  
% 3.29/1.00  --bmc1_incremental                      false
% 3.29/1.00  --bmc1_axioms                           reachable_all
% 3.29/1.00  --bmc1_min_bound                        0
% 3.29/1.00  --bmc1_max_bound                        -1
% 3.29/1.00  --bmc1_max_bound_default                -1
% 3.29/1.00  --bmc1_symbol_reachability              true
% 3.29/1.00  --bmc1_property_lemmas                  false
% 3.29/1.00  --bmc1_k_induction                      false
% 3.29/1.00  --bmc1_non_equiv_states                 false
% 3.29/1.00  --bmc1_deadlock                         false
% 3.29/1.00  --bmc1_ucm                              false
% 3.29/1.00  --bmc1_add_unsat_core                   none
% 3.29/1.00  --bmc1_unsat_core_children              false
% 3.29/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.29/1.00  --bmc1_out_stat                         full
% 3.29/1.00  --bmc1_ground_init                      false
% 3.29/1.00  --bmc1_pre_inst_next_state              false
% 3.29/1.00  --bmc1_pre_inst_state                   false
% 3.29/1.00  --bmc1_pre_inst_reach_state             false
% 3.29/1.00  --bmc1_out_unsat_core                   false
% 3.29/1.00  --bmc1_aig_witness_out                  false
% 3.29/1.00  --bmc1_verbose                          false
% 3.29/1.00  --bmc1_dump_clauses_tptp                false
% 3.29/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.29/1.00  --bmc1_dump_file                        -
% 3.29/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.29/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.29/1.00  --bmc1_ucm_extend_mode                  1
% 3.29/1.00  --bmc1_ucm_init_mode                    2
% 3.29/1.00  --bmc1_ucm_cone_mode                    none
% 3.29/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.29/1.00  --bmc1_ucm_relax_model                  4
% 3.29/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.29/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.29/1.00  --bmc1_ucm_layered_model                none
% 3.29/1.00  --bmc1_ucm_max_lemma_size               10
% 3.29/1.00  
% 3.29/1.00  ------ AIG Options
% 3.29/1.00  
% 3.29/1.00  --aig_mode                              false
% 3.29/1.00  
% 3.29/1.00  ------ Instantiation Options
% 3.29/1.00  
% 3.29/1.00  --instantiation_flag                    true
% 3.29/1.00  --inst_sos_flag                         false
% 3.29/1.00  --inst_sos_phase                        true
% 3.29/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.29/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.29/1.00  --inst_lit_sel_side                     num_symb
% 3.29/1.00  --inst_solver_per_active                1400
% 3.29/1.00  --inst_solver_calls_frac                1.
% 3.29/1.00  --inst_passive_queue_type               priority_queues
% 3.29/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.29/1.00  --inst_passive_queues_freq              [25;2]
% 3.29/1.00  --inst_dismatching                      true
% 3.29/1.00  --inst_eager_unprocessed_to_passive     true
% 3.29/1.00  --inst_prop_sim_given                   true
% 3.29/1.00  --inst_prop_sim_new                     false
% 3.29/1.00  --inst_subs_new                         false
% 3.29/1.00  --inst_eq_res_simp                      false
% 3.29/1.00  --inst_subs_given                       false
% 3.29/1.00  --inst_orphan_elimination               true
% 3.29/1.00  --inst_learning_loop_flag               true
% 3.29/1.00  --inst_learning_start                   3000
% 3.29/1.00  --inst_learning_factor                  2
% 3.29/1.00  --inst_start_prop_sim_after_learn       3
% 3.29/1.00  --inst_sel_renew                        solver
% 3.29/1.00  --inst_lit_activity_flag                true
% 3.29/1.00  --inst_restr_to_given                   false
% 3.29/1.00  --inst_activity_threshold               500
% 3.29/1.00  --inst_out_proof                        true
% 3.29/1.00  
% 3.29/1.00  ------ Resolution Options
% 3.29/1.00  
% 3.29/1.00  --resolution_flag                       true
% 3.29/1.00  --res_lit_sel                           adaptive
% 3.29/1.00  --res_lit_sel_side                      none
% 3.29/1.00  --res_ordering                          kbo
% 3.29/1.00  --res_to_prop_solver                    active
% 3.29/1.00  --res_prop_simpl_new                    false
% 3.29/1.00  --res_prop_simpl_given                  true
% 3.29/1.00  --res_passive_queue_type                priority_queues
% 3.29/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.29/1.00  --res_passive_queues_freq               [15;5]
% 3.29/1.00  --res_forward_subs                      full
% 3.29/1.00  --res_backward_subs                     full
% 3.29/1.00  --res_forward_subs_resolution           true
% 3.29/1.00  --res_backward_subs_resolution          true
% 3.29/1.00  --res_orphan_elimination                true
% 3.29/1.00  --res_time_limit                        2.
% 3.29/1.00  --res_out_proof                         true
% 3.29/1.00  
% 3.29/1.00  ------ Superposition Options
% 3.29/1.00  
% 3.29/1.00  --superposition_flag                    true
% 3.29/1.00  --sup_passive_queue_type                priority_queues
% 3.29/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.29/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.29/1.00  --demod_completeness_check              fast
% 3.29/1.00  --demod_use_ground                      true
% 3.29/1.00  --sup_to_prop_solver                    passive
% 3.29/1.00  --sup_prop_simpl_new                    true
% 3.29/1.00  --sup_prop_simpl_given                  true
% 3.29/1.00  --sup_fun_splitting                     false
% 3.29/1.00  --sup_smt_interval                      50000
% 3.29/1.00  
% 3.29/1.00  ------ Superposition Simplification Setup
% 3.29/1.00  
% 3.29/1.00  --sup_indices_passive                   []
% 3.29/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.29/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.00  --sup_full_bw                           [BwDemod]
% 3.29/1.00  --sup_immed_triv                        [TrivRules]
% 3.29/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.00  --sup_immed_bw_main                     []
% 3.29/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.29/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/1.00  
% 3.29/1.00  ------ Combination Options
% 3.29/1.00  
% 3.29/1.00  --comb_res_mult                         3
% 3.29/1.00  --comb_sup_mult                         2
% 3.29/1.00  --comb_inst_mult                        10
% 3.29/1.00  
% 3.29/1.00  ------ Debug Options
% 3.29/1.00  
% 3.29/1.00  --dbg_backtrace                         false
% 3.29/1.00  --dbg_dump_prop_clauses                 false
% 3.29/1.00  --dbg_dump_prop_clauses_file            -
% 3.29/1.00  --dbg_out_stat                          false
% 3.29/1.00  ------ Parsing...
% 3.29/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.29/1.00  
% 3.29/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.29/1.00  
% 3.29/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.29/1.00  
% 3.29/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.29/1.00  ------ Proving...
% 3.29/1.00  ------ Problem Properties 
% 3.29/1.00  
% 3.29/1.00  
% 3.29/1.00  clauses                                 28
% 3.29/1.00  conjectures                             3
% 3.29/1.00  EPR                                     5
% 3.29/1.00  Horn                                    21
% 3.29/1.00  unary                                   8
% 3.29/1.00  binary                                  9
% 3.29/1.00  lits                                    61
% 3.29/1.00  lits eq                                 23
% 3.29/1.00  fd_pure                                 0
% 3.29/1.00  fd_pseudo                               0
% 3.29/1.00  fd_cond                                 0
% 3.29/1.00  fd_pseudo_cond                          5
% 3.29/1.00  AC symbols                              0
% 3.29/1.00  
% 3.29/1.00  ------ Schedule dynamic 5 is on 
% 3.29/1.00  
% 3.29/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.29/1.00  
% 3.29/1.00  
% 3.29/1.00  ------ 
% 3.29/1.00  Current options:
% 3.29/1.00  ------ 
% 3.29/1.00  
% 3.29/1.00  ------ Input Options
% 3.29/1.00  
% 3.29/1.00  --out_options                           all
% 3.29/1.00  --tptp_safe_out                         true
% 3.29/1.00  --problem_path                          ""
% 3.29/1.00  --include_path                          ""
% 3.29/1.00  --clausifier                            res/vclausify_rel
% 3.29/1.00  --clausifier_options                    --mode clausify
% 3.29/1.00  --stdin                                 false
% 3.29/1.00  --stats_out                             all
% 3.29/1.00  
% 3.29/1.00  ------ General Options
% 3.29/1.00  
% 3.29/1.00  --fof                                   false
% 3.29/1.00  --time_out_real                         305.
% 3.29/1.00  --time_out_virtual                      -1.
% 3.29/1.00  --symbol_type_check                     false
% 3.29/1.00  --clausify_out                          false
% 3.29/1.00  --sig_cnt_out                           false
% 3.29/1.00  --trig_cnt_out                          false
% 3.29/1.00  --trig_cnt_out_tolerance                1.
% 3.29/1.00  --trig_cnt_out_sk_spl                   false
% 3.29/1.00  --abstr_cl_out                          false
% 3.29/1.00  
% 3.29/1.00  ------ Global Options
% 3.29/1.00  
% 3.29/1.00  --schedule                              default
% 3.29/1.00  --add_important_lit                     false
% 3.29/1.00  --prop_solver_per_cl                    1000
% 3.29/1.00  --min_unsat_core                        false
% 3.29/1.00  --soft_assumptions                      false
% 3.29/1.00  --soft_lemma_size                       3
% 3.29/1.00  --prop_impl_unit_size                   0
% 3.29/1.00  --prop_impl_unit                        []
% 3.29/1.00  --share_sel_clauses                     true
% 3.29/1.00  --reset_solvers                         false
% 3.29/1.00  --bc_imp_inh                            [conj_cone]
% 3.29/1.00  --conj_cone_tolerance                   3.
% 3.29/1.00  --extra_neg_conj                        none
% 3.29/1.00  --large_theory_mode                     true
% 3.29/1.00  --prolific_symb_bound                   200
% 3.29/1.00  --lt_threshold                          2000
% 3.29/1.00  --clause_weak_htbl                      true
% 3.29/1.00  --gc_record_bc_elim                     false
% 3.29/1.00  
% 3.29/1.00  ------ Preprocessing Options
% 3.29/1.00  
% 3.29/1.00  --preprocessing_flag                    true
% 3.29/1.00  --time_out_prep_mult                    0.1
% 3.29/1.00  --splitting_mode                        input
% 3.29/1.00  --splitting_grd                         true
% 3.29/1.00  --splitting_cvd                         false
% 3.29/1.00  --splitting_cvd_svl                     false
% 3.29/1.00  --splitting_nvd                         32
% 3.29/1.00  --sub_typing                            true
% 3.29/1.00  --prep_gs_sim                           true
% 3.29/1.00  --prep_unflatten                        true
% 3.29/1.00  --prep_res_sim                          true
% 3.29/1.00  --prep_upred                            true
% 3.29/1.00  --prep_sem_filter                       exhaustive
% 3.29/1.00  --prep_sem_filter_out                   false
% 3.29/1.00  --pred_elim                             true
% 3.29/1.00  --res_sim_input                         true
% 3.29/1.00  --eq_ax_congr_red                       true
% 3.29/1.00  --pure_diseq_elim                       true
% 3.29/1.00  --brand_transform                       false
% 3.29/1.00  --non_eq_to_eq                          false
% 3.29/1.00  --prep_def_merge                        true
% 3.29/1.00  --prep_def_merge_prop_impl              false
% 3.29/1.00  --prep_def_merge_mbd                    true
% 3.29/1.00  --prep_def_merge_tr_red                 false
% 3.29/1.00  --prep_def_merge_tr_cl                  false
% 3.29/1.00  --smt_preprocessing                     true
% 3.29/1.00  --smt_ac_axioms                         fast
% 3.29/1.00  --preprocessed_out                      false
% 3.29/1.00  --preprocessed_stats                    false
% 3.29/1.00  
% 3.29/1.00  ------ Abstraction refinement Options
% 3.29/1.00  
% 3.29/1.00  --abstr_ref                             []
% 3.29/1.00  --abstr_ref_prep                        false
% 3.29/1.00  --abstr_ref_until_sat                   false
% 3.29/1.00  --abstr_ref_sig_restrict                funpre
% 3.29/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.29/1.00  --abstr_ref_under                       []
% 3.29/1.00  
% 3.29/1.00  ------ SAT Options
% 3.29/1.00  
% 3.29/1.00  --sat_mode                              false
% 3.29/1.00  --sat_fm_restart_options                ""
% 3.29/1.00  --sat_gr_def                            false
% 3.29/1.00  --sat_epr_types                         true
% 3.29/1.00  --sat_non_cyclic_types                  false
% 3.29/1.00  --sat_finite_models                     false
% 3.29/1.00  --sat_fm_lemmas                         false
% 3.29/1.00  --sat_fm_prep                           false
% 3.29/1.00  --sat_fm_uc_incr                        true
% 3.29/1.00  --sat_out_model                         small
% 3.29/1.00  --sat_out_clauses                       false
% 3.29/1.00  
% 3.29/1.00  ------ QBF Options
% 3.29/1.00  
% 3.29/1.00  --qbf_mode                              false
% 3.29/1.00  --qbf_elim_univ                         false
% 3.29/1.00  --qbf_dom_inst                          none
% 3.29/1.00  --qbf_dom_pre_inst                      false
% 3.29/1.00  --qbf_sk_in                             false
% 3.29/1.00  --qbf_pred_elim                         true
% 3.29/1.00  --qbf_split                             512
% 3.29/1.00  
% 3.29/1.00  ------ BMC1 Options
% 3.29/1.00  
% 3.29/1.00  --bmc1_incremental                      false
% 3.29/1.00  --bmc1_axioms                           reachable_all
% 3.29/1.00  --bmc1_min_bound                        0
% 3.29/1.00  --bmc1_max_bound                        -1
% 3.29/1.00  --bmc1_max_bound_default                -1
% 3.29/1.00  --bmc1_symbol_reachability              true
% 3.29/1.00  --bmc1_property_lemmas                  false
% 3.29/1.00  --bmc1_k_induction                      false
% 3.29/1.00  --bmc1_non_equiv_states                 false
% 3.29/1.00  --bmc1_deadlock                         false
% 3.29/1.00  --bmc1_ucm                              false
% 3.29/1.00  --bmc1_add_unsat_core                   none
% 3.29/1.00  --bmc1_unsat_core_children              false
% 3.29/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.29/1.00  --bmc1_out_stat                         full
% 3.29/1.00  --bmc1_ground_init                      false
% 3.29/1.00  --bmc1_pre_inst_next_state              false
% 3.29/1.00  --bmc1_pre_inst_state                   false
% 3.29/1.00  --bmc1_pre_inst_reach_state             false
% 3.29/1.00  --bmc1_out_unsat_core                   false
% 3.29/1.00  --bmc1_aig_witness_out                  false
% 3.29/1.00  --bmc1_verbose                          false
% 3.29/1.00  --bmc1_dump_clauses_tptp                false
% 3.29/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.29/1.00  --bmc1_dump_file                        -
% 3.29/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.29/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.29/1.00  --bmc1_ucm_extend_mode                  1
% 3.29/1.00  --bmc1_ucm_init_mode                    2
% 3.29/1.00  --bmc1_ucm_cone_mode                    none
% 3.29/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.29/1.00  --bmc1_ucm_relax_model                  4
% 3.29/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.29/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.29/1.00  --bmc1_ucm_layered_model                none
% 3.29/1.00  --bmc1_ucm_max_lemma_size               10
% 3.29/1.00  
% 3.29/1.00  ------ AIG Options
% 3.29/1.00  
% 3.29/1.00  --aig_mode                              false
% 3.29/1.00  
% 3.29/1.00  ------ Instantiation Options
% 3.29/1.00  
% 3.29/1.00  --instantiation_flag                    true
% 3.29/1.00  --inst_sos_flag                         false
% 3.29/1.00  --inst_sos_phase                        true
% 3.29/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.29/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.29/1.00  --inst_lit_sel_side                     none
% 3.29/1.00  --inst_solver_per_active                1400
% 3.29/1.00  --inst_solver_calls_frac                1.
% 3.29/1.00  --inst_passive_queue_type               priority_queues
% 3.29/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.29/1.00  --inst_passive_queues_freq              [25;2]
% 3.29/1.00  --inst_dismatching                      true
% 3.29/1.00  --inst_eager_unprocessed_to_passive     true
% 3.29/1.00  --inst_prop_sim_given                   true
% 3.29/1.00  --inst_prop_sim_new                     false
% 3.29/1.00  --inst_subs_new                         false
% 3.29/1.00  --inst_eq_res_simp                      false
% 3.29/1.00  --inst_subs_given                       false
% 3.29/1.00  --inst_orphan_elimination               true
% 3.29/1.00  --inst_learning_loop_flag               true
% 3.29/1.00  --inst_learning_start                   3000
% 3.29/1.00  --inst_learning_factor                  2
% 3.29/1.00  --inst_start_prop_sim_after_learn       3
% 3.29/1.00  --inst_sel_renew                        solver
% 3.29/1.00  --inst_lit_activity_flag                true
% 3.29/1.00  --inst_restr_to_given                   false
% 3.29/1.00  --inst_activity_threshold               500
% 3.29/1.00  --inst_out_proof                        true
% 3.29/1.00  
% 3.29/1.00  ------ Resolution Options
% 3.29/1.00  
% 3.29/1.00  --resolution_flag                       false
% 3.29/1.00  --res_lit_sel                           adaptive
% 3.29/1.00  --res_lit_sel_side                      none
% 3.29/1.00  --res_ordering                          kbo
% 3.29/1.00  --res_to_prop_solver                    active
% 3.29/1.00  --res_prop_simpl_new                    false
% 3.29/1.00  --res_prop_simpl_given                  true
% 3.29/1.00  --res_passive_queue_type                priority_queues
% 3.29/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.29/1.00  --res_passive_queues_freq               [15;5]
% 3.29/1.00  --res_forward_subs                      full
% 3.29/1.00  --res_backward_subs                     full
% 3.29/1.00  --res_forward_subs_resolution           true
% 3.29/1.00  --res_backward_subs_resolution          true
% 3.29/1.00  --res_orphan_elimination                true
% 3.29/1.00  --res_time_limit                        2.
% 3.29/1.00  --res_out_proof                         true
% 3.29/1.00  
% 3.29/1.00  ------ Superposition Options
% 3.29/1.00  
% 3.29/1.00  --superposition_flag                    true
% 3.29/1.00  --sup_passive_queue_type                priority_queues
% 3.29/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.29/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.29/1.00  --demod_completeness_check              fast
% 3.29/1.00  --demod_use_ground                      true
% 3.29/1.00  --sup_to_prop_solver                    passive
% 3.29/1.00  --sup_prop_simpl_new                    true
% 3.29/1.00  --sup_prop_simpl_given                  true
% 3.29/1.00  --sup_fun_splitting                     false
% 3.29/1.00  --sup_smt_interval                      50000
% 3.29/1.00  
% 3.29/1.00  ------ Superposition Simplification Setup
% 3.29/1.00  
% 3.29/1.00  --sup_indices_passive                   []
% 3.29/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.29/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.00  --sup_full_bw                           [BwDemod]
% 3.29/1.00  --sup_immed_triv                        [TrivRules]
% 3.29/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.00  --sup_immed_bw_main                     []
% 3.29/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.29/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/1.00  
% 3.29/1.00  ------ Combination Options
% 3.29/1.00  
% 3.29/1.00  --comb_res_mult                         3
% 3.29/1.00  --comb_sup_mult                         2
% 3.29/1.00  --comb_inst_mult                        10
% 3.29/1.00  
% 3.29/1.00  ------ Debug Options
% 3.29/1.00  
% 3.29/1.00  --dbg_backtrace                         false
% 3.29/1.00  --dbg_dump_prop_clauses                 false
% 3.29/1.00  --dbg_dump_prop_clauses_file            -
% 3.29/1.00  --dbg_out_stat                          false
% 3.29/1.00  
% 3.29/1.00  
% 3.29/1.00  
% 3.29/1.00  
% 3.29/1.00  ------ Proving...
% 3.29/1.00  
% 3.29/1.00  
% 3.29/1.00  % SZS status Theorem for theBenchmark.p
% 3.29/1.00  
% 3.29/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.29/1.00  
% 3.29/1.00  fof(f17,conjecture,(
% 3.29/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f18,negated_conjecture,(
% 3.29/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.29/1.00    inference(negated_conjecture,[],[f17])).
% 3.29/1.00  
% 3.29/1.00  fof(f35,plain,(
% 3.29/1.00    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 3.29/1.00    inference(ennf_transformation,[],[f18])).
% 3.29/1.00  
% 3.29/1.00  fof(f36,plain,(
% 3.29/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 3.29/1.00    inference(flattening,[],[f35])).
% 3.29/1.00  
% 3.29/1.00  fof(f49,plain,(
% 3.29/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK5,sK4) != sK3 & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5))),
% 3.29/1.00    introduced(choice_axiom,[])).
% 3.29/1.00  
% 3.29/1.00  fof(f50,plain,(
% 3.29/1.00    k1_funct_1(sK5,sK4) != sK3 & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5)),
% 3.29/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f36,f49])).
% 3.29/1.00  
% 3.29/1.00  fof(f85,plain,(
% 3.29/1.00    r2_hidden(sK4,sK2)),
% 3.29/1.00    inference(cnf_transformation,[],[f50])).
% 3.29/1.00  
% 3.29/1.00  fof(f16,axiom,(
% 3.29/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f33,plain,(
% 3.29/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/1.00    inference(ennf_transformation,[],[f16])).
% 3.29/1.00  
% 3.29/1.00  fof(f34,plain,(
% 3.29/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/1.00    inference(flattening,[],[f33])).
% 3.29/1.00  
% 3.29/1.00  fof(f48,plain,(
% 3.29/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/1.00    inference(nnf_transformation,[],[f34])).
% 3.29/1.00  
% 3.29/1.00  fof(f76,plain,(
% 3.29/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/1.00    inference(cnf_transformation,[],[f48])).
% 3.29/1.00  
% 3.29/1.00  fof(f83,plain,(
% 3.29/1.00    v1_funct_2(sK5,sK2,k1_tarski(sK3))),
% 3.29/1.00    inference(cnf_transformation,[],[f50])).
% 3.29/1.00  
% 3.29/1.00  fof(f5,axiom,(
% 3.29/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f63,plain,(
% 3.29/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.29/1.00    inference(cnf_transformation,[],[f5])).
% 3.29/1.00  
% 3.29/1.00  fof(f6,axiom,(
% 3.29/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f64,plain,(
% 3.29/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.29/1.00    inference(cnf_transformation,[],[f6])).
% 3.29/1.00  
% 3.29/1.00  fof(f87,plain,(
% 3.29/1.00    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.29/1.00    inference(definition_unfolding,[],[f63,f64])).
% 3.29/1.00  
% 3.29/1.00  fof(f99,plain,(
% 3.29/1.00    v1_funct_2(sK5,sK2,k1_enumset1(sK3,sK3,sK3))),
% 3.29/1.00    inference(definition_unfolding,[],[f83,f87])).
% 3.29/1.00  
% 3.29/1.00  fof(f84,plain,(
% 3.29/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 3.29/1.00    inference(cnf_transformation,[],[f50])).
% 3.29/1.00  
% 3.29/1.00  fof(f98,plain,(
% 3.29/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3))))),
% 3.29/1.00    inference(definition_unfolding,[],[f84,f87])).
% 3.29/1.00  
% 3.29/1.00  fof(f15,axiom,(
% 3.29/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f32,plain,(
% 3.29/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/1.00    inference(ennf_transformation,[],[f15])).
% 3.29/1.00  
% 3.29/1.00  fof(f75,plain,(
% 3.29/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/1.00    inference(cnf_transformation,[],[f32])).
% 3.29/1.00  
% 3.29/1.00  fof(f4,axiom,(
% 3.29/1.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f41,plain,(
% 3.29/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.29/1.00    inference(nnf_transformation,[],[f4])).
% 3.29/1.00  
% 3.29/1.00  fof(f42,plain,(
% 3.29/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.29/1.00    inference(flattening,[],[f41])).
% 3.29/1.00  
% 3.29/1.00  fof(f43,plain,(
% 3.29/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.29/1.00    inference(rectify,[],[f42])).
% 3.29/1.00  
% 3.29/1.00  fof(f44,plain,(
% 3.29/1.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.29/1.00    introduced(choice_axiom,[])).
% 3.29/1.00  
% 3.29/1.00  fof(f45,plain,(
% 3.29/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.29/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 3.29/1.00  
% 3.29/1.00  fof(f59,plain,(
% 3.29/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.29/1.00    inference(cnf_transformation,[],[f45])).
% 3.29/1.00  
% 3.29/1.00  fof(f95,plain,(
% 3.29/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 3.29/1.00    inference(definition_unfolding,[],[f59,f64])).
% 3.29/1.00  
% 3.29/1.00  fof(f103,plain,(
% 3.29/1.00    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 3.29/1.00    inference(equality_resolution,[],[f95])).
% 3.29/1.00  
% 3.29/1.00  fof(f104,plain,(
% 3.29/1.00    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 3.29/1.00    inference(equality_resolution,[],[f103])).
% 3.29/1.00  
% 3.29/1.00  fof(f2,axiom,(
% 3.29/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f52,plain,(
% 3.29/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.29/1.00    inference(cnf_transformation,[],[f2])).
% 3.29/1.00  
% 3.29/1.00  fof(f12,axiom,(
% 3.29/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f29,plain,(
% 3.29/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.29/1.00    inference(ennf_transformation,[],[f12])).
% 3.29/1.00  
% 3.29/1.00  fof(f72,plain,(
% 3.29/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.29/1.00    inference(cnf_transformation,[],[f29])).
% 3.29/1.00  
% 3.29/1.00  fof(f13,axiom,(
% 3.29/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f30,plain,(
% 3.29/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/1.00    inference(ennf_transformation,[],[f13])).
% 3.29/1.00  
% 3.29/1.00  fof(f73,plain,(
% 3.29/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/1.00    inference(cnf_transformation,[],[f30])).
% 3.29/1.00  
% 3.29/1.00  fof(f11,axiom,(
% 3.29/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f27,plain,(
% 3.29/1.00    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.29/1.00    inference(ennf_transformation,[],[f11])).
% 3.29/1.00  
% 3.29/1.00  fof(f28,plain,(
% 3.29/1.00    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.29/1.00    inference(flattening,[],[f27])).
% 3.29/1.00  
% 3.29/1.00  fof(f71,plain,(
% 3.29/1.00    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.29/1.00    inference(cnf_transformation,[],[f28])).
% 3.29/1.00  
% 3.29/1.00  fof(f82,plain,(
% 3.29/1.00    v1_funct_1(sK5)),
% 3.29/1.00    inference(cnf_transformation,[],[f50])).
% 3.29/1.00  
% 3.29/1.00  fof(f8,axiom,(
% 3.29/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f46,plain,(
% 3.29/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.29/1.00    inference(nnf_transformation,[],[f8])).
% 3.29/1.00  
% 3.29/1.00  fof(f67,plain,(
% 3.29/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.29/1.00    inference(cnf_transformation,[],[f46])).
% 3.29/1.00  
% 3.29/1.00  fof(f14,axiom,(
% 3.29/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f20,plain,(
% 3.29/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.29/1.00    inference(pure_predicate_removal,[],[f14])).
% 3.29/1.00  
% 3.29/1.00  fof(f31,plain,(
% 3.29/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/1.00    inference(ennf_transformation,[],[f20])).
% 3.29/1.00  
% 3.29/1.00  fof(f74,plain,(
% 3.29/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/1.00    inference(cnf_transformation,[],[f31])).
% 3.29/1.00  
% 3.29/1.00  fof(f10,axiom,(
% 3.29/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f26,plain,(
% 3.29/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.29/1.00    inference(ennf_transformation,[],[f10])).
% 3.29/1.00  
% 3.29/1.00  fof(f47,plain,(
% 3.29/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.29/1.00    inference(nnf_transformation,[],[f26])).
% 3.29/1.00  
% 3.29/1.00  fof(f69,plain,(
% 3.29/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.29/1.00    inference(cnf_transformation,[],[f47])).
% 3.29/1.00  
% 3.29/1.00  fof(f9,axiom,(
% 3.29/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f24,plain,(
% 3.29/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.29/1.00    inference(ennf_transformation,[],[f9])).
% 3.29/1.00  
% 3.29/1.00  fof(f25,plain,(
% 3.29/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.29/1.00    inference(flattening,[],[f24])).
% 3.29/1.00  
% 3.29/1.00  fof(f68,plain,(
% 3.29/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.29/1.00    inference(cnf_transformation,[],[f25])).
% 3.29/1.00  
% 3.29/1.00  fof(f7,axiom,(
% 3.29/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f22,plain,(
% 3.29/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.29/1.00    inference(ennf_transformation,[],[f7])).
% 3.29/1.00  
% 3.29/1.00  fof(f23,plain,(
% 3.29/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.29/1.00    inference(flattening,[],[f22])).
% 3.29/1.00  
% 3.29/1.00  fof(f65,plain,(
% 3.29/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.29/1.00    inference(cnf_transformation,[],[f23])).
% 3.29/1.00  
% 3.29/1.00  fof(f1,axiom,(
% 3.29/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f19,plain,(
% 3.29/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.29/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.29/1.00  
% 3.29/1.00  fof(f21,plain,(
% 3.29/1.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.29/1.00    inference(ennf_transformation,[],[f19])).
% 3.29/1.00  
% 3.29/1.00  fof(f51,plain,(
% 3.29/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.29/1.00    inference(cnf_transformation,[],[f21])).
% 3.29/1.00  
% 3.29/1.00  fof(f3,axiom,(
% 3.29/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.29/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.00  
% 3.29/1.00  fof(f37,plain,(
% 3.29/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.29/1.00    inference(nnf_transformation,[],[f3])).
% 3.29/1.00  
% 3.29/1.00  fof(f38,plain,(
% 3.29/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.29/1.00    inference(rectify,[],[f37])).
% 3.29/1.00  
% 3.29/1.00  fof(f39,plain,(
% 3.29/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.29/1.00    introduced(choice_axiom,[])).
% 3.29/1.00  
% 3.29/1.00  fof(f40,plain,(
% 3.29/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.29/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 3.29/1.00  
% 3.29/1.00  fof(f53,plain,(
% 3.29/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.29/1.00    inference(cnf_transformation,[],[f40])).
% 3.29/1.00  
% 3.29/1.00  fof(f91,plain,(
% 3.29/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 3.29/1.00    inference(definition_unfolding,[],[f53,f87])).
% 3.29/1.00  
% 3.29/1.00  fof(f102,plain,(
% 3.29/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 3.29/1.00    inference(equality_resolution,[],[f91])).
% 3.29/1.00  
% 3.29/1.00  fof(f86,plain,(
% 3.29/1.00    k1_funct_1(sK5,sK4) != sK3),
% 3.29/1.00    inference(cnf_transformation,[],[f50])).
% 3.29/1.00  
% 3.29/1.00  cnf(c_30,negated_conjecture,
% 3.29/1.00      ( r2_hidden(sK4,sK2) ),
% 3.29/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1278,plain,
% 3.29/1.00      ( r2_hidden(sK4,sK2) = iProver_top ),
% 3.29/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_28,plain,
% 3.29/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.29/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.29/1.00      | k1_xboole_0 = X2 ),
% 3.29/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_32,negated_conjecture,
% 3.29/1.00      ( v1_funct_2(sK5,sK2,k1_enumset1(sK3,sK3,sK3)) ),
% 3.29/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_632,plain,
% 3.29/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.29/1.00      | k1_enumset1(sK3,sK3,sK3) != X2
% 3.29/1.00      | sK2 != X1
% 3.29/1.00      | sK5 != X0
% 3.29/1.00      | k1_xboole_0 = X2 ),
% 3.29/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_633,plain,
% 3.29/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3))))
% 3.29/1.00      | k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = sK2
% 3.29/1.00      | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) ),
% 3.29/1.00      inference(unflattening,[status(thm)],[c_632]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_31,negated_conjecture,
% 3.29/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) ),
% 3.29/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_635,plain,
% 3.29/1.00      ( k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = sK2
% 3.29/1.00      | k1_xboole_0 = k1_enumset1(sK3,sK3,sK3) ),
% 3.29/1.00      inference(global_propositional_subsumption,
% 3.29/1.00                [status(thm)],
% 3.29/1.00                [c_633,c_31]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1277,plain,
% 3.29/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) = iProver_top ),
% 3.29/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_22,plain,
% 3.29/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.29/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1279,plain,
% 3.29/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.29/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.29/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_2554,plain,
% 3.29/1.00      ( k1_relset_1(sK2,k1_enumset1(sK3,sK3,sK3),sK5) = k1_relat_1(sK5) ),
% 3.29/1.00      inference(superposition,[status(thm)],[c_1277,c_1279]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_3037,plain,
% 3.29/1.00      ( k1_enumset1(sK3,sK3,sK3) = k1_xboole_0 | k1_relat_1(sK5) = sK2 ),
% 3.29/1.00      inference(superposition,[status(thm)],[c_635,c_2554]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_9,plain,
% 3.29/1.00      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
% 3.29/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1284,plain,
% 3.29/1.00      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
% 3.29/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_3107,plain,
% 3.29/1.00      ( k1_relat_1(sK5) = sK2
% 3.29/1.00      | r2_hidden(sK3,k1_xboole_0) = iProver_top ),
% 3.29/1.00      inference(superposition,[status(thm)],[c_3037,c_1284]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1,plain,
% 3.29/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.29/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_19,plain,
% 3.29/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.29/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_528,plain,
% 3.29/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.29/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_19]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_529,plain,
% 3.29/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.29/1.00      inference(unflattening,[status(thm)],[c_528]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1272,plain,
% 3.29/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.29/1.00      inference(predicate_to_equality,[status(thm)],[c_529]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_4512,plain,
% 3.29/1.00      ( k1_relat_1(sK5) = sK2 ),
% 3.29/1.00      inference(forward_subsumption_resolution,
% 3.29/1.00                [status(thm)],
% 3.29/1.00                [c_3107,c_1272]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_20,plain,
% 3.29/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/1.00      | v1_relat_1(X0) ),
% 3.29/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_18,plain,
% 3.29/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.29/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.29/1.00      | ~ v1_funct_1(X1)
% 3.29/1.00      | ~ v1_relat_1(X1) ),
% 3.29/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_33,negated_conjecture,
% 3.29/1.00      ( v1_funct_1(sK5) ),
% 3.29/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_457,plain,
% 3.29/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.29/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.29/1.00      | ~ v1_relat_1(X1)
% 3.29/1.00      | sK5 != X1 ),
% 3.29/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_33]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_458,plain,
% 3.29/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 3.29/1.00      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
% 3.29/1.00      | ~ v1_relat_1(sK5) ),
% 3.29/1.00      inference(unflattening,[status(thm)],[c_457]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_497,plain,
% 3.29/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/1.00      | ~ r2_hidden(X3,k1_relat_1(sK5))
% 3.29/1.00      | r2_hidden(k1_funct_1(sK5,X3),k2_relat_1(sK5))
% 3.29/1.00      | sK5 != X0 ),
% 3.29/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_458]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_498,plain,
% 3.29/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.29/1.00      | ~ r2_hidden(X2,k1_relat_1(sK5))
% 3.29/1.00      | r2_hidden(k1_funct_1(sK5,X2),k2_relat_1(sK5)) ),
% 3.29/1.00      inference(unflattening,[status(thm)],[c_497]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_831,plain,
% 3.29/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 3.29/1.00      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
% 3.29/1.00      | ~ sP0_iProver_split ),
% 3.29/1.00      inference(splitting,
% 3.29/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.29/1.00                [c_498]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1276,plain,
% 3.29/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.29/1.00      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 3.29/1.00      | sP0_iProver_split != iProver_top ),
% 3.29/1.00      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_36,plain,
% 3.29/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) = iProver_top ),
% 3.29/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_833,plain,
% 3.29/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 3.29/1.00      inference(splitting,
% 3.29/1.00                [splitting(split),new_symbols(definition,[])],
% 3.29/1.00                [c_498]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_864,plain,
% 3.29/1.00      ( sP1_iProver_split = iProver_top
% 3.29/1.00      | sP0_iProver_split = iProver_top ),
% 3.29/1.00      inference(predicate_to_equality,[status(thm)],[c_833]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_868,plain,
% 3.29/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.29/1.00      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 3.29/1.00      | sP0_iProver_split != iProver_top ),
% 3.29/1.00      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_832,plain,
% 3.29/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.29/1.00      | ~ sP1_iProver_split ),
% 3.29/1.00      inference(splitting,
% 3.29/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.29/1.00                [c_498]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1466,plain,
% 3.29/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3))))
% 3.29/1.00      | ~ sP1_iProver_split ),
% 3.29/1.00      inference(instantiation,[status(thm)],[c_832]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1467,plain,
% 3.29/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))) != iProver_top
% 3.29/1.00      | sP1_iProver_split != iProver_top ),
% 3.29/1.00      inference(predicate_to_equality,[status(thm)],[c_1466]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1587,plain,
% 3.29/1.00      ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 3.29/1.00      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 3.29/1.00      inference(global_propositional_subsumption,
% 3.29/1.00                [status(thm)],
% 3.29/1.00                [c_1276,c_36,c_864,c_868,c_1467]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1588,plain,
% 3.29/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.29/1.00      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
% 3.29/1.00      inference(renaming,[status(thm)],[c_1587]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_4515,plain,
% 3.29/1.00      ( r2_hidden(X0,sK2) != iProver_top
% 3.29/1.00      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
% 3.29/1.00      inference(demodulation,[status(thm)],[c_4512,c_1588]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_13,plain,
% 3.29/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.29/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_259,plain,
% 3.29/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.29/1.00      inference(prop_impl,[status(thm)],[c_13]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_260,plain,
% 3.29/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.29/1.00      inference(renaming,[status(thm)],[c_259]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_21,plain,
% 3.29/1.00      ( v5_relat_1(X0,X1)
% 3.29/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.29/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_17,plain,
% 3.29/1.00      ( ~ v5_relat_1(X0,X1)
% 3.29/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.29/1.00      | ~ v1_relat_1(X0) ),
% 3.29/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_476,plain,
% 3.29/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 3.29/1.00      | ~ v1_relat_1(X0) ),
% 3.29/1.00      inference(resolution,[status(thm)],[c_21,c_17]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_480,plain,
% 3.29/1.00      ( r1_tarski(k2_relat_1(X0),X2)
% 3.29/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.29/1.00      inference(global_propositional_subsumption,
% 3.29/1.00                [status(thm)],
% 3.29/1.00                [c_476,c_20]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_481,plain,
% 3.29/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/1.00      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.29/1.00      inference(renaming,[status(thm)],[c_480]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_558,plain,
% 3.29/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.29/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.29/1.00      | X4 != X1
% 3.29/1.00      | k2_relat_1(X2) != X0 ),
% 3.29/1.00      inference(resolution_lifted,[status(thm)],[c_260,c_481]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_559,plain,
% 3.29/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/1.00      | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X2)) ),
% 3.29/1.00      inference(unflattening,[status(thm)],[c_558]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1269,plain,
% 3.29/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.29/1.00      | m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.29/1.00      inference(predicate_to_equality,[status(thm)],[c_559]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1685,plain,
% 3.29/1.00      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(k1_enumset1(sK3,sK3,sK3))) = iProver_top ),
% 3.29/1.00      inference(superposition,[status(thm)],[c_1277,c_1269]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_15,plain,
% 3.29/1.00      ( m1_subset_1(X0,X1)
% 3.29/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.29/1.00      | ~ r2_hidden(X0,X2) ),
% 3.29/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1280,plain,
% 3.29/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.29/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.29/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 3.29/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_2773,plain,
% 3.29/1.00      ( m1_subset_1(X0,k1_enumset1(sK3,sK3,sK3)) = iProver_top
% 3.29/1.00      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 3.29/1.00      inference(superposition,[status(thm)],[c_1685,c_1280]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_12,plain,
% 3.29/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.29/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1281,plain,
% 3.29/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.29/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.29/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.29/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_3435,plain,
% 3.29/1.00      ( r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) = iProver_top
% 3.29/1.00      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 3.29/1.00      | v1_xboole_0(k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
% 3.29/1.00      inference(superposition,[status(thm)],[c_2773,c_1281]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_0,plain,
% 3.29/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.29/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1292,plain,
% 3.29/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.29/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.29/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1789,plain,
% 3.29/1.00      ( v1_xboole_0(k1_enumset1(X0,X0,X1)) != iProver_top ),
% 3.29/1.00      inference(superposition,[status(thm)],[c_1284,c_1292]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_5555,plain,
% 3.29/1.00      ( r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) = iProver_top
% 3.29/1.00      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 3.29/1.00      inference(forward_subsumption_resolution,
% 3.29/1.00                [status(thm)],
% 3.29/1.00                [c_3435,c_1789]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_5,plain,
% 3.29/1.00      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 3.29/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_1288,plain,
% 3.29/1.00      ( X0 = X1 | r2_hidden(X0,k1_enumset1(X1,X1,X1)) != iProver_top ),
% 3.29/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_5561,plain,
% 3.29/1.00      ( sK3 = X0 | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 3.29/1.00      inference(superposition,[status(thm)],[c_5555,c_1288]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_6107,plain,
% 3.29/1.00      ( k1_funct_1(sK5,X0) = sK3 | r2_hidden(X0,sK2) != iProver_top ),
% 3.29/1.00      inference(superposition,[status(thm)],[c_4515,c_5561]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_8902,plain,
% 3.29/1.00      ( k1_funct_1(sK5,sK4) = sK3 ),
% 3.29/1.00      inference(superposition,[status(thm)],[c_1278,c_6107]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(c_29,negated_conjecture,
% 3.29/1.00      ( k1_funct_1(sK5,sK4) != sK3 ),
% 3.29/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.29/1.00  
% 3.29/1.00  cnf(contradiction,plain,
% 3.29/1.00      ( $false ),
% 3.29/1.00      inference(minisat,[status(thm)],[c_8902,c_29]) ).
% 3.29/1.00  
% 3.29/1.00  
% 3.29/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.29/1.00  
% 3.29/1.00  ------                               Statistics
% 3.29/1.00  
% 3.29/1.00  ------ General
% 3.29/1.00  
% 3.29/1.00  abstr_ref_over_cycles:                  0
% 3.29/1.00  abstr_ref_under_cycles:                 0
% 3.29/1.00  gc_basic_clause_elim:                   0
% 3.29/1.00  forced_gc_time:                         0
% 3.29/1.00  parsing_time:                           0.008
% 3.29/1.00  unif_index_cands_time:                  0.
% 3.29/1.00  unif_index_add_time:                    0.
% 3.29/1.00  orderings_time:                         0.
% 3.29/1.00  out_proof_time:                         0.009
% 3.29/1.00  total_time:                             0.284
% 3.29/1.00  num_of_symbols:                         55
% 3.29/1.00  num_of_terms:                           10822
% 3.29/1.00  
% 3.29/1.00  ------ Preprocessing
% 3.29/1.00  
% 3.29/1.00  num_of_splits:                          2
% 3.29/1.00  num_of_split_atoms:                     2
% 3.29/1.00  num_of_reused_defs:                     0
% 3.29/1.00  num_eq_ax_congr_red:                    26
% 3.29/1.00  num_of_sem_filtered_clauses:            1
% 3.29/1.00  num_of_subtypes:                        0
% 3.29/1.00  monotx_restored_types:                  0
% 3.29/1.00  sat_num_of_epr_types:                   0
% 3.29/1.00  sat_num_of_non_cyclic_types:            0
% 3.29/1.00  sat_guarded_non_collapsed_types:        0
% 3.29/1.00  num_pure_diseq_elim:                    0
% 3.29/1.00  simp_replaced_by:                       0
% 3.29/1.00  res_preprocessed:                       139
% 3.29/1.00  prep_upred:                             0
% 3.29/1.00  prep_unflattend:                        37
% 3.29/1.00  smt_new_axioms:                         0
% 3.29/1.00  pred_elim_cands:                        3
% 3.29/1.00  pred_elim:                              5
% 3.29/1.00  pred_elim_cl:                           8
% 3.29/1.00  pred_elim_cycles:                       8
% 3.29/1.00  merged_defs:                            2
% 3.29/1.00  merged_defs_ncl:                        0
% 3.29/1.00  bin_hyper_res:                          2
% 3.29/1.00  prep_cycles:                            4
% 3.29/1.00  pred_elim_time:                         0.003
% 3.29/1.00  splitting_time:                         0.
% 3.29/1.00  sem_filter_time:                        0.
% 3.29/1.00  monotx_time:                            0.001
% 3.29/1.00  subtype_inf_time:                       0.
% 3.29/1.00  
% 3.29/1.00  ------ Problem properties
% 3.29/1.00  
% 3.29/1.00  clauses:                                28
% 3.29/1.00  conjectures:                            3
% 3.29/1.00  epr:                                    5
% 3.29/1.00  horn:                                   21
% 3.29/1.00  ground:                                 7
% 3.29/1.00  unary:                                  8
% 3.29/1.00  binary:                                 9
% 3.29/1.00  lits:                                   61
% 3.29/1.00  lits_eq:                                23
% 3.29/1.00  fd_pure:                                0
% 3.29/1.00  fd_pseudo:                              0
% 3.29/1.00  fd_cond:                                0
% 3.29/1.00  fd_pseudo_cond:                         5
% 3.29/1.00  ac_symbols:                             0
% 3.29/1.00  
% 3.29/1.00  ------ Propositional Solver
% 3.29/1.00  
% 3.29/1.00  prop_solver_calls:                      27
% 3.29/1.00  prop_fast_solver_calls:                 857
% 3.29/1.00  smt_solver_calls:                       0
% 3.29/1.00  smt_fast_solver_calls:                  0
% 3.29/1.00  prop_num_of_clauses:                    3435
% 3.29/1.00  prop_preprocess_simplified:             10140
% 3.29/1.00  prop_fo_subsumed:                       8
% 3.29/1.00  prop_solver_time:                       0.
% 3.29/1.00  smt_solver_time:                        0.
% 3.29/1.00  smt_fast_solver_time:                   0.
% 3.29/1.00  prop_fast_solver_time:                  0.
% 3.29/1.00  prop_unsat_core_time:                   0.
% 3.29/1.00  
% 3.29/1.00  ------ QBF
% 3.29/1.00  
% 3.29/1.00  qbf_q_res:                              0
% 3.29/1.00  qbf_num_tautologies:                    0
% 3.29/1.00  qbf_prep_cycles:                        0
% 3.29/1.00  
% 3.29/1.00  ------ BMC1
% 3.29/1.00  
% 3.29/1.00  bmc1_current_bound:                     -1
% 3.29/1.00  bmc1_last_solved_bound:                 -1
% 3.29/1.00  bmc1_unsat_core_size:                   -1
% 3.29/1.00  bmc1_unsat_core_parents_size:           -1
% 3.29/1.00  bmc1_merge_next_fun:                    0
% 3.29/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.29/1.00  
% 3.29/1.00  ------ Instantiation
% 3.29/1.00  
% 3.29/1.00  inst_num_of_clauses:                    1030
% 3.29/1.00  inst_num_in_passive:                    486
% 3.29/1.00  inst_num_in_active:                     312
% 3.29/1.00  inst_num_in_unprocessed:                232
% 3.29/1.00  inst_num_of_loops:                      350
% 3.29/1.00  inst_num_of_learning_restarts:          0
% 3.29/1.00  inst_num_moves_active_passive:          37
% 3.29/1.00  inst_lit_activity:                      0
% 3.29/1.00  inst_lit_activity_moves:                0
% 3.29/1.00  inst_num_tautologies:                   0
% 3.29/1.00  inst_num_prop_implied:                  0
% 3.29/1.00  inst_num_existing_simplified:           0
% 3.29/1.00  inst_num_eq_res_simplified:             0
% 3.29/1.00  inst_num_child_elim:                    0
% 3.29/1.00  inst_num_of_dismatching_blockings:      770
% 3.29/1.00  inst_num_of_non_proper_insts:           764
% 3.29/1.00  inst_num_of_duplicates:                 0
% 3.29/1.00  inst_inst_num_from_inst_to_res:         0
% 3.29/1.00  inst_dismatching_checking_time:         0.
% 3.29/1.00  
% 3.29/1.00  ------ Resolution
% 3.29/1.00  
% 3.29/1.00  res_num_of_clauses:                     0
% 3.29/1.00  res_num_in_passive:                     0
% 3.29/1.00  res_num_in_active:                      0
% 3.29/1.00  res_num_of_loops:                       143
% 3.29/1.00  res_forward_subset_subsumed:            135
% 3.29/1.00  res_backward_subset_subsumed:           0
% 3.29/1.00  res_forward_subsumed:                   0
% 3.29/1.00  res_backward_subsumed:                  0
% 3.29/1.00  res_forward_subsumption_resolution:     0
% 3.29/1.00  res_backward_subsumption_resolution:    1
% 3.29/1.00  res_clause_to_clause_subsumption:       217
% 3.29/1.00  res_orphan_elimination:                 0
% 3.29/1.00  res_tautology_del:                      33
% 3.29/1.00  res_num_eq_res_simplified:              0
% 3.29/1.00  res_num_sel_changes:                    0
% 3.29/1.00  res_moves_from_active_to_pass:          0
% 3.29/1.00  
% 3.29/1.00  ------ Superposition
% 3.29/1.00  
% 3.29/1.00  sup_time_total:                         0.
% 3.29/1.00  sup_time_generating:                    0.
% 3.29/1.00  sup_time_sim_full:                      0.
% 3.29/1.00  sup_time_sim_immed:                     0.
% 3.29/1.00  
% 3.29/1.00  sup_num_of_clauses:                     82
% 3.29/1.00  sup_num_in_active:                      55
% 3.29/1.00  sup_num_in_passive:                     27
% 3.29/1.00  sup_num_of_loops:                       69
% 3.29/1.00  sup_fw_superposition:                   50
% 3.29/1.00  sup_bw_superposition:                   78
% 3.29/1.00  sup_immediate_simplified:               23
% 3.29/1.00  sup_given_eliminated:                   1
% 3.29/1.00  comparisons_done:                       0
% 3.29/1.00  comparisons_avoided:                    20
% 3.29/1.00  
% 3.29/1.00  ------ Simplifications
% 3.29/1.00  
% 3.29/1.00  
% 3.29/1.00  sim_fw_subset_subsumed:                 16
% 3.29/1.00  sim_bw_subset_subsumed:                 11
% 3.29/1.00  sim_fw_subsumed:                        5
% 3.29/1.00  sim_bw_subsumed:                        1
% 3.29/1.00  sim_fw_subsumption_res:                 4
% 3.29/1.00  sim_bw_subsumption_res:                 0
% 3.29/1.00  sim_tautology_del:                      5
% 3.29/1.00  sim_eq_tautology_del:                   14
% 3.29/1.00  sim_eq_res_simp:                        0
% 3.29/1.00  sim_fw_demodulated:                     6
% 3.29/1.00  sim_bw_demodulated:                     10
% 3.29/1.00  sim_light_normalised:                   2
% 3.29/1.00  sim_joinable_taut:                      0
% 3.29/1.00  sim_joinable_simp:                      0
% 3.29/1.00  sim_ac_normalised:                      0
% 3.29/1.00  sim_smt_subsumption:                    0
% 3.29/1.00  
%------------------------------------------------------------------------------
