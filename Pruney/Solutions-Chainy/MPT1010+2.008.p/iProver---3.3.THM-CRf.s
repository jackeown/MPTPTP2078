%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:03 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 255 expanded)
%              Number of clauses        :   56 (  65 expanded)
%              Number of leaves         :   20 (  57 expanded)
%              Depth                    :   20
%              Number of atoms          :  498 (1044 expanded)
%              Number of equality atoms :  243 ( 448 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f45,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK7,sK6) != sK5
      & r2_hidden(sK6,sK4)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))
      & v1_funct_2(sK7,sK4,k1_tarski(sK5))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( k1_funct_1(sK7,sK6) != sK5
    & r2_hidden(sK6,sK4)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))
    & v1_funct_2(sK7,sK4,k1_tarski(sK5))
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f30,f45])).

fof(f83,plain,(
    r2_hidden(sK6,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f85])).

fof(f95,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) ),
    inference(definition_unfolding,[],[f82,f86])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f27])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    v1_funct_2(sK7,sK4,k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
    v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f81,f86])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f51,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f97,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f91])).

fof(f98,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f97])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f38])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f42,f41,f40])).

fof(f66,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f104,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f105,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f104])).

fof(f80,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f58])).

fof(f103,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f84,plain,(
    k1_funct_1(sK7,sK6) != sK5 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_31,negated_conjecture,
    ( r2_hidden(sK6,sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2668,plain,
    ( r2_hidden(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2667,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_22,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_453,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_13])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_457,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_453,c_21])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_457])).

cnf(c_2665,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_3960,plain,
    ( r1_tarski(k2_relat_1(sK7),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2667,c_2665])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1205,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK5,sK5,sK5,sK5) != X2
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X1
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_33])).

cnf(c_1206,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5))))
    | k1_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = sK4
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(unflattening,[status(thm)],[c_1205])).

cnf(c_1208,plain,
    ( k1_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = sK4
    | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1206,c_32])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2669,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5232,plain,
    ( k1_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2667,c_2669])).

cnf(c_5594,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0
    | k1_relat_1(sK7) = sK4 ),
    inference(superposition,[status(thm)],[c_1208,c_5232])).

cnf(c_5,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2677,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2671,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4064,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X1,X2),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2677,c_2671])).

cnf(c_6893,plain,
    ( k1_relat_1(sK7) = sK4
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5594,c_4064])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2682,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7052,plain,
    ( k1_relat_1(sK7) = sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6893,c_2682])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_641,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_34])).

cnf(c_642,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_2660,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_37,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_643,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_2895,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5))))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2896,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2895])).

cnf(c_2944,plain,
    ( r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2660,c_37,c_643,c_2896])).

cnf(c_2945,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2944])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_263,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_264,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_263])).

cnf(c_335,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_264])).

cnf(c_2666,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_5158,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(sK7),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2945,c_2666])).

cnf(c_7054,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(sK7),X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7052,c_5158])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2674,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_15897,plain,
    ( k1_funct_1(sK7,X0) = X1
    | k1_funct_1(sK7,X0) = X2
    | k1_funct_1(sK7,X0) = X3
    | r2_hidden(X0,sK4) != iProver_top
    | r1_tarski(k2_relat_1(sK7),k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7054,c_2674])).

cnf(c_17784,plain,
    ( k1_funct_1(sK7,X0) = sK5
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3960,c_15897])).

cnf(c_17819,plain,
    ( k1_funct_1(sK7,sK6) = sK5 ),
    inference(superposition,[status(thm)],[c_2668,c_17784])).

cnf(c_30,negated_conjecture,
    ( k1_funct_1(sK7,sK6) != sK5 ),
    inference(cnf_transformation,[],[f84])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17819,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.99/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.00  
% 3.99/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.99/1.00  
% 3.99/1.00  ------  iProver source info
% 3.99/1.00  
% 3.99/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.99/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.99/1.00  git: non_committed_changes: false
% 3.99/1.00  git: last_make_outside_of_git: false
% 3.99/1.00  
% 3.99/1.00  ------ 
% 3.99/1.00  
% 3.99/1.00  ------ Input Options
% 3.99/1.00  
% 3.99/1.00  --out_options                           all
% 3.99/1.00  --tptp_safe_out                         true
% 3.99/1.00  --problem_path                          ""
% 3.99/1.00  --include_path                          ""
% 3.99/1.00  --clausifier                            res/vclausify_rel
% 3.99/1.00  --clausifier_options                    --mode clausify
% 3.99/1.00  --stdin                                 false
% 3.99/1.00  --stats_out                             all
% 3.99/1.00  
% 3.99/1.00  ------ General Options
% 3.99/1.00  
% 3.99/1.00  --fof                                   false
% 3.99/1.00  --time_out_real                         305.
% 3.99/1.00  --time_out_virtual                      -1.
% 3.99/1.00  --symbol_type_check                     false
% 3.99/1.00  --clausify_out                          false
% 3.99/1.00  --sig_cnt_out                           false
% 3.99/1.00  --trig_cnt_out                          false
% 3.99/1.00  --trig_cnt_out_tolerance                1.
% 3.99/1.00  --trig_cnt_out_sk_spl                   false
% 3.99/1.00  --abstr_cl_out                          false
% 3.99/1.00  
% 3.99/1.00  ------ Global Options
% 3.99/1.00  
% 3.99/1.00  --schedule                              default
% 3.99/1.00  --add_important_lit                     false
% 3.99/1.00  --prop_solver_per_cl                    1000
% 3.99/1.00  --min_unsat_core                        false
% 3.99/1.00  --soft_assumptions                      false
% 3.99/1.00  --soft_lemma_size                       3
% 3.99/1.00  --prop_impl_unit_size                   0
% 3.99/1.00  --prop_impl_unit                        []
% 3.99/1.00  --share_sel_clauses                     true
% 3.99/1.00  --reset_solvers                         false
% 3.99/1.00  --bc_imp_inh                            [conj_cone]
% 3.99/1.00  --conj_cone_tolerance                   3.
% 3.99/1.00  --extra_neg_conj                        none
% 3.99/1.00  --large_theory_mode                     true
% 3.99/1.00  --prolific_symb_bound                   200
% 3.99/1.00  --lt_threshold                          2000
% 3.99/1.00  --clause_weak_htbl                      true
% 3.99/1.00  --gc_record_bc_elim                     false
% 3.99/1.00  
% 3.99/1.00  ------ Preprocessing Options
% 3.99/1.00  
% 3.99/1.00  --preprocessing_flag                    true
% 3.99/1.00  --time_out_prep_mult                    0.1
% 3.99/1.00  --splitting_mode                        input
% 3.99/1.00  --splitting_grd                         true
% 3.99/1.00  --splitting_cvd                         false
% 3.99/1.00  --splitting_cvd_svl                     false
% 3.99/1.00  --splitting_nvd                         32
% 3.99/1.00  --sub_typing                            true
% 3.99/1.00  --prep_gs_sim                           true
% 3.99/1.00  --prep_unflatten                        true
% 3.99/1.00  --prep_res_sim                          true
% 3.99/1.00  --prep_upred                            true
% 3.99/1.00  --prep_sem_filter                       exhaustive
% 3.99/1.00  --prep_sem_filter_out                   false
% 3.99/1.00  --pred_elim                             true
% 3.99/1.00  --res_sim_input                         true
% 3.99/1.00  --eq_ax_congr_red                       true
% 3.99/1.00  --pure_diseq_elim                       true
% 3.99/1.00  --brand_transform                       false
% 3.99/1.00  --non_eq_to_eq                          false
% 3.99/1.00  --prep_def_merge                        true
% 3.99/1.00  --prep_def_merge_prop_impl              false
% 3.99/1.00  --prep_def_merge_mbd                    true
% 3.99/1.00  --prep_def_merge_tr_red                 false
% 3.99/1.00  --prep_def_merge_tr_cl                  false
% 3.99/1.00  --smt_preprocessing                     true
% 3.99/1.00  --smt_ac_axioms                         fast
% 3.99/1.00  --preprocessed_out                      false
% 3.99/1.00  --preprocessed_stats                    false
% 3.99/1.00  
% 3.99/1.00  ------ Abstraction refinement Options
% 3.99/1.00  
% 3.99/1.00  --abstr_ref                             []
% 3.99/1.00  --abstr_ref_prep                        false
% 3.99/1.00  --abstr_ref_until_sat                   false
% 3.99/1.00  --abstr_ref_sig_restrict                funpre
% 3.99/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.99/1.00  --abstr_ref_under                       []
% 3.99/1.00  
% 3.99/1.00  ------ SAT Options
% 3.99/1.00  
% 3.99/1.00  --sat_mode                              false
% 3.99/1.00  --sat_fm_restart_options                ""
% 3.99/1.00  --sat_gr_def                            false
% 3.99/1.00  --sat_epr_types                         true
% 3.99/1.00  --sat_non_cyclic_types                  false
% 3.99/1.00  --sat_finite_models                     false
% 3.99/1.00  --sat_fm_lemmas                         false
% 3.99/1.00  --sat_fm_prep                           false
% 3.99/1.00  --sat_fm_uc_incr                        true
% 3.99/1.00  --sat_out_model                         small
% 3.99/1.00  --sat_out_clauses                       false
% 3.99/1.00  
% 3.99/1.00  ------ QBF Options
% 3.99/1.00  
% 3.99/1.00  --qbf_mode                              false
% 3.99/1.00  --qbf_elim_univ                         false
% 3.99/1.00  --qbf_dom_inst                          none
% 3.99/1.00  --qbf_dom_pre_inst                      false
% 3.99/1.00  --qbf_sk_in                             false
% 3.99/1.00  --qbf_pred_elim                         true
% 3.99/1.00  --qbf_split                             512
% 3.99/1.00  
% 3.99/1.00  ------ BMC1 Options
% 3.99/1.00  
% 3.99/1.00  --bmc1_incremental                      false
% 3.99/1.00  --bmc1_axioms                           reachable_all
% 3.99/1.00  --bmc1_min_bound                        0
% 3.99/1.00  --bmc1_max_bound                        -1
% 3.99/1.00  --bmc1_max_bound_default                -1
% 3.99/1.00  --bmc1_symbol_reachability              true
% 3.99/1.00  --bmc1_property_lemmas                  false
% 3.99/1.00  --bmc1_k_induction                      false
% 3.99/1.00  --bmc1_non_equiv_states                 false
% 3.99/1.00  --bmc1_deadlock                         false
% 3.99/1.00  --bmc1_ucm                              false
% 3.99/1.00  --bmc1_add_unsat_core                   none
% 3.99/1.00  --bmc1_unsat_core_children              false
% 3.99/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.99/1.00  --bmc1_out_stat                         full
% 3.99/1.00  --bmc1_ground_init                      false
% 3.99/1.00  --bmc1_pre_inst_next_state              false
% 3.99/1.00  --bmc1_pre_inst_state                   false
% 3.99/1.00  --bmc1_pre_inst_reach_state             false
% 3.99/1.00  --bmc1_out_unsat_core                   false
% 3.99/1.00  --bmc1_aig_witness_out                  false
% 3.99/1.00  --bmc1_verbose                          false
% 3.99/1.00  --bmc1_dump_clauses_tptp                false
% 3.99/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.99/1.00  --bmc1_dump_file                        -
% 3.99/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.99/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.99/1.00  --bmc1_ucm_extend_mode                  1
% 3.99/1.00  --bmc1_ucm_init_mode                    2
% 3.99/1.00  --bmc1_ucm_cone_mode                    none
% 3.99/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.99/1.00  --bmc1_ucm_relax_model                  4
% 3.99/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.99/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.99/1.00  --bmc1_ucm_layered_model                none
% 3.99/1.00  --bmc1_ucm_max_lemma_size               10
% 3.99/1.00  
% 3.99/1.00  ------ AIG Options
% 3.99/1.00  
% 3.99/1.00  --aig_mode                              false
% 3.99/1.00  
% 3.99/1.00  ------ Instantiation Options
% 3.99/1.00  
% 3.99/1.00  --instantiation_flag                    true
% 3.99/1.00  --inst_sos_flag                         false
% 3.99/1.00  --inst_sos_phase                        true
% 3.99/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.99/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.99/1.00  --inst_lit_sel_side                     num_symb
% 3.99/1.00  --inst_solver_per_active                1400
% 3.99/1.00  --inst_solver_calls_frac                1.
% 3.99/1.00  --inst_passive_queue_type               priority_queues
% 3.99/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.99/1.00  --inst_passive_queues_freq              [25;2]
% 3.99/1.00  --inst_dismatching                      true
% 3.99/1.00  --inst_eager_unprocessed_to_passive     true
% 3.99/1.00  --inst_prop_sim_given                   true
% 3.99/1.00  --inst_prop_sim_new                     false
% 3.99/1.00  --inst_subs_new                         false
% 3.99/1.00  --inst_eq_res_simp                      false
% 3.99/1.00  --inst_subs_given                       false
% 3.99/1.00  --inst_orphan_elimination               true
% 3.99/1.00  --inst_learning_loop_flag               true
% 3.99/1.00  --inst_learning_start                   3000
% 3.99/1.00  --inst_learning_factor                  2
% 3.99/1.00  --inst_start_prop_sim_after_learn       3
% 3.99/1.00  --inst_sel_renew                        solver
% 3.99/1.00  --inst_lit_activity_flag                true
% 3.99/1.00  --inst_restr_to_given                   false
% 3.99/1.00  --inst_activity_threshold               500
% 3.99/1.00  --inst_out_proof                        true
% 3.99/1.00  
% 3.99/1.00  ------ Resolution Options
% 3.99/1.00  
% 3.99/1.00  --resolution_flag                       true
% 3.99/1.00  --res_lit_sel                           adaptive
% 3.99/1.00  --res_lit_sel_side                      none
% 3.99/1.00  --res_ordering                          kbo
% 3.99/1.00  --res_to_prop_solver                    active
% 3.99/1.00  --res_prop_simpl_new                    false
% 3.99/1.00  --res_prop_simpl_given                  true
% 3.99/1.00  --res_passive_queue_type                priority_queues
% 3.99/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.99/1.00  --res_passive_queues_freq               [15;5]
% 3.99/1.00  --res_forward_subs                      full
% 3.99/1.00  --res_backward_subs                     full
% 3.99/1.00  --res_forward_subs_resolution           true
% 3.99/1.00  --res_backward_subs_resolution          true
% 3.99/1.00  --res_orphan_elimination                true
% 3.99/1.00  --res_time_limit                        2.
% 3.99/1.00  --res_out_proof                         true
% 3.99/1.00  
% 3.99/1.00  ------ Superposition Options
% 3.99/1.00  
% 3.99/1.00  --superposition_flag                    true
% 3.99/1.00  --sup_passive_queue_type                priority_queues
% 3.99/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.99/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.99/1.00  --demod_completeness_check              fast
% 3.99/1.00  --demod_use_ground                      true
% 3.99/1.00  --sup_to_prop_solver                    passive
% 3.99/1.00  --sup_prop_simpl_new                    true
% 3.99/1.00  --sup_prop_simpl_given                  true
% 3.99/1.00  --sup_fun_splitting                     false
% 3.99/1.00  --sup_smt_interval                      50000
% 3.99/1.00  
% 3.99/1.00  ------ Superposition Simplification Setup
% 3.99/1.00  
% 3.99/1.00  --sup_indices_passive                   []
% 3.99/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.99/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/1.00  --sup_full_bw                           [BwDemod]
% 3.99/1.00  --sup_immed_triv                        [TrivRules]
% 3.99/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.99/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/1.00  --sup_immed_bw_main                     []
% 3.99/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.99/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/1.00  
% 3.99/1.00  ------ Combination Options
% 3.99/1.00  
% 3.99/1.00  --comb_res_mult                         3
% 3.99/1.00  --comb_sup_mult                         2
% 3.99/1.00  --comb_inst_mult                        10
% 3.99/1.00  
% 3.99/1.00  ------ Debug Options
% 3.99/1.00  
% 3.99/1.00  --dbg_backtrace                         false
% 3.99/1.00  --dbg_dump_prop_clauses                 false
% 3.99/1.00  --dbg_dump_prop_clauses_file            -
% 3.99/1.00  --dbg_out_stat                          false
% 3.99/1.00  ------ Parsing...
% 3.99/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.99/1.00  
% 3.99/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.99/1.00  
% 3.99/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.99/1.00  
% 3.99/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.99/1.00  ------ Proving...
% 3.99/1.00  ------ Problem Properties 
% 3.99/1.00  
% 3.99/1.00  
% 3.99/1.00  clauses                                 28
% 3.99/1.00  conjectures                             3
% 3.99/1.00  EPR                                     4
% 3.99/1.00  Horn                                    22
% 3.99/1.00  unary                                   7
% 3.99/1.00  binary                                  7
% 3.99/1.00  lits                                    71
% 3.99/1.00  lits eq                                 28
% 3.99/1.00  fd_pure                                 0
% 3.99/1.00  fd_pseudo                               0
% 3.99/1.00  fd_cond                                 3
% 3.99/1.00  fd_pseudo_cond                          4
% 3.99/1.00  AC symbols                              0
% 3.99/1.00  
% 3.99/1.00  ------ Schedule dynamic 5 is on 
% 3.99/1.00  
% 3.99/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.99/1.00  
% 3.99/1.00  
% 3.99/1.00  ------ 
% 3.99/1.00  Current options:
% 3.99/1.00  ------ 
% 3.99/1.00  
% 3.99/1.00  ------ Input Options
% 3.99/1.00  
% 3.99/1.00  --out_options                           all
% 3.99/1.00  --tptp_safe_out                         true
% 3.99/1.00  --problem_path                          ""
% 3.99/1.00  --include_path                          ""
% 3.99/1.00  --clausifier                            res/vclausify_rel
% 3.99/1.00  --clausifier_options                    --mode clausify
% 3.99/1.00  --stdin                                 false
% 3.99/1.00  --stats_out                             all
% 3.99/1.00  
% 3.99/1.00  ------ General Options
% 3.99/1.00  
% 3.99/1.00  --fof                                   false
% 3.99/1.00  --time_out_real                         305.
% 3.99/1.00  --time_out_virtual                      -1.
% 3.99/1.00  --symbol_type_check                     false
% 3.99/1.00  --clausify_out                          false
% 3.99/1.00  --sig_cnt_out                           false
% 3.99/1.00  --trig_cnt_out                          false
% 3.99/1.00  --trig_cnt_out_tolerance                1.
% 3.99/1.00  --trig_cnt_out_sk_spl                   false
% 3.99/1.00  --abstr_cl_out                          false
% 3.99/1.00  
% 3.99/1.00  ------ Global Options
% 3.99/1.00  
% 3.99/1.00  --schedule                              default
% 3.99/1.00  --add_important_lit                     false
% 3.99/1.00  --prop_solver_per_cl                    1000
% 3.99/1.00  --min_unsat_core                        false
% 3.99/1.00  --soft_assumptions                      false
% 3.99/1.00  --soft_lemma_size                       3
% 3.99/1.00  --prop_impl_unit_size                   0
% 3.99/1.00  --prop_impl_unit                        []
% 3.99/1.00  --share_sel_clauses                     true
% 3.99/1.00  --reset_solvers                         false
% 3.99/1.00  --bc_imp_inh                            [conj_cone]
% 3.99/1.00  --conj_cone_tolerance                   3.
% 3.99/1.00  --extra_neg_conj                        none
% 3.99/1.00  --large_theory_mode                     true
% 3.99/1.00  --prolific_symb_bound                   200
% 3.99/1.00  --lt_threshold                          2000
% 3.99/1.00  --clause_weak_htbl                      true
% 3.99/1.00  --gc_record_bc_elim                     false
% 3.99/1.00  
% 3.99/1.00  ------ Preprocessing Options
% 3.99/1.00  
% 3.99/1.00  --preprocessing_flag                    true
% 3.99/1.00  --time_out_prep_mult                    0.1
% 3.99/1.00  --splitting_mode                        input
% 3.99/1.00  --splitting_grd                         true
% 3.99/1.00  --splitting_cvd                         false
% 3.99/1.00  --splitting_cvd_svl                     false
% 3.99/1.00  --splitting_nvd                         32
% 3.99/1.00  --sub_typing                            true
% 3.99/1.00  --prep_gs_sim                           true
% 3.99/1.00  --prep_unflatten                        true
% 3.99/1.00  --prep_res_sim                          true
% 3.99/1.00  --prep_upred                            true
% 3.99/1.00  --prep_sem_filter                       exhaustive
% 3.99/1.00  --prep_sem_filter_out                   false
% 3.99/1.00  --pred_elim                             true
% 3.99/1.00  --res_sim_input                         true
% 3.99/1.00  --eq_ax_congr_red                       true
% 3.99/1.00  --pure_diseq_elim                       true
% 3.99/1.00  --brand_transform                       false
% 3.99/1.00  --non_eq_to_eq                          false
% 3.99/1.00  --prep_def_merge                        true
% 3.99/1.00  --prep_def_merge_prop_impl              false
% 3.99/1.00  --prep_def_merge_mbd                    true
% 3.99/1.00  --prep_def_merge_tr_red                 false
% 3.99/1.00  --prep_def_merge_tr_cl                  false
% 3.99/1.00  --smt_preprocessing                     true
% 3.99/1.00  --smt_ac_axioms                         fast
% 3.99/1.00  --preprocessed_out                      false
% 3.99/1.00  --preprocessed_stats                    false
% 3.99/1.00  
% 3.99/1.00  ------ Abstraction refinement Options
% 3.99/1.00  
% 3.99/1.00  --abstr_ref                             []
% 3.99/1.00  --abstr_ref_prep                        false
% 3.99/1.00  --abstr_ref_until_sat                   false
% 3.99/1.00  --abstr_ref_sig_restrict                funpre
% 3.99/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.99/1.00  --abstr_ref_under                       []
% 3.99/1.00  
% 3.99/1.00  ------ SAT Options
% 3.99/1.00  
% 3.99/1.00  --sat_mode                              false
% 3.99/1.00  --sat_fm_restart_options                ""
% 3.99/1.00  --sat_gr_def                            false
% 3.99/1.00  --sat_epr_types                         true
% 3.99/1.00  --sat_non_cyclic_types                  false
% 3.99/1.00  --sat_finite_models                     false
% 3.99/1.00  --sat_fm_lemmas                         false
% 3.99/1.00  --sat_fm_prep                           false
% 3.99/1.00  --sat_fm_uc_incr                        true
% 3.99/1.00  --sat_out_model                         small
% 3.99/1.00  --sat_out_clauses                       false
% 3.99/1.00  
% 3.99/1.00  ------ QBF Options
% 3.99/1.00  
% 3.99/1.00  --qbf_mode                              false
% 3.99/1.00  --qbf_elim_univ                         false
% 3.99/1.00  --qbf_dom_inst                          none
% 3.99/1.00  --qbf_dom_pre_inst                      false
% 3.99/1.00  --qbf_sk_in                             false
% 3.99/1.00  --qbf_pred_elim                         true
% 3.99/1.00  --qbf_split                             512
% 3.99/1.00  
% 3.99/1.00  ------ BMC1 Options
% 3.99/1.00  
% 3.99/1.00  --bmc1_incremental                      false
% 3.99/1.00  --bmc1_axioms                           reachable_all
% 3.99/1.00  --bmc1_min_bound                        0
% 3.99/1.00  --bmc1_max_bound                        -1
% 3.99/1.00  --bmc1_max_bound_default                -1
% 3.99/1.00  --bmc1_symbol_reachability              true
% 3.99/1.00  --bmc1_property_lemmas                  false
% 3.99/1.00  --bmc1_k_induction                      false
% 3.99/1.00  --bmc1_non_equiv_states                 false
% 3.99/1.00  --bmc1_deadlock                         false
% 3.99/1.00  --bmc1_ucm                              false
% 3.99/1.00  --bmc1_add_unsat_core                   none
% 3.99/1.00  --bmc1_unsat_core_children              false
% 3.99/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.99/1.00  --bmc1_out_stat                         full
% 3.99/1.00  --bmc1_ground_init                      false
% 3.99/1.00  --bmc1_pre_inst_next_state              false
% 3.99/1.00  --bmc1_pre_inst_state                   false
% 3.99/1.00  --bmc1_pre_inst_reach_state             false
% 3.99/1.00  --bmc1_out_unsat_core                   false
% 3.99/1.00  --bmc1_aig_witness_out                  false
% 3.99/1.00  --bmc1_verbose                          false
% 3.99/1.00  --bmc1_dump_clauses_tptp                false
% 3.99/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.99/1.00  --bmc1_dump_file                        -
% 3.99/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.99/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.99/1.00  --bmc1_ucm_extend_mode                  1
% 3.99/1.00  --bmc1_ucm_init_mode                    2
% 3.99/1.00  --bmc1_ucm_cone_mode                    none
% 3.99/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.99/1.00  --bmc1_ucm_relax_model                  4
% 3.99/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.99/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.99/1.00  --bmc1_ucm_layered_model                none
% 3.99/1.00  --bmc1_ucm_max_lemma_size               10
% 3.99/1.00  
% 3.99/1.00  ------ AIG Options
% 3.99/1.00  
% 3.99/1.00  --aig_mode                              false
% 3.99/1.00  
% 3.99/1.00  ------ Instantiation Options
% 3.99/1.00  
% 3.99/1.00  --instantiation_flag                    true
% 3.99/1.00  --inst_sos_flag                         false
% 3.99/1.00  --inst_sos_phase                        true
% 3.99/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.99/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.99/1.00  --inst_lit_sel_side                     none
% 3.99/1.00  --inst_solver_per_active                1400
% 3.99/1.00  --inst_solver_calls_frac                1.
% 3.99/1.00  --inst_passive_queue_type               priority_queues
% 3.99/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.99/1.00  --inst_passive_queues_freq              [25;2]
% 3.99/1.00  --inst_dismatching                      true
% 3.99/1.00  --inst_eager_unprocessed_to_passive     true
% 3.99/1.00  --inst_prop_sim_given                   true
% 3.99/1.00  --inst_prop_sim_new                     false
% 3.99/1.00  --inst_subs_new                         false
% 3.99/1.00  --inst_eq_res_simp                      false
% 3.99/1.00  --inst_subs_given                       false
% 3.99/1.00  --inst_orphan_elimination               true
% 3.99/1.00  --inst_learning_loop_flag               true
% 3.99/1.00  --inst_learning_start                   3000
% 3.99/1.00  --inst_learning_factor                  2
% 3.99/1.00  --inst_start_prop_sim_after_learn       3
% 3.99/1.00  --inst_sel_renew                        solver
% 3.99/1.00  --inst_lit_activity_flag                true
% 3.99/1.00  --inst_restr_to_given                   false
% 3.99/1.00  --inst_activity_threshold               500
% 3.99/1.00  --inst_out_proof                        true
% 3.99/1.00  
% 3.99/1.00  ------ Resolution Options
% 3.99/1.00  
% 3.99/1.00  --resolution_flag                       false
% 3.99/1.00  --res_lit_sel                           adaptive
% 3.99/1.00  --res_lit_sel_side                      none
% 3.99/1.00  --res_ordering                          kbo
% 3.99/1.00  --res_to_prop_solver                    active
% 3.99/1.00  --res_prop_simpl_new                    false
% 3.99/1.00  --res_prop_simpl_given                  true
% 3.99/1.00  --res_passive_queue_type                priority_queues
% 3.99/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.99/1.00  --res_passive_queues_freq               [15;5]
% 3.99/1.00  --res_forward_subs                      full
% 3.99/1.00  --res_backward_subs                     full
% 3.99/1.00  --res_forward_subs_resolution           true
% 3.99/1.00  --res_backward_subs_resolution          true
% 3.99/1.00  --res_orphan_elimination                true
% 3.99/1.00  --res_time_limit                        2.
% 3.99/1.00  --res_out_proof                         true
% 3.99/1.00  
% 3.99/1.00  ------ Superposition Options
% 3.99/1.00  
% 3.99/1.00  --superposition_flag                    true
% 3.99/1.00  --sup_passive_queue_type                priority_queues
% 3.99/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.99/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.99/1.00  --demod_completeness_check              fast
% 3.99/1.00  --demod_use_ground                      true
% 3.99/1.00  --sup_to_prop_solver                    passive
% 3.99/1.00  --sup_prop_simpl_new                    true
% 3.99/1.00  --sup_prop_simpl_given                  true
% 3.99/1.00  --sup_fun_splitting                     false
% 3.99/1.00  --sup_smt_interval                      50000
% 3.99/1.00  
% 3.99/1.00  ------ Superposition Simplification Setup
% 3.99/1.00  
% 3.99/1.00  --sup_indices_passive                   []
% 3.99/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.99/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.99/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/1.00  --sup_full_bw                           [BwDemod]
% 3.99/1.00  --sup_immed_triv                        [TrivRules]
% 3.99/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.99/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/1.00  --sup_immed_bw_main                     []
% 3.99/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.99/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.99/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.99/1.00  
% 3.99/1.00  ------ Combination Options
% 3.99/1.00  
% 3.99/1.00  --comb_res_mult                         3
% 3.99/1.00  --comb_sup_mult                         2
% 3.99/1.00  --comb_inst_mult                        10
% 3.99/1.00  
% 3.99/1.00  ------ Debug Options
% 3.99/1.00  
% 3.99/1.00  --dbg_backtrace                         false
% 3.99/1.00  --dbg_dump_prop_clauses                 false
% 3.99/1.00  --dbg_dump_prop_clauses_file            -
% 3.99/1.00  --dbg_out_stat                          false
% 3.99/1.00  
% 3.99/1.00  
% 3.99/1.00  
% 3.99/1.00  
% 3.99/1.00  ------ Proving...
% 3.99/1.00  
% 3.99/1.00  
% 3.99/1.00  % SZS status Theorem for theBenchmark.p
% 3.99/1.00  
% 3.99/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.99/1.00  
% 3.99/1.00  fof(f15,conjecture,(
% 3.99/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f16,negated_conjecture,(
% 3.99/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.99/1.00    inference(negated_conjecture,[],[f15])).
% 3.99/1.00  
% 3.99/1.00  fof(f29,plain,(
% 3.99/1.00    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 3.99/1.00    inference(ennf_transformation,[],[f16])).
% 3.99/1.00  
% 3.99/1.00  fof(f30,plain,(
% 3.99/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 3.99/1.00    inference(flattening,[],[f29])).
% 3.99/1.00  
% 3.99/1.00  fof(f45,plain,(
% 3.99/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK7,sK6) != sK5 & r2_hidden(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) & v1_funct_2(sK7,sK4,k1_tarski(sK5)) & v1_funct_1(sK7))),
% 3.99/1.00    introduced(choice_axiom,[])).
% 3.99/1.00  
% 3.99/1.00  fof(f46,plain,(
% 3.99/1.00    k1_funct_1(sK7,sK6) != sK5 & r2_hidden(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) & v1_funct_2(sK7,sK4,k1_tarski(sK5)) & v1_funct_1(sK7)),
% 3.99/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f30,f45])).
% 3.99/1.00  
% 3.99/1.00  fof(f83,plain,(
% 3.99/1.00    r2_hidden(sK6,sK4)),
% 3.99/1.00    inference(cnf_transformation,[],[f46])).
% 3.99/1.00  
% 3.99/1.00  fof(f82,plain,(
% 3.99/1.00    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))),
% 3.99/1.00    inference(cnf_transformation,[],[f46])).
% 3.99/1.00  
% 3.99/1.00  fof(f3,axiom,(
% 3.99/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f56,plain,(
% 3.99/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.99/1.00    inference(cnf_transformation,[],[f3])).
% 3.99/1.00  
% 3.99/1.00  fof(f4,axiom,(
% 3.99/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f57,plain,(
% 3.99/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.99/1.00    inference(cnf_transformation,[],[f4])).
% 3.99/1.00  
% 3.99/1.00  fof(f5,axiom,(
% 3.99/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f58,plain,(
% 3.99/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.99/1.00    inference(cnf_transformation,[],[f5])).
% 3.99/1.00  
% 3.99/1.00  fof(f85,plain,(
% 3.99/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.99/1.00    inference(definition_unfolding,[],[f57,f58])).
% 3.99/1.00  
% 3.99/1.00  fof(f86,plain,(
% 3.99/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.99/1.00    inference(definition_unfolding,[],[f56,f85])).
% 3.99/1.00  
% 3.99/1.00  fof(f95,plain,(
% 3.99/1.00    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5))))),
% 3.99/1.00    inference(definition_unfolding,[],[f82,f86])).
% 3.99/1.00  
% 3.99/1.00  fof(f12,axiom,(
% 3.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f17,plain,(
% 3.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.99/1.00    inference(pure_predicate_removal,[],[f12])).
% 3.99/1.00  
% 3.99/1.00  fof(f25,plain,(
% 3.99/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.99/1.00    inference(ennf_transformation,[],[f17])).
% 3.99/1.00  
% 3.99/1.00  fof(f72,plain,(
% 3.99/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.99/1.00    inference(cnf_transformation,[],[f25])).
% 3.99/1.00  
% 3.99/1.00  fof(f8,axiom,(
% 3.99/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f20,plain,(
% 3.99/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.99/1.00    inference(ennf_transformation,[],[f8])).
% 3.99/1.00  
% 3.99/1.00  fof(f37,plain,(
% 3.99/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.99/1.00    inference(nnf_transformation,[],[f20])).
% 3.99/1.00  
% 3.99/1.00  fof(f62,plain,(
% 3.99/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.99/1.00    inference(cnf_transformation,[],[f37])).
% 3.99/1.00  
% 3.99/1.00  fof(f11,axiom,(
% 3.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f24,plain,(
% 3.99/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.99/1.00    inference(ennf_transformation,[],[f11])).
% 3.99/1.00  
% 3.99/1.00  fof(f71,plain,(
% 3.99/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.99/1.00    inference(cnf_transformation,[],[f24])).
% 3.99/1.00  
% 3.99/1.00  fof(f14,axiom,(
% 3.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f27,plain,(
% 3.99/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.99/1.00    inference(ennf_transformation,[],[f14])).
% 3.99/1.00  
% 3.99/1.00  fof(f28,plain,(
% 3.99/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.99/1.00    inference(flattening,[],[f27])).
% 3.99/1.00  
% 3.99/1.00  fof(f44,plain,(
% 3.99/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.99/1.00    inference(nnf_transformation,[],[f28])).
% 3.99/1.00  
% 3.99/1.00  fof(f74,plain,(
% 3.99/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.99/1.00    inference(cnf_transformation,[],[f44])).
% 3.99/1.00  
% 3.99/1.00  fof(f81,plain,(
% 3.99/1.00    v1_funct_2(sK7,sK4,k1_tarski(sK5))),
% 3.99/1.00    inference(cnf_transformation,[],[f46])).
% 3.99/1.00  
% 3.99/1.00  fof(f96,plain,(
% 3.99/1.00    v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5))),
% 3.99/1.00    inference(definition_unfolding,[],[f81,f86])).
% 3.99/1.00  
% 3.99/1.00  fof(f13,axiom,(
% 3.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f26,plain,(
% 3.99/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.99/1.00    inference(ennf_transformation,[],[f13])).
% 3.99/1.00  
% 3.99/1.00  fof(f73,plain,(
% 3.99/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.99/1.00    inference(cnf_transformation,[],[f26])).
% 3.99/1.00  
% 3.99/1.00  fof(f2,axiom,(
% 3.99/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f18,plain,(
% 3.99/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.99/1.00    inference(ennf_transformation,[],[f2])).
% 3.99/1.00  
% 3.99/1.00  fof(f31,plain,(
% 3.99/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.99/1.00    inference(nnf_transformation,[],[f18])).
% 3.99/1.00  
% 3.99/1.00  fof(f32,plain,(
% 3.99/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.99/1.00    inference(flattening,[],[f31])).
% 3.99/1.00  
% 3.99/1.00  fof(f33,plain,(
% 3.99/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.99/1.00    inference(rectify,[],[f32])).
% 3.99/1.00  
% 3.99/1.00  fof(f34,plain,(
% 3.99/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.99/1.00    introduced(choice_axiom,[])).
% 3.99/1.00  
% 3.99/1.00  fof(f35,plain,(
% 3.99/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.99/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.99/1.00  
% 3.99/1.00  fof(f51,plain,(
% 3.99/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.99/1.00    inference(cnf_transformation,[],[f35])).
% 3.99/1.00  
% 3.99/1.00  fof(f91,plain,(
% 3.99/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.99/1.00    inference(definition_unfolding,[],[f51,f58])).
% 3.99/1.00  
% 3.99/1.00  fof(f97,plain,(
% 3.99/1.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 3.99/1.00    inference(equality_resolution,[],[f91])).
% 3.99/1.00  
% 3.99/1.00  fof(f98,plain,(
% 3.99/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 3.99/1.00    inference(equality_resolution,[],[f97])).
% 3.99/1.00  
% 3.99/1.00  fof(f10,axiom,(
% 3.99/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f23,plain,(
% 3.99/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.99/1.00    inference(ennf_transformation,[],[f10])).
% 3.99/1.00  
% 3.99/1.00  fof(f70,plain,(
% 3.99/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.99/1.00    inference(cnf_transformation,[],[f23])).
% 3.99/1.00  
% 3.99/1.00  fof(f1,axiom,(
% 3.99/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f47,plain,(
% 3.99/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.99/1.00    inference(cnf_transformation,[],[f1])).
% 3.99/1.00  
% 3.99/1.00  fof(f9,axiom,(
% 3.99/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f21,plain,(
% 3.99/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.99/1.00    inference(ennf_transformation,[],[f9])).
% 3.99/1.00  
% 3.99/1.00  fof(f22,plain,(
% 3.99/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.99/1.00    inference(flattening,[],[f21])).
% 3.99/1.00  
% 3.99/1.00  fof(f38,plain,(
% 3.99/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.99/1.00    inference(nnf_transformation,[],[f22])).
% 3.99/1.00  
% 3.99/1.00  fof(f39,plain,(
% 3.99/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.99/1.00    inference(rectify,[],[f38])).
% 3.99/1.00  
% 3.99/1.00  fof(f42,plain,(
% 3.99/1.00    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 3.99/1.00    introduced(choice_axiom,[])).
% 3.99/1.00  
% 3.99/1.00  fof(f41,plain,(
% 3.99/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 3.99/1.00    introduced(choice_axiom,[])).
% 3.99/1.00  
% 3.99/1.00  fof(f40,plain,(
% 3.99/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 3.99/1.00    introduced(choice_axiom,[])).
% 3.99/1.00  
% 3.99/1.00  fof(f43,plain,(
% 3.99/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.99/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f42,f41,f40])).
% 3.99/1.00  
% 3.99/1.00  fof(f66,plain,(
% 3.99/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.99/1.00    inference(cnf_transformation,[],[f43])).
% 3.99/1.00  
% 3.99/1.00  fof(f104,plain,(
% 3.99/1.00    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.99/1.00    inference(equality_resolution,[],[f66])).
% 3.99/1.00  
% 3.99/1.00  fof(f105,plain,(
% 3.99/1.00    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.99/1.00    inference(equality_resolution,[],[f104])).
% 3.99/1.00  
% 3.99/1.00  fof(f80,plain,(
% 3.99/1.00    v1_funct_1(sK7)),
% 3.99/1.00    inference(cnf_transformation,[],[f46])).
% 3.99/1.00  
% 3.99/1.00  fof(f6,axiom,(
% 3.99/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f19,plain,(
% 3.99/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.99/1.00    inference(ennf_transformation,[],[f6])).
% 3.99/1.00  
% 3.99/1.00  fof(f59,plain,(
% 3.99/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.99/1.00    inference(cnf_transformation,[],[f19])).
% 3.99/1.00  
% 3.99/1.00  fof(f7,axiom,(
% 3.99/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.00  
% 3.99/1.00  fof(f36,plain,(
% 3.99/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.99/1.00    inference(nnf_transformation,[],[f7])).
% 3.99/1.00  
% 3.99/1.00  fof(f61,plain,(
% 3.99/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.99/1.00    inference(cnf_transformation,[],[f36])).
% 3.99/1.00  
% 3.99/1.00  fof(f48,plain,(
% 3.99/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.99/1.00    inference(cnf_transformation,[],[f35])).
% 3.99/1.00  
% 3.99/1.00  fof(f94,plain,(
% 3.99/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.99/1.00    inference(definition_unfolding,[],[f48,f58])).
% 3.99/1.00  
% 3.99/1.00  fof(f103,plain,(
% 3.99/1.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 3.99/1.00    inference(equality_resolution,[],[f94])).
% 3.99/1.00  
% 3.99/1.00  fof(f84,plain,(
% 3.99/1.00    k1_funct_1(sK7,sK6) != sK5),
% 3.99/1.00    inference(cnf_transformation,[],[f46])).
% 3.99/1.00  
% 3.99/1.00  cnf(c_31,negated_conjecture,
% 3.99/1.00      ( r2_hidden(sK6,sK4) ),
% 3.99/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2668,plain,
% 3.99/1.00      ( r2_hidden(sK6,sK4) = iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_32,negated_conjecture,
% 3.99/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) ),
% 3.99/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2667,plain,
% 3.99/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) = iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_22,plain,
% 3.99/1.00      ( v5_relat_1(X0,X1)
% 3.99/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.99/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_13,plain,
% 3.99/1.00      ( ~ v5_relat_1(X0,X1)
% 3.99/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.99/1.00      | ~ v1_relat_1(X0) ),
% 3.99/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_453,plain,
% 3.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.99/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 3.99/1.00      | ~ v1_relat_1(X0) ),
% 3.99/1.00      inference(resolution,[status(thm)],[c_22,c_13]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_21,plain,
% 3.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.99/1.00      | v1_relat_1(X0) ),
% 3.99/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_457,plain,
% 3.99/1.00      ( r1_tarski(k2_relat_1(X0),X2)
% 3.99/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.99/1.00      inference(global_propositional_subsumption,
% 3.99/1.00                [status(thm)],
% 3.99/1.00                [c_453,c_21]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_458,plain,
% 3.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.99/1.00      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.99/1.00      inference(renaming,[status(thm)],[c_457]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2665,plain,
% 3.99/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.99/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_3960,plain,
% 3.99/1.00      ( r1_tarski(k2_relat_1(sK7),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_2667,c_2665]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_29,plain,
% 3.99/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.99/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.99/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.99/1.00      | k1_xboole_0 = X2 ),
% 3.99/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_33,negated_conjecture,
% 3.99/1.00      ( v1_funct_2(sK7,sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 3.99/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1205,plain,
% 3.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.99/1.00      | k2_enumset1(sK5,sK5,sK5,sK5) != X2
% 3.99/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.99/1.00      | sK4 != X1
% 3.99/1.00      | sK7 != X0
% 3.99/1.00      | k1_xboole_0 = X2 ),
% 3.99/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_33]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1206,plain,
% 3.99/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5))))
% 3.99/1.00      | k1_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = sK4
% 3.99/1.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.99/1.00      inference(unflattening,[status(thm)],[c_1205]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_1208,plain,
% 3.99/1.00      ( k1_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = sK4
% 3.99/1.00      | k1_xboole_0 = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.99/1.00      inference(global_propositional_subsumption,
% 3.99/1.00                [status(thm)],
% 3.99/1.00                [c_1206,c_32]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_23,plain,
% 3.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.99/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.99/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2669,plain,
% 3.99/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.99/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_5232,plain,
% 3.99/1.00      ( k1_relset_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK7) = k1_relat_1(sK7) ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_2667,c_2669]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_5594,plain,
% 3.99/1.00      ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_xboole_0
% 3.99/1.00      | k1_relat_1(sK7) = sK4 ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_1208,c_5232]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_5,plain,
% 3.99/1.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 3.99/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2677,plain,
% 3.99/1.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_20,plain,
% 3.99/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.99/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2671,plain,
% 3.99/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.99/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_4064,plain,
% 3.99/1.00      ( r1_tarski(k2_enumset1(X0,X0,X1,X2),X2) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_2677,c_2671]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_6893,plain,
% 3.99/1.00      ( k1_relat_1(sK7) = sK4
% 3.99/1.00      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_5594,c_4064]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_0,plain,
% 3.99/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.99/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2682,plain,
% 3.99/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_7052,plain,
% 3.99/1.00      ( k1_relat_1(sK7) = sK4 ),
% 3.99/1.00      inference(forward_subsumption_resolution,
% 3.99/1.00                [status(thm)],
% 3.99/1.00                [c_6893,c_2682]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_17,plain,
% 3.99/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.99/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.99/1.00      | ~ v1_funct_1(X1)
% 3.99/1.00      | ~ v1_relat_1(X1) ),
% 3.99/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_34,negated_conjecture,
% 3.99/1.00      ( v1_funct_1(sK7) ),
% 3.99/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_641,plain,
% 3.99/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.99/1.00      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.99/1.00      | ~ v1_relat_1(X1)
% 3.99/1.00      | sK7 != X1 ),
% 3.99/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_34]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_642,plain,
% 3.99/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 3.99/1.00      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
% 3.99/1.00      | ~ v1_relat_1(sK7) ),
% 3.99/1.00      inference(unflattening,[status(thm)],[c_641]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2660,plain,
% 3.99/1.00      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.99/1.00      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 3.99/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_37,plain,
% 3.99/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) = iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_643,plain,
% 3.99/1.00      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.99/1.00      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 3.99/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2895,plain,
% 3.99/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5))))
% 3.99/1.00      | v1_relat_1(sK7) ),
% 3.99/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2896,plain,
% 3.99/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) != iProver_top
% 3.99/1.00      | v1_relat_1(sK7) = iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_2895]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2944,plain,
% 3.99/1.00      ( r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 3.99/1.00      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.99/1.00      inference(global_propositional_subsumption,
% 3.99/1.00                [status(thm)],
% 3.99/1.00                [c_2660,c_37,c_643,c_2896]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2945,plain,
% 3.99/1.00      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.99/1.00      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
% 3.99/1.00      inference(renaming,[status(thm)],[c_2944]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_9,plain,
% 3.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.99/1.00      | ~ r2_hidden(X2,X0)
% 3.99/1.00      | r2_hidden(X2,X1) ),
% 3.99/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_10,plain,
% 3.99/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.99/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_263,plain,
% 3.99/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.99/1.00      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_264,plain,
% 3.99/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.99/1.00      inference(renaming,[status(thm)],[c_263]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_335,plain,
% 3.99/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.99/1.00      inference(bin_hyper_res,[status(thm)],[c_9,c_264]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2666,plain,
% 3.99/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.99/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.99/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_5158,plain,
% 3.99/1.00      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.99/1.00      | r2_hidden(k1_funct_1(sK7,X0),X1) = iProver_top
% 3.99/1.00      | r1_tarski(k2_relat_1(sK7),X1) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_2945,c_2666]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_7054,plain,
% 3.99/1.00      ( r2_hidden(X0,sK4) != iProver_top
% 3.99/1.00      | r2_hidden(k1_funct_1(sK7,X0),X1) = iProver_top
% 3.99/1.00      | r1_tarski(k2_relat_1(sK7),X1) != iProver_top ),
% 3.99/1.00      inference(demodulation,[status(thm)],[c_7052,c_5158]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_8,plain,
% 3.99/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 3.99/1.00      | X0 = X1
% 3.99/1.00      | X0 = X2
% 3.99/1.00      | X0 = X3 ),
% 3.99/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_2674,plain,
% 3.99/1.00      ( X0 = X1
% 3.99/1.00      | X0 = X2
% 3.99/1.00      | X0 = X3
% 3.99/1.00      | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
% 3.99/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_15897,plain,
% 3.99/1.00      ( k1_funct_1(sK7,X0) = X1
% 3.99/1.00      | k1_funct_1(sK7,X0) = X2
% 3.99/1.00      | k1_funct_1(sK7,X0) = X3
% 3.99/1.00      | r2_hidden(X0,sK4) != iProver_top
% 3.99/1.00      | r1_tarski(k2_relat_1(sK7),k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_7054,c_2674]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_17784,plain,
% 3.99/1.00      ( k1_funct_1(sK7,X0) = sK5 | r2_hidden(X0,sK4) != iProver_top ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_3960,c_15897]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_17819,plain,
% 3.99/1.00      ( k1_funct_1(sK7,sK6) = sK5 ),
% 3.99/1.00      inference(superposition,[status(thm)],[c_2668,c_17784]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(c_30,negated_conjecture,
% 3.99/1.00      ( k1_funct_1(sK7,sK6) != sK5 ),
% 3.99/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.99/1.00  
% 3.99/1.00  cnf(contradiction,plain,
% 3.99/1.00      ( $false ),
% 3.99/1.00      inference(minisat,[status(thm)],[c_17819,c_30]) ).
% 3.99/1.00  
% 3.99/1.00  
% 3.99/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.99/1.00  
% 3.99/1.00  ------                               Statistics
% 3.99/1.00  
% 3.99/1.00  ------ General
% 3.99/1.00  
% 3.99/1.00  abstr_ref_over_cycles:                  0
% 3.99/1.00  abstr_ref_under_cycles:                 0
% 3.99/1.00  gc_basic_clause_elim:                   0
% 3.99/1.00  forced_gc_time:                         0
% 3.99/1.00  parsing_time:                           0.009
% 3.99/1.00  unif_index_cands_time:                  0.
% 3.99/1.00  unif_index_add_time:                    0.
% 3.99/1.00  orderings_time:                         0.
% 3.99/1.00  out_proof_time:                         0.011
% 3.99/1.00  total_time:                             0.482
% 3.99/1.00  num_of_symbols:                         54
% 3.99/1.00  num_of_terms:                           19345
% 3.99/1.00  
% 3.99/1.00  ------ Preprocessing
% 3.99/1.00  
% 3.99/1.00  num_of_splits:                          0
% 3.99/1.00  num_of_split_atoms:                     0
% 3.99/1.00  num_of_reused_defs:                     0
% 3.99/1.00  num_eq_ax_congr_red:                    34
% 3.99/1.00  num_of_sem_filtered_clauses:            1
% 3.99/1.00  num_of_subtypes:                        0
% 3.99/1.00  monotx_restored_types:                  0
% 3.99/1.00  sat_num_of_epr_types:                   0
% 3.99/1.00  sat_num_of_non_cyclic_types:            0
% 3.99/1.00  sat_guarded_non_collapsed_types:        0
% 3.99/1.00  num_pure_diseq_elim:                    0
% 3.99/1.00  simp_replaced_by:                       0
% 3.99/1.00  res_preprocessed:                       152
% 3.99/1.00  prep_upred:                             0
% 3.99/1.00  prep_unflattend:                        112
% 3.99/1.00  smt_new_axioms:                         0
% 3.99/1.00  pred_elim_cands:                        4
% 3.99/1.00  pred_elim:                              3
% 3.99/1.00  pred_elim_cl:                           7
% 3.99/1.00  pred_elim_cycles:                       10
% 3.99/1.00  merged_defs:                            8
% 3.99/1.00  merged_defs_ncl:                        0
% 3.99/1.00  bin_hyper_res:                          9
% 3.99/1.00  prep_cycles:                            4
% 3.99/1.00  pred_elim_time:                         0.024
% 3.99/1.00  splitting_time:                         0.
% 3.99/1.00  sem_filter_time:                        0.
% 3.99/1.00  monotx_time:                            0.
% 3.99/1.00  subtype_inf_time:                       0.
% 3.99/1.00  
% 3.99/1.00  ------ Problem properties
% 3.99/1.00  
% 3.99/1.00  clauses:                                28
% 3.99/1.00  conjectures:                            3
% 3.99/1.00  epr:                                    4
% 3.99/1.00  horn:                                   22
% 3.99/1.00  ground:                                 6
% 3.99/1.00  unary:                                  7
% 3.99/1.00  binary:                                 7
% 3.99/1.00  lits:                                   71
% 3.99/1.00  lits_eq:                                28
% 3.99/1.00  fd_pure:                                0
% 3.99/1.00  fd_pseudo:                              0
% 3.99/1.00  fd_cond:                                3
% 3.99/1.00  fd_pseudo_cond:                         4
% 3.99/1.00  ac_symbols:                             0
% 3.99/1.00  
% 3.99/1.00  ------ Propositional Solver
% 3.99/1.00  
% 3.99/1.00  prop_solver_calls:                      28
% 3.99/1.00  prop_fast_solver_calls:                 1417
% 3.99/1.00  smt_solver_calls:                       0
% 3.99/1.00  smt_fast_solver_calls:                  0
% 3.99/1.00  prop_num_of_clauses:                    6166
% 3.99/1.00  prop_preprocess_simplified:             16669
% 3.99/1.00  prop_fo_subsumed:                       10
% 3.99/1.00  prop_solver_time:                       0.
% 3.99/1.00  smt_solver_time:                        0.
% 3.99/1.00  smt_fast_solver_time:                   0.
% 3.99/1.00  prop_fast_solver_time:                  0.
% 3.99/1.00  prop_unsat_core_time:                   0.
% 3.99/1.00  
% 3.99/1.00  ------ QBF
% 3.99/1.00  
% 3.99/1.00  qbf_q_res:                              0
% 3.99/1.00  qbf_num_tautologies:                    0
% 3.99/1.00  qbf_prep_cycles:                        0
% 3.99/1.00  
% 3.99/1.00  ------ BMC1
% 3.99/1.00  
% 3.99/1.00  bmc1_current_bound:                     -1
% 3.99/1.00  bmc1_last_solved_bound:                 -1
% 3.99/1.00  bmc1_unsat_core_size:                   -1
% 3.99/1.00  bmc1_unsat_core_parents_size:           -1
% 3.99/1.00  bmc1_merge_next_fun:                    0
% 3.99/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.99/1.00  
% 3.99/1.00  ------ Instantiation
% 3.99/1.00  
% 3.99/1.00  inst_num_of_clauses:                    1651
% 3.99/1.00  inst_num_in_passive:                    997
% 3.99/1.00  inst_num_in_active:                     518
% 3.99/1.00  inst_num_in_unprocessed:                137
% 3.99/1.00  inst_num_of_loops:                      580
% 3.99/1.00  inst_num_of_learning_restarts:          0
% 3.99/1.00  inst_num_moves_active_passive:          61
% 3.99/1.00  inst_lit_activity:                      0
% 3.99/1.00  inst_lit_activity_moves:                0
% 3.99/1.00  inst_num_tautologies:                   0
% 3.99/1.00  inst_num_prop_implied:                  0
% 3.99/1.00  inst_num_existing_simplified:           0
% 3.99/1.00  inst_num_eq_res_simplified:             0
% 3.99/1.00  inst_num_child_elim:                    0
% 3.99/1.00  inst_num_of_dismatching_blockings:      2144
% 3.99/1.00  inst_num_of_non_proper_insts:           1641
% 3.99/1.00  inst_num_of_duplicates:                 0
% 3.99/1.00  inst_inst_num_from_inst_to_res:         0
% 3.99/1.00  inst_dismatching_checking_time:         0.
% 3.99/1.00  
% 3.99/1.00  ------ Resolution
% 3.99/1.00  
% 3.99/1.00  res_num_of_clauses:                     0
% 3.99/1.00  res_num_in_passive:                     0
% 3.99/1.00  res_num_in_active:                      0
% 3.99/1.00  res_num_of_loops:                       156
% 3.99/1.00  res_forward_subset_subsumed:            371
% 3.99/1.00  res_backward_subset_subsumed:           2
% 3.99/1.00  res_forward_subsumed:                   0
% 3.99/1.00  res_backward_subsumed:                  0
% 3.99/1.00  res_forward_subsumption_resolution:     0
% 3.99/1.00  res_backward_subsumption_resolution:    1
% 3.99/1.00  res_clause_to_clause_subsumption:       981
% 3.99/1.00  res_orphan_elimination:                 0
% 3.99/1.00  res_tautology_del:                      88
% 3.99/1.00  res_num_eq_res_simplified:              0
% 3.99/1.00  res_num_sel_changes:                    0
% 3.99/1.00  res_moves_from_active_to_pass:          0
% 3.99/1.00  
% 3.99/1.00  ------ Superposition
% 3.99/1.00  
% 3.99/1.00  sup_time_total:                         0.
% 3.99/1.00  sup_time_generating:                    0.
% 3.99/1.00  sup_time_sim_full:                      0.
% 3.99/1.00  sup_time_sim_immed:                     0.
% 3.99/1.00  
% 3.99/1.00  sup_num_of_clauses:                     248
% 3.99/1.00  sup_num_in_active:                      100
% 3.99/1.00  sup_num_in_passive:                     148
% 3.99/1.00  sup_num_of_loops:                       115
% 3.99/1.00  sup_fw_superposition:                   173
% 3.99/1.00  sup_bw_superposition:                   181
% 3.99/1.00  sup_immediate_simplified:               33
% 3.99/1.00  sup_given_eliminated:                   0
% 3.99/1.00  comparisons_done:                       0
% 3.99/1.00  comparisons_avoided:                    91
% 3.99/1.00  
% 3.99/1.00  ------ Simplifications
% 3.99/1.00  
% 3.99/1.00  
% 3.99/1.00  sim_fw_subset_subsumed:                 24
% 3.99/1.00  sim_bw_subset_subsumed:                 8
% 3.99/1.00  sim_fw_subsumed:                        6
% 3.99/1.00  sim_bw_subsumed:                        0
% 3.99/1.00  sim_fw_subsumption_res:                 2
% 3.99/1.00  sim_bw_subsumption_res:                 0
% 3.99/1.00  sim_tautology_del:                      2
% 3.99/1.00  sim_eq_tautology_del:                   42
% 3.99/1.00  sim_eq_res_simp:                        0
% 3.99/1.00  sim_fw_demodulated:                     0
% 3.99/1.00  sim_bw_demodulated:                     14
% 3.99/1.00  sim_light_normalised:                   19
% 3.99/1.00  sim_joinable_taut:                      0
% 3.99/1.00  sim_joinable_simp:                      0
% 3.99/1.00  sim_ac_normalised:                      0
% 3.99/1.00  sim_smt_subsumption:                    0
% 3.99/1.00  
%------------------------------------------------------------------------------
