%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:14 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 867 expanded)
%              Number of clauses        :   69 ( 222 expanded)
%              Number of leaves         :   17 ( 192 expanded)
%              Depth                    :   24
%              Number of atoms          :  496 (2931 expanded)
%              Number of equality atoms :  286 (1195 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f39,plain,
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

fof(f40,plain,
    ( k1_funct_1(sK5,sK4) != sK3
    & r2_hidden(sK4,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f39])).

fof(f76,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f78])).

fof(f84,plain,(
    v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f74,f79])).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f83,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f75,f79])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( sP0(X3,X2,X1,X0,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP0(X3,X2,X1,X0,X4) ) ),
    inference(definition_folding,[],[f15,f26])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP0(X3,X2,X1,X0,X4) )
      & ( sP0(X3,X2,X1,X0,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] : sP0(X3,X2,X1,X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f58])).

fof(f30,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f31,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ( X0 != X5
                & X1 != X5
                & X2 != X5
                & X3 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | X3 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X0 != X5
              & X1 != X5
              & X2 != X5
              & X3 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X0 = X5
            | X1 = X5
            | X2 = X5
            | X3 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK1(X0,X1,X2,X3,X4) != X0
            & sK1(X0,X1,X2,X3,X4) != X1
            & sK1(X0,X1,X2,X3,X4) != X2
            & sK1(X0,X1,X2,X3,X4) != X3 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3,X4),X4) )
        & ( sK1(X0,X1,X2,X3,X4) = X0
          | sK1(X0,X1,X2,X3,X4) = X1
          | sK1(X0,X1,X2,X3,X4) = X2
          | sK1(X0,X1,X2,X3,X4) = X3
          | r2_hidden(sK1(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( ( ( sK1(X0,X1,X2,X3,X4) != X0
              & sK1(X0,X1,X2,X3,X4) != X1
              & sK1(X0,X1,X2,X3,X4) != X2
              & sK1(X0,X1,X2,X3,X4) != X3 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3,X4),X4) )
          & ( sK1(X0,X1,X2,X3,X4) = X0
            | sK1(X0,X1,X2,X3,X4) = X1
            | sK1(X0,X1,X2,X3,X4) = X2
            | sK1(X0,X1,X2,X3,X4) = X3
            | r2_hidden(sK1(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X0 != X6
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,(
    ! [X6,X4,X2,X3,X1] :
      ( r2_hidden(X6,X4)
      | ~ sP0(X6,X1,X2,X3,X4) ) ),
    inference(equality_resolution,[],[f52])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f71])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f63])).

fof(f73,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f28])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) ) ),
    inference(definition_unfolding,[],[f46,f79])).

fof(f77,plain,(
    k1_funct_1(sK5,sK4) != sK3 ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2705,plain,
    ( r2_hidden(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_505,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_31])).

cnf(c_506,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | k1_relset_1(X0,X1,sK5) = X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_723,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != X0
    | k1_relset_1(X1,X0,sK5) = X1
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
    | sK2 != X1
    | sK5 != sK5
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_506])).

cnf(c_724,plain,
    ( k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_1471,plain,
    ( k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = sK2
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_724])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_541,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_542,plain,
    ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_2924,plain,
    ( k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = k1_relat_1(sK5) ),
    inference(equality_resolution,[status(thm)],[c_542])).

cnf(c_3081,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0
    | k1_relat_1(sK5) = sK2 ),
    inference(demodulation,[status(thm)],[c_1471,c_2924])).

cnf(c_15,plain,
    ( sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2706,plain,
    ( sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3117,plain,
    ( k1_relat_1(sK5) = sK2
    | sP0(sK3,sK3,sK3,sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3081,c_2706])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | r2_hidden(X0,X4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2712,plain,
    ( sP0(X0,X1,X2,X3,X4) != iProver_top
    | r2_hidden(X0,X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5222,plain,
    ( k1_relat_1(sK5) = sK2
    | r2_hidden(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3117,c_2712])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_579,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))
    | sK5 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_580,plain,
    ( ~ v1_funct_2(sK5,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_734,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))
    | sK2 != X0
    | sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_580])).

cnf(c_735,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))
    | sK5 = k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_734])).

cnf(c_3085,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != k1_xboole_0
    | k1_relat_1(sK5) = sK2
    | sK2 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3081,c_735])).

cnf(c_3106,plain,
    ( k1_relat_1(sK5) = sK2
    | sK2 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3085,c_3081])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_409,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_410,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_2701,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_411,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_2310,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2909,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_2310])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_550,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_551,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_2911,plain,
    ( v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_2912,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2911])).

cnf(c_3525,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2701,c_411,c_2909,c_2912])).

cnf(c_3526,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_3525])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_490,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_31])).

cnf(c_491,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK5)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_2700,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_3540,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2700])).

cnf(c_2,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
    | X1 = X3 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2719,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,k2_enumset1(X1,X1,X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4237,plain,
    ( sK3 = X0
    | r2_hidden(k4_tarski(X1,X0),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3540,c_2719])).

cnf(c_4621,plain,
    ( k1_funct_1(sK5,X0) = sK3
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3526,c_4237])).

cnf(c_4628,plain,
    ( k1_funct_1(sK5,X0) = sK3
    | sK2 = k1_xboole_0
    | sK5 = k1_xboole_0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3106,c_4621])).

cnf(c_6307,plain,
    ( k1_funct_1(sK5,sK4) = sK3
    | sK2 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2705,c_4628])).

cnf(c_29,negated_conjecture,
    ( k1_funct_1(sK5,sK4) != sK3 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_6308,plain,
    ( sK2 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6307,c_29])).

cnf(c_6324,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6308,c_2705])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_368,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_369,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_2704,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_6810,plain,
    ( sK5 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6324,c_2704])).

cnf(c_8781,plain,
    ( k1_relat_1(k1_xboole_0) = sK2
    | r2_hidden(sK3,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5222,c_6810])).

cnf(c_8784,plain,
    ( k1_relat_1(k1_xboole_0) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8781,c_2704])).

cnf(c_6827,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6810,c_3526])).

cnf(c_8514,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6827,c_2704])).

cnf(c_8785,plain,
    ( r2_hidden(X0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8784,c_8514])).

cnf(c_9586,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2705,c_8785])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.16/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/0.99  
% 3.16/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/0.99  
% 3.16/0.99  ------  iProver source info
% 3.16/0.99  
% 3.16/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.16/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/0.99  git: non_committed_changes: false
% 3.16/0.99  git: last_make_outside_of_git: false
% 3.16/0.99  
% 3.16/0.99  ------ 
% 3.16/0.99  
% 3.16/0.99  ------ Input Options
% 3.16/0.99  
% 3.16/0.99  --out_options                           all
% 3.16/0.99  --tptp_safe_out                         true
% 3.16/0.99  --problem_path                          ""
% 3.16/0.99  --include_path                          ""
% 3.16/0.99  --clausifier                            res/vclausify_rel
% 3.16/0.99  --clausifier_options                    --mode clausify
% 3.16/0.99  --stdin                                 false
% 3.16/0.99  --stats_out                             all
% 3.16/0.99  
% 3.16/0.99  ------ General Options
% 3.16/0.99  
% 3.16/0.99  --fof                                   false
% 3.16/0.99  --time_out_real                         305.
% 3.16/0.99  --time_out_virtual                      -1.
% 3.16/0.99  --symbol_type_check                     false
% 3.16/0.99  --clausify_out                          false
% 3.16/0.99  --sig_cnt_out                           false
% 3.16/0.99  --trig_cnt_out                          false
% 3.16/0.99  --trig_cnt_out_tolerance                1.
% 3.16/0.99  --trig_cnt_out_sk_spl                   false
% 3.16/0.99  --abstr_cl_out                          false
% 3.16/0.99  
% 3.16/0.99  ------ Global Options
% 3.16/0.99  
% 3.16/0.99  --schedule                              default
% 3.16/0.99  --add_important_lit                     false
% 3.16/0.99  --prop_solver_per_cl                    1000
% 3.16/0.99  --min_unsat_core                        false
% 3.16/0.99  --soft_assumptions                      false
% 3.16/0.99  --soft_lemma_size                       3
% 3.16/0.99  --prop_impl_unit_size                   0
% 3.16/0.99  --prop_impl_unit                        []
% 3.16/0.99  --share_sel_clauses                     true
% 3.16/0.99  --reset_solvers                         false
% 3.16/0.99  --bc_imp_inh                            [conj_cone]
% 3.16/0.99  --conj_cone_tolerance                   3.
% 3.16/0.99  --extra_neg_conj                        none
% 3.16/0.99  --large_theory_mode                     true
% 3.16/0.99  --prolific_symb_bound                   200
% 3.16/0.99  --lt_threshold                          2000
% 3.16/0.99  --clause_weak_htbl                      true
% 3.16/0.99  --gc_record_bc_elim                     false
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing Options
% 3.16/0.99  
% 3.16/0.99  --preprocessing_flag                    true
% 3.16/0.99  --time_out_prep_mult                    0.1
% 3.16/0.99  --splitting_mode                        input
% 3.16/0.99  --splitting_grd                         true
% 3.16/0.99  --splitting_cvd                         false
% 3.16/0.99  --splitting_cvd_svl                     false
% 3.16/0.99  --splitting_nvd                         32
% 3.16/0.99  --sub_typing                            true
% 3.16/0.99  --prep_gs_sim                           true
% 3.16/0.99  --prep_unflatten                        true
% 3.16/0.99  --prep_res_sim                          true
% 3.16/0.99  --prep_upred                            true
% 3.16/0.99  --prep_sem_filter                       exhaustive
% 3.16/0.99  --prep_sem_filter_out                   false
% 3.16/0.99  --pred_elim                             true
% 3.16/0.99  --res_sim_input                         true
% 3.16/0.99  --eq_ax_congr_red                       true
% 3.16/0.99  --pure_diseq_elim                       true
% 3.16/0.99  --brand_transform                       false
% 3.16/0.99  --non_eq_to_eq                          false
% 3.16/0.99  --prep_def_merge                        true
% 3.16/0.99  --prep_def_merge_prop_impl              false
% 3.16/0.99  --prep_def_merge_mbd                    true
% 3.16/0.99  --prep_def_merge_tr_red                 false
% 3.16/0.99  --prep_def_merge_tr_cl                  false
% 3.16/0.99  --smt_preprocessing                     true
% 3.16/0.99  --smt_ac_axioms                         fast
% 3.16/0.99  --preprocessed_out                      false
% 3.16/0.99  --preprocessed_stats                    false
% 3.16/0.99  
% 3.16/0.99  ------ Abstraction refinement Options
% 3.16/0.99  
% 3.16/0.99  --abstr_ref                             []
% 3.16/0.99  --abstr_ref_prep                        false
% 3.16/0.99  --abstr_ref_until_sat                   false
% 3.16/0.99  --abstr_ref_sig_restrict                funpre
% 3.16/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/0.99  --abstr_ref_under                       []
% 3.16/0.99  
% 3.16/0.99  ------ SAT Options
% 3.16/0.99  
% 3.16/0.99  --sat_mode                              false
% 3.16/0.99  --sat_fm_restart_options                ""
% 3.16/0.99  --sat_gr_def                            false
% 3.16/0.99  --sat_epr_types                         true
% 3.16/0.99  --sat_non_cyclic_types                  false
% 3.16/0.99  --sat_finite_models                     false
% 3.16/0.99  --sat_fm_lemmas                         false
% 3.16/0.99  --sat_fm_prep                           false
% 3.16/0.99  --sat_fm_uc_incr                        true
% 3.16/0.99  --sat_out_model                         small
% 3.16/0.99  --sat_out_clauses                       false
% 3.16/0.99  
% 3.16/0.99  ------ QBF Options
% 3.16/0.99  
% 3.16/0.99  --qbf_mode                              false
% 3.16/0.99  --qbf_elim_univ                         false
% 3.16/0.99  --qbf_dom_inst                          none
% 3.16/0.99  --qbf_dom_pre_inst                      false
% 3.16/0.99  --qbf_sk_in                             false
% 3.16/0.99  --qbf_pred_elim                         true
% 3.16/0.99  --qbf_split                             512
% 3.16/0.99  
% 3.16/0.99  ------ BMC1 Options
% 3.16/0.99  
% 3.16/0.99  --bmc1_incremental                      false
% 3.16/0.99  --bmc1_axioms                           reachable_all
% 3.16/0.99  --bmc1_min_bound                        0
% 3.16/0.99  --bmc1_max_bound                        -1
% 3.16/0.99  --bmc1_max_bound_default                -1
% 3.16/0.99  --bmc1_symbol_reachability              true
% 3.16/0.99  --bmc1_property_lemmas                  false
% 3.16/0.99  --bmc1_k_induction                      false
% 3.16/0.99  --bmc1_non_equiv_states                 false
% 3.16/0.99  --bmc1_deadlock                         false
% 3.16/0.99  --bmc1_ucm                              false
% 3.16/0.99  --bmc1_add_unsat_core                   none
% 3.16/0.99  --bmc1_unsat_core_children              false
% 3.16/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/0.99  --bmc1_out_stat                         full
% 3.16/0.99  --bmc1_ground_init                      false
% 3.16/0.99  --bmc1_pre_inst_next_state              false
% 3.16/0.99  --bmc1_pre_inst_state                   false
% 3.16/0.99  --bmc1_pre_inst_reach_state             false
% 3.16/0.99  --bmc1_out_unsat_core                   false
% 3.16/0.99  --bmc1_aig_witness_out                  false
% 3.16/0.99  --bmc1_verbose                          false
% 3.16/0.99  --bmc1_dump_clauses_tptp                false
% 3.16/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.16/0.99  --bmc1_dump_file                        -
% 3.16/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.16/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.16/0.99  --bmc1_ucm_extend_mode                  1
% 3.16/0.99  --bmc1_ucm_init_mode                    2
% 3.16/0.99  --bmc1_ucm_cone_mode                    none
% 3.16/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.16/0.99  --bmc1_ucm_relax_model                  4
% 3.16/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.16/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/0.99  --bmc1_ucm_layered_model                none
% 3.16/0.99  --bmc1_ucm_max_lemma_size               10
% 3.16/0.99  
% 3.16/0.99  ------ AIG Options
% 3.16/0.99  
% 3.16/0.99  --aig_mode                              false
% 3.16/0.99  
% 3.16/0.99  ------ Instantiation Options
% 3.16/0.99  
% 3.16/0.99  --instantiation_flag                    true
% 3.16/0.99  --inst_sos_flag                         false
% 3.16/0.99  --inst_sos_phase                        true
% 3.16/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/0.99  --inst_lit_sel_side                     num_symb
% 3.16/0.99  --inst_solver_per_active                1400
% 3.16/0.99  --inst_solver_calls_frac                1.
% 3.16/0.99  --inst_passive_queue_type               priority_queues
% 3.16/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/0.99  --inst_passive_queues_freq              [25;2]
% 3.16/0.99  --inst_dismatching                      true
% 3.16/0.99  --inst_eager_unprocessed_to_passive     true
% 3.16/0.99  --inst_prop_sim_given                   true
% 3.16/0.99  --inst_prop_sim_new                     false
% 3.16/0.99  --inst_subs_new                         false
% 3.16/0.99  --inst_eq_res_simp                      false
% 3.16/0.99  --inst_subs_given                       false
% 3.16/0.99  --inst_orphan_elimination               true
% 3.16/0.99  --inst_learning_loop_flag               true
% 3.16/0.99  --inst_learning_start                   3000
% 3.16/0.99  --inst_learning_factor                  2
% 3.16/0.99  --inst_start_prop_sim_after_learn       3
% 3.16/0.99  --inst_sel_renew                        solver
% 3.16/0.99  --inst_lit_activity_flag                true
% 3.16/0.99  --inst_restr_to_given                   false
% 3.16/0.99  --inst_activity_threshold               500
% 3.16/0.99  --inst_out_proof                        true
% 3.16/0.99  
% 3.16/0.99  ------ Resolution Options
% 3.16/0.99  
% 3.16/0.99  --resolution_flag                       true
% 3.16/0.99  --res_lit_sel                           adaptive
% 3.16/0.99  --res_lit_sel_side                      none
% 3.16/0.99  --res_ordering                          kbo
% 3.16/0.99  --res_to_prop_solver                    active
% 3.16/0.99  --res_prop_simpl_new                    false
% 3.16/0.99  --res_prop_simpl_given                  true
% 3.16/0.99  --res_passive_queue_type                priority_queues
% 3.16/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/0.99  --res_passive_queues_freq               [15;5]
% 3.16/0.99  --res_forward_subs                      full
% 3.16/0.99  --res_backward_subs                     full
% 3.16/0.99  --res_forward_subs_resolution           true
% 3.16/0.99  --res_backward_subs_resolution          true
% 3.16/0.99  --res_orphan_elimination                true
% 3.16/0.99  --res_time_limit                        2.
% 3.16/0.99  --res_out_proof                         true
% 3.16/0.99  
% 3.16/0.99  ------ Superposition Options
% 3.16/0.99  
% 3.16/0.99  --superposition_flag                    true
% 3.16/0.99  --sup_passive_queue_type                priority_queues
% 3.16/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.16/0.99  --demod_completeness_check              fast
% 3.16/0.99  --demod_use_ground                      true
% 3.16/0.99  --sup_to_prop_solver                    passive
% 3.16/0.99  --sup_prop_simpl_new                    true
% 3.16/0.99  --sup_prop_simpl_given                  true
% 3.16/0.99  --sup_fun_splitting                     false
% 3.16/0.99  --sup_smt_interval                      50000
% 3.16/0.99  
% 3.16/0.99  ------ Superposition Simplification Setup
% 3.16/0.99  
% 3.16/0.99  --sup_indices_passive                   []
% 3.16/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_full_bw                           [BwDemod]
% 3.16/0.99  --sup_immed_triv                        [TrivRules]
% 3.16/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_immed_bw_main                     []
% 3.16/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.99  
% 3.16/0.99  ------ Combination Options
% 3.16/0.99  
% 3.16/0.99  --comb_res_mult                         3
% 3.16/0.99  --comb_sup_mult                         2
% 3.16/0.99  --comb_inst_mult                        10
% 3.16/0.99  
% 3.16/0.99  ------ Debug Options
% 3.16/0.99  
% 3.16/0.99  --dbg_backtrace                         false
% 3.16/0.99  --dbg_dump_prop_clauses                 false
% 3.16/0.99  --dbg_dump_prop_clauses_file            -
% 3.16/0.99  --dbg_out_stat                          false
% 3.16/0.99  ------ Parsing...
% 3.16/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/0.99  ------ Proving...
% 3.16/0.99  ------ Problem Properties 
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  clauses                                 27
% 3.16/0.99  conjectures                             2
% 3.16/0.99  EPR                                     7
% 3.16/0.99  Horn                                    23
% 3.16/0.99  unary                                   4
% 3.16/0.99  binary                                  11
% 3.16/0.99  lits                                    69
% 3.16/0.99  lits eq                                 29
% 3.16/0.99  fd_pure                                 0
% 3.16/0.99  fd_pseudo                               0
% 3.16/0.99  fd_cond                                 0
% 3.16/0.99  fd_pseudo_cond                          4
% 3.16/0.99  AC symbols                              0
% 3.16/0.99  
% 3.16/0.99  ------ Schedule dynamic 5 is on 
% 3.16/0.99  
% 3.16/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  ------ 
% 3.16/0.99  Current options:
% 3.16/0.99  ------ 
% 3.16/0.99  
% 3.16/0.99  ------ Input Options
% 3.16/0.99  
% 3.16/0.99  --out_options                           all
% 3.16/0.99  --tptp_safe_out                         true
% 3.16/0.99  --problem_path                          ""
% 3.16/0.99  --include_path                          ""
% 3.16/0.99  --clausifier                            res/vclausify_rel
% 3.16/0.99  --clausifier_options                    --mode clausify
% 3.16/0.99  --stdin                                 false
% 3.16/0.99  --stats_out                             all
% 3.16/1.00  
% 3.16/1.00  ------ General Options
% 3.16/1.00  
% 3.16/1.00  --fof                                   false
% 3.16/1.00  --time_out_real                         305.
% 3.16/1.00  --time_out_virtual                      -1.
% 3.16/1.00  --symbol_type_check                     false
% 3.16/1.00  --clausify_out                          false
% 3.16/1.00  --sig_cnt_out                           false
% 3.16/1.00  --trig_cnt_out                          false
% 3.16/1.00  --trig_cnt_out_tolerance                1.
% 3.16/1.00  --trig_cnt_out_sk_spl                   false
% 3.16/1.00  --abstr_cl_out                          false
% 3.16/1.00  
% 3.16/1.00  ------ Global Options
% 3.16/1.00  
% 3.16/1.00  --schedule                              default
% 3.16/1.00  --add_important_lit                     false
% 3.16/1.00  --prop_solver_per_cl                    1000
% 3.16/1.00  --min_unsat_core                        false
% 3.16/1.00  --soft_assumptions                      false
% 3.16/1.00  --soft_lemma_size                       3
% 3.16/1.00  --prop_impl_unit_size                   0
% 3.16/1.00  --prop_impl_unit                        []
% 3.16/1.00  --share_sel_clauses                     true
% 3.16/1.00  --reset_solvers                         false
% 3.16/1.00  --bc_imp_inh                            [conj_cone]
% 3.16/1.00  --conj_cone_tolerance                   3.
% 3.16/1.00  --extra_neg_conj                        none
% 3.16/1.00  --large_theory_mode                     true
% 3.16/1.00  --prolific_symb_bound                   200
% 3.16/1.00  --lt_threshold                          2000
% 3.16/1.00  --clause_weak_htbl                      true
% 3.16/1.00  --gc_record_bc_elim                     false
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing Options
% 3.16/1.00  
% 3.16/1.00  --preprocessing_flag                    true
% 3.16/1.00  --time_out_prep_mult                    0.1
% 3.16/1.00  --splitting_mode                        input
% 3.16/1.00  --splitting_grd                         true
% 3.16/1.00  --splitting_cvd                         false
% 3.16/1.00  --splitting_cvd_svl                     false
% 3.16/1.00  --splitting_nvd                         32
% 3.16/1.00  --sub_typing                            true
% 3.16/1.00  --prep_gs_sim                           true
% 3.16/1.00  --prep_unflatten                        true
% 3.16/1.00  --prep_res_sim                          true
% 3.16/1.00  --prep_upred                            true
% 3.16/1.00  --prep_sem_filter                       exhaustive
% 3.16/1.00  --prep_sem_filter_out                   false
% 3.16/1.00  --pred_elim                             true
% 3.16/1.00  --res_sim_input                         true
% 3.16/1.00  --eq_ax_congr_red                       true
% 3.16/1.00  --pure_diseq_elim                       true
% 3.16/1.00  --brand_transform                       false
% 3.16/1.00  --non_eq_to_eq                          false
% 3.16/1.00  --prep_def_merge                        true
% 3.16/1.00  --prep_def_merge_prop_impl              false
% 3.16/1.00  --prep_def_merge_mbd                    true
% 3.16/1.00  --prep_def_merge_tr_red                 false
% 3.16/1.00  --prep_def_merge_tr_cl                  false
% 3.16/1.00  --smt_preprocessing                     true
% 3.16/1.00  --smt_ac_axioms                         fast
% 3.16/1.00  --preprocessed_out                      false
% 3.16/1.00  --preprocessed_stats                    false
% 3.16/1.00  
% 3.16/1.00  ------ Abstraction refinement Options
% 3.16/1.00  
% 3.16/1.00  --abstr_ref                             []
% 3.16/1.00  --abstr_ref_prep                        false
% 3.16/1.00  --abstr_ref_until_sat                   false
% 3.16/1.00  --abstr_ref_sig_restrict                funpre
% 3.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/1.00  --abstr_ref_under                       []
% 3.16/1.00  
% 3.16/1.00  ------ SAT Options
% 3.16/1.00  
% 3.16/1.00  --sat_mode                              false
% 3.16/1.00  --sat_fm_restart_options                ""
% 3.16/1.00  --sat_gr_def                            false
% 3.16/1.00  --sat_epr_types                         true
% 3.16/1.00  --sat_non_cyclic_types                  false
% 3.16/1.00  --sat_finite_models                     false
% 3.16/1.00  --sat_fm_lemmas                         false
% 3.16/1.00  --sat_fm_prep                           false
% 3.16/1.00  --sat_fm_uc_incr                        true
% 3.16/1.00  --sat_out_model                         small
% 3.16/1.00  --sat_out_clauses                       false
% 3.16/1.00  
% 3.16/1.00  ------ QBF Options
% 3.16/1.00  
% 3.16/1.00  --qbf_mode                              false
% 3.16/1.00  --qbf_elim_univ                         false
% 3.16/1.00  --qbf_dom_inst                          none
% 3.16/1.00  --qbf_dom_pre_inst                      false
% 3.16/1.00  --qbf_sk_in                             false
% 3.16/1.00  --qbf_pred_elim                         true
% 3.16/1.00  --qbf_split                             512
% 3.16/1.00  
% 3.16/1.00  ------ BMC1 Options
% 3.16/1.00  
% 3.16/1.00  --bmc1_incremental                      false
% 3.16/1.00  --bmc1_axioms                           reachable_all
% 3.16/1.00  --bmc1_min_bound                        0
% 3.16/1.00  --bmc1_max_bound                        -1
% 3.16/1.00  --bmc1_max_bound_default                -1
% 3.16/1.00  --bmc1_symbol_reachability              true
% 3.16/1.00  --bmc1_property_lemmas                  false
% 3.16/1.00  --bmc1_k_induction                      false
% 3.16/1.00  --bmc1_non_equiv_states                 false
% 3.16/1.00  --bmc1_deadlock                         false
% 3.16/1.00  --bmc1_ucm                              false
% 3.16/1.00  --bmc1_add_unsat_core                   none
% 3.16/1.00  --bmc1_unsat_core_children              false
% 3.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/1.00  --bmc1_out_stat                         full
% 3.16/1.00  --bmc1_ground_init                      false
% 3.16/1.00  --bmc1_pre_inst_next_state              false
% 3.16/1.00  --bmc1_pre_inst_state                   false
% 3.16/1.00  --bmc1_pre_inst_reach_state             false
% 3.16/1.00  --bmc1_out_unsat_core                   false
% 3.16/1.00  --bmc1_aig_witness_out                  false
% 3.16/1.00  --bmc1_verbose                          false
% 3.16/1.00  --bmc1_dump_clauses_tptp                false
% 3.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.16/1.00  --bmc1_dump_file                        -
% 3.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.16/1.00  --bmc1_ucm_extend_mode                  1
% 3.16/1.00  --bmc1_ucm_init_mode                    2
% 3.16/1.00  --bmc1_ucm_cone_mode                    none
% 3.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.16/1.00  --bmc1_ucm_relax_model                  4
% 3.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/1.00  --bmc1_ucm_layered_model                none
% 3.16/1.00  --bmc1_ucm_max_lemma_size               10
% 3.16/1.00  
% 3.16/1.00  ------ AIG Options
% 3.16/1.00  
% 3.16/1.00  --aig_mode                              false
% 3.16/1.00  
% 3.16/1.00  ------ Instantiation Options
% 3.16/1.00  
% 3.16/1.00  --instantiation_flag                    true
% 3.16/1.00  --inst_sos_flag                         false
% 3.16/1.00  --inst_sos_phase                        true
% 3.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel_side                     none
% 3.16/1.00  --inst_solver_per_active                1400
% 3.16/1.00  --inst_solver_calls_frac                1.
% 3.16/1.00  --inst_passive_queue_type               priority_queues
% 3.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/1.00  --inst_passive_queues_freq              [25;2]
% 3.16/1.00  --inst_dismatching                      true
% 3.16/1.00  --inst_eager_unprocessed_to_passive     true
% 3.16/1.00  --inst_prop_sim_given                   true
% 3.16/1.00  --inst_prop_sim_new                     false
% 3.16/1.00  --inst_subs_new                         false
% 3.16/1.00  --inst_eq_res_simp                      false
% 3.16/1.00  --inst_subs_given                       false
% 3.16/1.00  --inst_orphan_elimination               true
% 3.16/1.00  --inst_learning_loop_flag               true
% 3.16/1.00  --inst_learning_start                   3000
% 3.16/1.00  --inst_learning_factor                  2
% 3.16/1.00  --inst_start_prop_sim_after_learn       3
% 3.16/1.00  --inst_sel_renew                        solver
% 3.16/1.00  --inst_lit_activity_flag                true
% 3.16/1.00  --inst_restr_to_given                   false
% 3.16/1.00  --inst_activity_threshold               500
% 3.16/1.00  --inst_out_proof                        true
% 3.16/1.00  
% 3.16/1.00  ------ Resolution Options
% 3.16/1.00  
% 3.16/1.00  --resolution_flag                       false
% 3.16/1.00  --res_lit_sel                           adaptive
% 3.16/1.00  --res_lit_sel_side                      none
% 3.16/1.00  --res_ordering                          kbo
% 3.16/1.00  --res_to_prop_solver                    active
% 3.16/1.00  --res_prop_simpl_new                    false
% 3.16/1.00  --res_prop_simpl_given                  true
% 3.16/1.00  --res_passive_queue_type                priority_queues
% 3.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/1.00  --res_passive_queues_freq               [15;5]
% 3.16/1.00  --res_forward_subs                      full
% 3.16/1.00  --res_backward_subs                     full
% 3.16/1.00  --res_forward_subs_resolution           true
% 3.16/1.00  --res_backward_subs_resolution          true
% 3.16/1.00  --res_orphan_elimination                true
% 3.16/1.00  --res_time_limit                        2.
% 3.16/1.00  --res_out_proof                         true
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Options
% 3.16/1.00  
% 3.16/1.00  --superposition_flag                    true
% 3.16/1.00  --sup_passive_queue_type                priority_queues
% 3.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.16/1.00  --demod_completeness_check              fast
% 3.16/1.00  --demod_use_ground                      true
% 3.16/1.00  --sup_to_prop_solver                    passive
% 3.16/1.00  --sup_prop_simpl_new                    true
% 3.16/1.00  --sup_prop_simpl_given                  true
% 3.16/1.00  --sup_fun_splitting                     false
% 3.16/1.00  --sup_smt_interval                      50000
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Simplification Setup
% 3.16/1.00  
% 3.16/1.00  --sup_indices_passive                   []
% 3.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_full_bw                           [BwDemod]
% 3.16/1.00  --sup_immed_triv                        [TrivRules]
% 3.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_immed_bw_main                     []
% 3.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  
% 3.16/1.00  ------ Combination Options
% 3.16/1.00  
% 3.16/1.00  --comb_res_mult                         3
% 3.16/1.00  --comb_sup_mult                         2
% 3.16/1.00  --comb_inst_mult                        10
% 3.16/1.00  
% 3.16/1.00  ------ Debug Options
% 3.16/1.00  
% 3.16/1.00  --dbg_backtrace                         false
% 3.16/1.00  --dbg_dump_prop_clauses                 false
% 3.16/1.00  --dbg_dump_prop_clauses_file            -
% 3.16/1.00  --dbg_out_stat                          false
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  ------ Proving...
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  % SZS status Theorem for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00   Resolution empty clause
% 3.16/1.00  
% 3.16/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  fof(f13,conjecture,(
% 3.16/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f14,negated_conjecture,(
% 3.16/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.16/1.00    inference(negated_conjecture,[],[f13])).
% 3.16/1.00  
% 3.16/1.00  fof(f24,plain,(
% 3.16/1.00    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 3.16/1.00    inference(ennf_transformation,[],[f14])).
% 3.16/1.00  
% 3.16/1.00  fof(f25,plain,(
% 3.16/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 3.16/1.00    inference(flattening,[],[f24])).
% 3.16/1.00  
% 3.16/1.00  fof(f39,plain,(
% 3.16/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK5,sK4) != sK3 & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5))),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f40,plain,(
% 3.16/1.00    k1_funct_1(sK5,sK4) != sK3 & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5)),
% 3.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f39])).
% 3.16/1.00  
% 3.16/1.00  fof(f76,plain,(
% 3.16/1.00    r2_hidden(sK4,sK2)),
% 3.16/1.00    inference(cnf_transformation,[],[f40])).
% 3.16/1.00  
% 3.16/1.00  fof(f74,plain,(
% 3.16/1.00    v1_funct_2(sK5,sK2,k1_tarski(sK3))),
% 3.16/1.00    inference(cnf_transformation,[],[f40])).
% 3.16/1.00  
% 3.16/1.00  fof(f2,axiom,(
% 3.16/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f42,plain,(
% 3.16/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f2])).
% 3.16/1.00  
% 3.16/1.00  fof(f3,axiom,(
% 3.16/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f43,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f3])).
% 3.16/1.00  
% 3.16/1.00  fof(f4,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f44,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f4])).
% 3.16/1.00  
% 3.16/1.00  fof(f78,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.16/1.00    inference(definition_unfolding,[],[f43,f44])).
% 3.16/1.00  
% 3.16/1.00  fof(f79,plain,(
% 3.16/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.16/1.00    inference(definition_unfolding,[],[f42,f78])).
% 3.16/1.00  
% 3.16/1.00  fof(f84,plain,(
% 3.16/1.00    v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3))),
% 3.16/1.00    inference(definition_unfolding,[],[f74,f79])).
% 3.16/1.00  
% 3.16/1.00  fof(f12,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f22,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(ennf_transformation,[],[f12])).
% 3.16/1.00  
% 3.16/1.00  fof(f23,plain,(
% 3.16/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(flattening,[],[f22])).
% 3.16/1.00  
% 3.16/1.00  fof(f38,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(nnf_transformation,[],[f23])).
% 3.16/1.00  
% 3.16/1.00  fof(f67,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f38])).
% 3.16/1.00  
% 3.16/1.00  fof(f75,plain,(
% 3.16/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 3.16/1.00    inference(cnf_transformation,[],[f40])).
% 3.16/1.00  
% 3.16/1.00  fof(f83,plain,(
% 3.16/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))),
% 3.16/1.00    inference(definition_unfolding,[],[f75,f79])).
% 3.16/1.00  
% 3.16/1.00  fof(f11,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f21,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(ennf_transformation,[],[f11])).
% 3.16/1.00  
% 3.16/1.00  fof(f66,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f21])).
% 3.16/1.00  
% 3.16/1.00  fof(f6,axiom,(
% 3.16/1.00    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f15,plain,(
% 3.16/1.00    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 3.16/1.00    inference(ennf_transformation,[],[f6])).
% 3.16/1.00  
% 3.16/1.00  fof(f26,plain,(
% 3.16/1.00    ! [X3,X2,X1,X0,X4] : (sP0(X3,X2,X1,X0,X4) <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 3.16/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.16/1.00  
% 3.16/1.00  fof(f27,plain,(
% 3.16/1.00    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> sP0(X3,X2,X1,X0,X4))),
% 3.16/1.00    inference(definition_folding,[],[f15,f26])).
% 3.16/1.00  
% 3.16/1.00  fof(f35,plain,(
% 3.16/1.00    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ~sP0(X3,X2,X1,X0,X4)) & (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 3.16/1.00    inference(nnf_transformation,[],[f27])).
% 3.16/1.00  
% 3.16/1.00  fof(f58,plain,(
% 3.16/1.00    ( ! [X4,X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 3.16/1.00    inference(cnf_transformation,[],[f35])).
% 3.16/1.00  
% 3.16/1.00  fof(f90,plain,(
% 3.16/1.00    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,k2_enumset1(X0,X1,X2,X3))) )),
% 3.16/1.00    inference(equality_resolution,[],[f58])).
% 3.16/1.00  
% 3.16/1.00  fof(f30,plain,(
% 3.16/1.00    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 3.16/1.00    inference(nnf_transformation,[],[f26])).
% 3.16/1.00  
% 3.16/1.00  fof(f31,plain,(
% 3.16/1.00    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 3.16/1.00    inference(flattening,[],[f30])).
% 3.16/1.00  
% 3.16/1.00  fof(f32,plain,(
% 3.16/1.00    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 3.16/1.00    inference(rectify,[],[f31])).
% 3.16/1.00  
% 3.16/1.00  fof(f33,plain,(
% 3.16/1.00    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4))) => (((sK1(X0,X1,X2,X3,X4) != X0 & sK1(X0,X1,X2,X3,X4) != X1 & sK1(X0,X1,X2,X3,X4) != X2 & sK1(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK1(X0,X1,X2,X3,X4),X4)) & (sK1(X0,X1,X2,X3,X4) = X0 | sK1(X0,X1,X2,X3,X4) = X1 | sK1(X0,X1,X2,X3,X4) = X2 | sK1(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK1(X0,X1,X2,X3,X4),X4))))),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f34,plain,(
% 3.16/1.00    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | (((sK1(X0,X1,X2,X3,X4) != X0 & sK1(X0,X1,X2,X3,X4) != X1 & sK1(X0,X1,X2,X3,X4) != X2 & sK1(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK1(X0,X1,X2,X3,X4),X4)) & (sK1(X0,X1,X2,X3,X4) = X0 | sK1(X0,X1,X2,X3,X4) = X1 | sK1(X0,X1,X2,X3,X4) = X2 | sK1(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK1(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 3.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 3.16/1.00  
% 3.16/1.00  fof(f52,plain,(
% 3.16/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X0 != X6 | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f34])).
% 3.16/1.00  
% 3.16/1.00  fof(f86,plain,(
% 3.16/1.00    ( ! [X6,X4,X2,X3,X1] : (r2_hidden(X6,X4) | ~sP0(X6,X1,X2,X3,X4)) )),
% 3.16/1.00    inference(equality_resolution,[],[f52])).
% 3.16/1.00  
% 3.16/1.00  fof(f71,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f38])).
% 3.16/1.00  
% 3.16/1.00  fof(f94,plain,(
% 3.16/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.16/1.00    inference(equality_resolution,[],[f71])).
% 3.16/1.00  
% 3.16/1.00  fof(f8,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f17,plain,(
% 3.16/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.16/1.00    inference(ennf_transformation,[],[f8])).
% 3.16/1.00  
% 3.16/1.00  fof(f18,plain,(
% 3.16/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.16/1.00    inference(flattening,[],[f17])).
% 3.16/1.00  
% 3.16/1.00  fof(f36,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.16/1.00    inference(nnf_transformation,[],[f18])).
% 3.16/1.00  
% 3.16/1.00  fof(f37,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.16/1.00    inference(flattening,[],[f36])).
% 3.16/1.00  
% 3.16/1.00  fof(f63,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f37])).
% 3.16/1.00  
% 3.16/1.00  fof(f91,plain,(
% 3.16/1.00    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.16/1.00    inference(equality_resolution,[],[f63])).
% 3.16/1.00  
% 3.16/1.00  fof(f73,plain,(
% 3.16/1.00    v1_funct_1(sK5)),
% 3.16/1.00    inference(cnf_transformation,[],[f40])).
% 3.16/1.00  
% 3.16/1.00  fof(f10,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f20,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(ennf_transformation,[],[f10])).
% 3.16/1.00  
% 3.16/1.00  fof(f65,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f20])).
% 3.16/1.00  
% 3.16/1.00  fof(f7,axiom,(
% 3.16/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f16,plain,(
% 3.16/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.16/1.00    inference(ennf_transformation,[],[f7])).
% 3.16/1.00  
% 3.16/1.00  fof(f60,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f16])).
% 3.16/1.00  
% 3.16/1.00  fof(f5,axiom,(
% 3.16/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f28,plain,(
% 3.16/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 3.16/1.00    inference(nnf_transformation,[],[f5])).
% 3.16/1.00  
% 3.16/1.00  fof(f29,plain,(
% 3.16/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 3.16/1.00    inference(flattening,[],[f28])).
% 3.16/1.00  
% 3.16/1.00  fof(f46,plain,(
% 3.16/1.00    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f29])).
% 3.16/1.00  
% 3.16/1.00  fof(f81,plain,(
% 3.16/1.00    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))) )),
% 3.16/1.00    inference(definition_unfolding,[],[f46,f79])).
% 3.16/1.00  
% 3.16/1.00  fof(f77,plain,(
% 3.16/1.00    k1_funct_1(sK5,sK4) != sK3),
% 3.16/1.00    inference(cnf_transformation,[],[f40])).
% 3.16/1.00  
% 3.16/1.00  fof(f1,axiom,(
% 3.16/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f41,plain,(
% 3.16/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f1])).
% 3.16/1.00  
% 3.16/1.00  fof(f9,axiom,(
% 3.16/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f19,plain,(
% 3.16/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.16/1.00    inference(ennf_transformation,[],[f9])).
% 3.16/1.00  
% 3.16/1.00  fof(f64,plain,(
% 3.16/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f19])).
% 3.16/1.00  
% 3.16/1.00  cnf(c_30,negated_conjecture,
% 3.16/1.00      ( r2_hidden(sK4,sK2) ),
% 3.16/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2705,plain,
% 3.16/1.00      ( r2_hidden(sK4,sK2) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_32,negated_conjecture,
% 3.16/1.00      ( v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 3.16/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_28,plain,
% 3.16/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.16/1.00      | k1_xboole_0 = X2 ),
% 3.16/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_31,negated_conjecture,
% 3.16/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
% 3.16/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_505,plain,
% 3.16/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.16/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.16/1.00      | sK5 != X0
% 3.16/1.00      | k1_xboole_0 = X2 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_31]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_506,plain,
% 3.16/1.00      ( ~ v1_funct_2(sK5,X0,X1)
% 3.16/1.00      | k1_relset_1(X0,X1,sK5) = X0
% 3.16/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.16/1.00      | k1_xboole_0 = X1 ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_505]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_723,plain,
% 3.16/1.00      ( k2_enumset1(sK3,sK3,sK3,sK3) != X0
% 3.16/1.00      | k1_relset_1(X1,X0,sK5) = X1
% 3.16/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
% 3.16/1.00      | sK2 != X1
% 3.16/1.00      | sK5 != sK5
% 3.16/1.00      | k1_xboole_0 = X0 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_32,c_506]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_724,plain,
% 3.16/1.00      ( k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = sK2
% 3.16/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))
% 3.16/1.00      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_723]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1471,plain,
% 3.16/1.00      ( k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = sK2
% 3.16/1.00      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.16/1.00      inference(equality_resolution_simp,[status(thm)],[c_724]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_22,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_541,plain,
% 3.16/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.16/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.16/1.00      | sK5 != X2 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_542,plain,
% 3.16/1.00      ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
% 3.16/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_541]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2924,plain,
% 3.16/1.00      ( k1_relset_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK5) = k1_relat_1(sK5) ),
% 3.16/1.00      inference(equality_resolution,[status(thm)],[c_542]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3081,plain,
% 3.16/1.00      ( k2_enumset1(sK3,sK3,sK3,sK3) = k1_xboole_0 | k1_relat_1(sK5) = sK2 ),
% 3.16/1.00      inference(demodulation,[status(thm)],[c_1471,c_2924]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_15,plain,
% 3.16/1.00      ( sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0)) ),
% 3.16/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2706,plain,
% 3.16/1.00      ( sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0)) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3117,plain,
% 3.16/1.00      ( k1_relat_1(sK5) = sK2
% 3.16/1.00      | sP0(sK3,sK3,sK3,sK3,k1_xboole_0) = iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3081,c_2706]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_9,plain,
% 3.16/1.00      ( ~ sP0(X0,X1,X2,X3,X4) | r2_hidden(X0,X4) ),
% 3.16/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2712,plain,
% 3.16/1.00      ( sP0(X0,X1,X2,X3,X4) != iProver_top | r2_hidden(X0,X4) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5222,plain,
% 3.16/1.00      ( k1_relat_1(sK5) = sK2 | r2_hidden(sK3,k1_xboole_0) = iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3117,c_2712]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_24,plain,
% 3.16/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.16/1.00      | k1_xboole_0 = X1
% 3.16/1.00      | k1_xboole_0 = X0 ),
% 3.16/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_579,plain,
% 3.16/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.16/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))
% 3.16/1.00      | sK5 != X0
% 3.16/1.00      | k1_xboole_0 = X0
% 3.16/1.00      | k1_xboole_0 = X1 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_580,plain,
% 3.16/1.00      ( ~ v1_funct_2(sK5,X0,k1_xboole_0)
% 3.16/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))
% 3.16/1.00      | k1_xboole_0 = X0
% 3.16/1.00      | k1_xboole_0 = sK5 ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_579]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_734,plain,
% 3.16/1.00      ( k2_enumset1(sK3,sK3,sK3,sK3) != k1_xboole_0
% 3.16/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))
% 3.16/1.00      | sK2 != X0
% 3.16/1.00      | sK5 != sK5
% 3.16/1.00      | sK5 = k1_xboole_0
% 3.16/1.00      | k1_xboole_0 = X0 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_32,c_580]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_735,plain,
% 3.16/1.00      ( k2_enumset1(sK3,sK3,sK3,sK3) != k1_xboole_0
% 3.16/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))
% 3.16/1.00      | sK5 = k1_xboole_0
% 3.16/1.00      | k1_xboole_0 = sK2 ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_734]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3085,plain,
% 3.16/1.00      ( k2_enumset1(sK3,sK3,sK3,sK3) != k1_xboole_0
% 3.16/1.00      | k1_relat_1(sK5) = sK2
% 3.16/1.00      | sK2 = k1_xboole_0
% 3.16/1.00      | sK5 = k1_xboole_0 ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3081,c_735]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3106,plain,
% 3.16/1.00      ( k1_relat_1(sK5) = sK2 | sK2 = k1_xboole_0 | sK5 = k1_xboole_0 ),
% 3.16/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3085,c_3081]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_17,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.16/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.16/1.00      | ~ v1_relat_1(X1)
% 3.16/1.00      | ~ v1_funct_1(X1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_33,negated_conjecture,
% 3.16/1.00      ( v1_funct_1(sK5) ),
% 3.16/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_409,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.16/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.16/1.00      | ~ v1_relat_1(X1)
% 3.16/1.00      | sK5 != X1 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_410,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 3.16/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
% 3.16/1.00      | ~ v1_relat_1(sK5) ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_409]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2701,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.16/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 3.16/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_411,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.16/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 3.16/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2310,plain,( X0 = X0 ),theory(equality) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2909,plain,
% 3.16/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_2310]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_21,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_550,plain,
% 3.16/1.00      ( v1_relat_1(X0)
% 3.16/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.16/1.00      | sK5 != X0 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_551,plain,
% 3.16/1.00      ( v1_relat_1(sK5)
% 3.16/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_550]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2911,plain,
% 3.16/1.00      ( v1_relat_1(sK5)
% 3.16/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_551]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2912,plain,
% 3.16/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))
% 3.16/1.00      | v1_relat_1(sK5) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2911]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3525,plain,
% 3.16/1.00      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 3.16/1.00      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_2701,c_411,c_2909,c_2912]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3526,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.16/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top ),
% 3.16/1.00      inference(renaming,[status(thm)],[c_3525]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_16,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.16/1.00      | ~ r2_hidden(X2,X0)
% 3.16/1.00      | r2_hidden(X2,X1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_490,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,X1)
% 3.16/1.00      | r2_hidden(X0,X2)
% 3.16/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(X2)
% 3.16/1.00      | sK5 != X1 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_31]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_491,plain,
% 3.16/1.00      ( r2_hidden(X0,X1)
% 3.16/1.00      | ~ r2_hidden(X0,sK5)
% 3.16/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(X1) ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_490]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2700,plain,
% 3.16/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(X0)
% 3.16/1.00      | r2_hidden(X1,X0) = iProver_top
% 3.16/1.00      | r2_hidden(X1,sK5) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3540,plain,
% 3.16/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top
% 3.16/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 3.16/1.00      inference(equality_resolution,[status(thm)],[c_2700]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2,plain,
% 3.16/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
% 3.16/1.00      | X1 = X3 ),
% 3.16/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2719,plain,
% 3.16/1.00      ( X0 = X1
% 3.16/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,k2_enumset1(X1,X1,X1,X1))) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4237,plain,
% 3.16/1.00      ( sK3 = X0 | r2_hidden(k4_tarski(X1,X0),sK5) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3540,c_2719]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4621,plain,
% 3.16/1.00      ( k1_funct_1(sK5,X0) = sK3
% 3.16/1.00      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3526,c_4237]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4628,plain,
% 3.16/1.00      ( k1_funct_1(sK5,X0) = sK3
% 3.16/1.00      | sK2 = k1_xboole_0
% 3.16/1.00      | sK5 = k1_xboole_0
% 3.16/1.00      | r2_hidden(X0,sK2) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3106,c_4621]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6307,plain,
% 3.16/1.00      ( k1_funct_1(sK5,sK4) = sK3 | sK2 = k1_xboole_0 | sK5 = k1_xboole_0 ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_2705,c_4628]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_29,negated_conjecture,
% 3.16/1.00      ( k1_funct_1(sK5,sK4) != sK3 ),
% 3.16/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6308,plain,
% 3.16/1.00      ( sK2 = k1_xboole_0 | sK5 = k1_xboole_0 ),
% 3.16/1.00      inference(global_propositional_subsumption,[status(thm)],[c_6307,c_29]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6324,plain,
% 3.16/1.00      ( sK5 = k1_xboole_0 | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_6308,c_2705]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_0,plain,
% 3.16/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_20,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_368,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_369,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_368]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2704,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_369]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6810,plain,
% 3.16/1.00      ( sK5 = k1_xboole_0 ),
% 3.16/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_6324,c_2704]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_8781,plain,
% 3.16/1.00      ( k1_relat_1(k1_xboole_0) = sK2
% 3.16/1.00      | r2_hidden(sK3,k1_xboole_0) = iProver_top ),
% 3.16/1.00      inference(light_normalisation,[status(thm)],[c_5222,c_6810]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_8784,plain,
% 3.16/1.00      ( k1_relat_1(k1_xboole_0) = sK2 ),
% 3.16/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_8781,c_2704]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6827,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 3.16/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 3.16/1.00      inference(demodulation,[status(thm)],[c_6810,c_3526]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_8514,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 3.16/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_6827,c_2704]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_8785,plain,
% 3.16/1.00      ( r2_hidden(X0,sK2) != iProver_top ),
% 3.16/1.00      inference(demodulation,[status(thm)],[c_8784,c_8514]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_9586,plain,
% 3.16/1.00      ( $false ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_2705,c_8785]) ).
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  ------                               Statistics
% 3.16/1.00  
% 3.16/1.00  ------ General
% 3.16/1.00  
% 3.16/1.00  abstr_ref_over_cycles:                  0
% 3.16/1.00  abstr_ref_under_cycles:                 0
% 3.16/1.00  gc_basic_clause_elim:                   0
% 3.16/1.00  forced_gc_time:                         0
% 3.16/1.00  parsing_time:                           0.01
% 3.16/1.00  unif_index_cands_time:                  0.
% 3.16/1.00  unif_index_add_time:                    0.
% 3.16/1.00  orderings_time:                         0.
% 3.16/1.00  out_proof_time:                         0.009
% 3.16/1.00  total_time:                             0.286
% 3.16/1.00  num_of_symbols:                         51
% 3.16/1.00  num_of_terms:                           10676
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing
% 3.16/1.00  
% 3.16/1.00  num_of_splits:                          0
% 3.16/1.00  num_of_split_atoms:                     0
% 3.16/1.00  num_of_reused_defs:                     0
% 3.16/1.00  num_eq_ax_congr_red:                    35
% 3.16/1.00  num_of_sem_filtered_clauses:            1
% 3.16/1.00  num_of_subtypes:                        0
% 3.16/1.00  monotx_restored_types:                  0
% 3.16/1.00  sat_num_of_epr_types:                   0
% 3.16/1.00  sat_num_of_non_cyclic_types:            0
% 3.16/1.00  sat_guarded_non_collapsed_types:        0
% 3.16/1.00  num_pure_diseq_elim:                    0
% 3.16/1.00  simp_replaced_by:                       0
% 3.16/1.00  res_preprocessed:                       140
% 3.16/1.00  prep_upred:                             0
% 3.16/1.00  prep_unflattend:                        93
% 3.16/1.00  smt_new_axioms:                         0
% 3.16/1.00  pred_elim_cands:                        3
% 3.16/1.00  pred_elim:                              4
% 3.16/1.00  pred_elim_cl:                           7
% 3.16/1.00  pred_elim_cycles:                       9
% 3.16/1.00  merged_defs:                            0
% 3.16/1.00  merged_defs_ncl:                        0
% 3.16/1.00  bin_hyper_res:                          0
% 3.16/1.00  prep_cycles:                            4
% 3.16/1.00  pred_elim_time:                         0.026
% 3.16/1.00  splitting_time:                         0.
% 3.16/1.00  sem_filter_time:                        0.
% 3.16/1.00  monotx_time:                            0.001
% 3.16/1.00  subtype_inf_time:                       0.
% 3.16/1.00  
% 3.16/1.00  ------ Problem properties
% 3.16/1.00  
% 3.16/1.00  clauses:                                27
% 3.16/1.00  conjectures:                            2
% 3.16/1.00  epr:                                    7
% 3.16/1.00  horn:                                   23
% 3.16/1.00  ground:                                 5
% 3.16/1.00  unary:                                  4
% 3.16/1.00  binary:                                 11
% 3.16/1.00  lits:                                   69
% 3.16/1.00  lits_eq:                                29
% 3.16/1.00  fd_pure:                                0
% 3.16/1.00  fd_pseudo:                              0
% 3.16/1.00  fd_cond:                                0
% 3.16/1.00  fd_pseudo_cond:                         4
% 3.16/1.00  ac_symbols:                             0
% 3.16/1.00  
% 3.16/1.00  ------ Propositional Solver
% 3.16/1.00  
% 3.16/1.00  prop_solver_calls:                      27
% 3.16/1.00  prop_fast_solver_calls:                 1318
% 3.16/1.00  smt_solver_calls:                       0
% 3.16/1.00  smt_fast_solver_calls:                  0
% 3.16/1.00  prop_num_of_clauses:                    3237
% 3.16/1.00  prop_preprocess_simplified:             10729
% 3.16/1.00  prop_fo_subsumed:                       36
% 3.16/1.00  prop_solver_time:                       0.
% 3.16/1.00  smt_solver_time:                        0.
% 3.16/1.00  smt_fast_solver_time:                   0.
% 3.16/1.00  prop_fast_solver_time:                  0.
% 3.16/1.00  prop_unsat_core_time:                   0.
% 3.16/1.00  
% 3.16/1.00  ------ QBF
% 3.16/1.00  
% 3.16/1.00  qbf_q_res:                              0
% 3.16/1.00  qbf_num_tautologies:                    0
% 3.16/1.00  qbf_prep_cycles:                        0
% 3.16/1.00  
% 3.16/1.00  ------ BMC1
% 3.16/1.00  
% 3.16/1.00  bmc1_current_bound:                     -1
% 3.16/1.00  bmc1_last_solved_bound:                 -1
% 3.16/1.00  bmc1_unsat_core_size:                   -1
% 3.16/1.00  bmc1_unsat_core_parents_size:           -1
% 3.16/1.00  bmc1_merge_next_fun:                    0
% 3.16/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.16/1.00  
% 3.16/1.00  ------ Instantiation
% 3.16/1.00  
% 3.16/1.00  inst_num_of_clauses:                    912
% 3.16/1.00  inst_num_in_passive:                    455
% 3.16/1.00  inst_num_in_active:                     255
% 3.16/1.00  inst_num_in_unprocessed:                202
% 3.16/1.00  inst_num_of_loops:                      310
% 3.16/1.00  inst_num_of_learning_restarts:          0
% 3.16/1.00  inst_num_moves_active_passive:          54
% 3.16/1.00  inst_lit_activity:                      0
% 3.16/1.00  inst_lit_activity_moves:                0
% 3.16/1.00  inst_num_tautologies:                   0
% 3.16/1.00  inst_num_prop_implied:                  0
% 3.16/1.00  inst_num_existing_simplified:           0
% 3.16/1.00  inst_num_eq_res_simplified:             0
% 3.16/1.00  inst_num_child_elim:                    0
% 3.16/1.00  inst_num_of_dismatching_blockings:      395
% 3.16/1.00  inst_num_of_non_proper_insts:           830
% 3.16/1.00  inst_num_of_duplicates:                 0
% 3.16/1.00  inst_inst_num_from_inst_to_res:         0
% 3.16/1.00  inst_dismatching_checking_time:         0.
% 3.16/1.00  
% 3.16/1.00  ------ Resolution
% 3.16/1.00  
% 3.16/1.00  res_num_of_clauses:                     0
% 3.16/1.00  res_num_in_passive:                     0
% 3.16/1.00  res_num_in_active:                      0
% 3.16/1.00  res_num_of_loops:                       144
% 3.16/1.00  res_forward_subset_subsumed:            151
% 3.16/1.00  res_backward_subset_subsumed:           0
% 3.16/1.00  res_forward_subsumed:                   0
% 3.16/1.00  res_backward_subsumed:                  0
% 3.16/1.00  res_forward_subsumption_resolution:     0
% 3.16/1.00  res_backward_subsumption_resolution:    0
% 3.16/1.00  res_clause_to_clause_subsumption:       1372
% 3.16/1.00  res_orphan_elimination:                 0
% 3.16/1.00  res_tautology_del:                      29
% 3.16/1.00  res_num_eq_res_simplified:              1
% 3.16/1.00  res_num_sel_changes:                    0
% 3.16/1.00  res_moves_from_active_to_pass:          0
% 3.16/1.00  
% 3.16/1.00  ------ Superposition
% 3.16/1.00  
% 3.16/1.00  sup_time_total:                         0.
% 3.16/1.00  sup_time_generating:                    0.
% 3.16/1.00  sup_time_sim_full:                      0.
% 3.16/1.00  sup_time_sim_immed:                     0.
% 3.16/1.00  
% 3.16/1.00  sup_num_of_clauses:                     49
% 3.16/1.00  sup_num_in_active:                      32
% 3.16/1.00  sup_num_in_passive:                     17
% 3.16/1.00  sup_num_of_loops:                       61
% 3.16/1.00  sup_fw_superposition:                   46
% 3.16/1.00  sup_bw_superposition:                   65
% 3.16/1.00  sup_immediate_simplified:               53
% 3.16/1.00  sup_given_eliminated:                   0
% 3.16/1.00  comparisons_done:                       0
% 3.16/1.00  comparisons_avoided:                    12
% 3.16/1.00  
% 3.16/1.00  ------ Simplifications
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  sim_fw_subset_subsumed:                 17
% 3.16/1.00  sim_bw_subset_subsumed:                 10
% 3.16/1.00  sim_fw_subsumed:                        34
% 3.16/1.00  sim_bw_subsumed:                        0
% 3.16/1.00  sim_fw_subsumption_res:                 5
% 3.16/1.00  sim_bw_subsumption_res:                 0
% 3.16/1.00  sim_tautology_del:                      2
% 3.16/1.00  sim_eq_tautology_del:                   11
% 3.16/1.00  sim_eq_res_simp:                        0
% 3.16/1.00  sim_fw_demodulated:                     1
% 3.16/1.00  sim_bw_demodulated:                     29
% 3.16/1.00  sim_light_normalised:                   3
% 3.16/1.00  sim_joinable_taut:                      0
% 3.16/1.00  sim_joinable_simp:                      0
% 3.16/1.00  sim_ac_normalised:                      0
% 3.16/1.00  sim_smt_subsumption:                    0
% 3.16/1.00  
%------------------------------------------------------------------------------
