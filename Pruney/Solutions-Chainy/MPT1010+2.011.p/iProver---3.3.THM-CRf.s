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

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 273 expanded)
%              Number of clauses        :   61 (  70 expanded)
%              Number of leaves         :   25 (  62 expanded)
%              Depth                    :   20
%              Number of atoms          :  616 (1074 expanded)
%              Number of equality atoms :  294 ( 431 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   22 (   2 average)
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

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f58,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK10,sK9) != sK8
      & r2_hidden(sK9,sK7)
      & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
      & v1_funct_2(sK10,sK7,k1_tarski(sK8))
      & v1_funct_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( k1_funct_1(sK10,sK9) != sK8
    & r2_hidden(sK9,sK7)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    & v1_funct_2(sK10,sK7,k1_tarski(sK8))
    & v1_funct_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f33,f58])).

fof(f107,plain,(
    r2_hidden(sK9,sK7) ),
    inference(cnf_transformation,[],[f59])).

fof(f106,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f109,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f110,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f65,f109])).

fof(f115,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8)))) ),
    inference(definition_unfolding,[],[f106,f110])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f105,plain,(
    v1_funct_2(sK10,sK7,k1_tarski(sK8)) ),
    inference(cnf_transformation,[],[f59])).

fof(f116,plain,(
    v1_funct_2(sK10,sK7,k2_enumset1(sK8,sK8,sK8,sK8)) ),
    inference(definition_unfolding,[],[f105,f110])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f34,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( sP0(X3,X2,X1,X0,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3,X4) != X0
            & sK3(X0,X1,X2,X3,X4) != X1
            & sK3(X0,X1,X2,X3,X4) != X2
            & sK3(X0,X1,X2,X3,X4) != X3 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4),X4) )
        & ( sK3(X0,X1,X2,X3,X4) = X0
          | sK3(X0,X1,X2,X3,X4) = X1
          | sK3(X0,X1,X2,X3,X4) = X2
          | sK3(X0,X1,X2,X3,X4) = X3
          | r2_hidden(sK3(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( ( ( sK3(X0,X1,X2,X3,X4) != X0
              & sK3(X0,X1,X2,X3,X4) != X1
              & sK3(X0,X1,X2,X3,X4) != X2
              & sK3(X0,X1,X2,X3,X4) != X3 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4),X4) )
          & ( sK3(X0,X1,X2,X3,X4) = X0
            | sK3(X0,X1,X2,X3,X4) = X1
            | sK3(X0,X1,X2,X3,X4) = X2
            | sK3(X0,X1,X2,X3,X4) = X3
            | r2_hidden(sK3(X0,X1,X2,X3,X4),X4) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X3 != X6
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f125,plain,(
    ! [X6,X4,X2,X0,X1] :
      ( r2_hidden(X6,X4)
      | ~ sP0(X0,X1,X2,X6,X4) ) ),
    inference(equality_resolution,[],[f73])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP0(X3,X2,X1,X0,X4) ) ),
    inference(definition_folding,[],[f20,f34])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP0(X3,X2,X1,X0,X4) )
      & ( sP0(X3,X2,X1,X0,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] : sP0(X3,X2,X1,X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f82])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f55,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) = X2
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f52,f55,f54,f53])).

fof(f90,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f127,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f128,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f127])).

fof(f104,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f59])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f120,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f114,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f61,f110])).

fof(f119,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f114])).

fof(f108,plain,(
    k1_funct_1(sK10,sK9) != sK8 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_42,negated_conjecture,
    ( r2_hidden(sK9,sK7) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_27597,plain,
    ( r2_hidden(sK9,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8)))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_27596,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_33,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_24,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_599,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_33,c_24])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_603,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_599,c_32])).

cnf(c_604,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_603])).

cnf(c_27592,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_27941,plain,
    ( r1_tarski(k2_relat_1(sK10),k2_enumset1(sK8,sK8,sK8,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27596,c_27592])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_44,negated_conjecture,
    ( v1_funct_2(sK10,sK7,k2_enumset1(sK8,sK8,sK8,sK8)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1433,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK8,sK8,sK8,sK8) != X2
    | k1_relset_1(X1,X2,X0) = X1
    | sK7 != X1
    | sK10 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_44])).

cnf(c_1434,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8))))
    | k1_relset_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8),sK10) = sK7
    | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
    inference(unflattening,[status(thm)],[c_1433])).

cnf(c_1436,plain,
    ( k1_relset_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8),sK10) = sK7
    | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1434,c_43])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_27598,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_27996,plain,
    ( k1_relset_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8),sK10) = k1_relat_1(sK10) ),
    inference(superposition,[status(thm)],[c_27596,c_27598])).

cnf(c_28036,plain,
    ( k2_enumset1(sK8,sK8,sK8,sK8) = k1_xboole_0
    | k1_relat_1(sK10) = sK7 ),
    inference(superposition,[status(thm)],[c_1436,c_27996])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | r2_hidden(X3,X4) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_20,plain,
    ( sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_2134,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | k2_enumset1(X4,X5,X7,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_2135,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(unflattening,[status(thm)],[c_2134])).

cnf(c_27588,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X1,X2,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2135])).

cnf(c_31,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_27600,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_27793,plain,
    ( r1_tarski(k2_enumset1(X0,X1,X2,X3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27588,c_27600])).

cnf(c_28066,plain,
    ( k1_relat_1(sK10) = sK7
    | r1_tarski(k1_xboole_0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_28036,c_27793])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_27608,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_28127,plain,
    ( k1_relat_1(sK10) = sK7 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_28066,c_27608])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_686,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_45])).

cnf(c_687,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK10))
    | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10))
    | ~ v1_relat_1(sK10) ),
    inference(unflattening,[status(thm)],[c_686])).

cnf(c_27591,plain,
    ( r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
    | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_48,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_688,plain,
    ( r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
    | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_27744,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8))))
    | v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_27745,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8)))) != iProver_top
    | v1_relat_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27744])).

cnf(c_27761,plain,
    ( r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK10)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27591,c_48,c_688,c_27745])).

cnf(c_27762,plain,
    ( r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
    | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top ),
    inference(renaming,[status(thm)],[c_27761])).

cnf(c_28131,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_28127,c_27762])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_27606,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_22,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_27601,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_27893,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_27606,c_27601])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_27602,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_28257,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_27893,c_27602])).

cnf(c_28628,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k1_funct_1(sK10,X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(sK10),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_28131,c_28257])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_27607,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_28761,plain,
    ( k1_funct_1(sK10,X0) = X1
    | r2_hidden(X0,sK7) != iProver_top
    | r1_tarski(k2_relat_1(sK10),k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28628,c_27607])).

cnf(c_29043,plain,
    ( k1_funct_1(sK10,X0) = sK8
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_27941,c_28761])).

cnf(c_29091,plain,
    ( k1_funct_1(sK10,sK9) = sK8 ),
    inference(superposition,[status(thm)],[c_27597,c_29043])).

cnf(c_41,negated_conjecture,
    ( k1_funct_1(sK10,sK9) != sK8 ),
    inference(cnf_transformation,[],[f108])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29091,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.67/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/1.49  
% 7.67/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.67/1.49  
% 7.67/1.49  ------  iProver source info
% 7.67/1.49  
% 7.67/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.67/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.67/1.49  git: non_committed_changes: false
% 7.67/1.49  git: last_make_outside_of_git: false
% 7.67/1.49  
% 7.67/1.49  ------ 
% 7.67/1.49  ------ Parsing...
% 7.67/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  ------ Proving...
% 7.67/1.49  ------ Problem Properties 
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  clauses                                 39
% 7.67/1.49  conjectures                             4
% 7.67/1.49  EPR                                     9
% 7.67/1.49  Horn                                    31
% 7.67/1.49  unary                                   6
% 7.67/1.49  binary                                  14
% 7.67/1.49  lits                                    102
% 7.67/1.49  lits eq                                 35
% 7.67/1.49  fd_pure                                 0
% 7.67/1.49  fd_pseudo                               0
% 7.67/1.49  fd_cond                                 3
% 7.67/1.49  fd_pseudo_cond                          6
% 7.67/1.49  AC symbols                              0
% 7.67/1.49  
% 7.67/1.49  ------ Input Options Time Limit: Unbounded
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing...
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.67/1.49  Current options:
% 7.67/1.49  ------ 
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing...
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing...
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing...
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  % SZS status Theorem for theBenchmark.p
% 7.67/1.49  
% 7.67/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.67/1.49  
% 7.67/1.49  fof(f17,conjecture,(
% 7.67/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f18,negated_conjecture,(
% 7.67/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 7.67/1.49    inference(negated_conjecture,[],[f17])).
% 7.67/1.49  
% 7.67/1.49  fof(f32,plain,(
% 7.67/1.49    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 7.67/1.49    inference(ennf_transformation,[],[f18])).
% 7.67/1.49  
% 7.67/1.49  fof(f33,plain,(
% 7.67/1.49    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 7.67/1.49    inference(flattening,[],[f32])).
% 7.67/1.49  
% 7.67/1.49  fof(f58,plain,(
% 7.67/1.49    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK10,sK9) != sK8 & r2_hidden(sK9,sK7) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) & v1_funct_2(sK10,sK7,k1_tarski(sK8)) & v1_funct_1(sK10))),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f59,plain,(
% 7.67/1.49    k1_funct_1(sK10,sK9) != sK8 & r2_hidden(sK9,sK7) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) & v1_funct_2(sK10,sK7,k1_tarski(sK8)) & v1_funct_1(sK10)),
% 7.67/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f33,f58])).
% 7.67/1.49  
% 7.67/1.49  fof(f107,plain,(
% 7.67/1.49    r2_hidden(sK9,sK7)),
% 7.67/1.49    inference(cnf_transformation,[],[f59])).
% 7.67/1.49  
% 7.67/1.49  fof(f106,plain,(
% 7.67/1.49    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))),
% 7.67/1.49    inference(cnf_transformation,[],[f59])).
% 7.67/1.49  
% 7.67/1.49  fof(f3,axiom,(
% 7.67/1.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f65,plain,(
% 7.67/1.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f3])).
% 7.67/1.49  
% 7.67/1.49  fof(f4,axiom,(
% 7.67/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f66,plain,(
% 7.67/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f4])).
% 7.67/1.49  
% 7.67/1.49  fof(f5,axiom,(
% 7.67/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f67,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f5])).
% 7.67/1.49  
% 7.67/1.49  fof(f109,plain,(
% 7.67/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.67/1.49    inference(definition_unfolding,[],[f66,f67])).
% 7.67/1.49  
% 7.67/1.49  fof(f110,plain,(
% 7.67/1.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.67/1.49    inference(definition_unfolding,[],[f65,f109])).
% 7.67/1.49  
% 7.67/1.49  fof(f115,plain,(
% 7.67/1.49    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8))))),
% 7.67/1.49    inference(definition_unfolding,[],[f106,f110])).
% 7.67/1.49  
% 7.67/1.49  fof(f14,axiom,(
% 7.67/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f19,plain,(
% 7.67/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.67/1.49    inference(pure_predicate_removal,[],[f14])).
% 7.67/1.49  
% 7.67/1.49  fof(f28,plain,(
% 7.67/1.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.49    inference(ennf_transformation,[],[f19])).
% 7.67/1.49  
% 7.67/1.49  fof(f96,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.49    inference(cnf_transformation,[],[f28])).
% 7.67/1.49  
% 7.67/1.49  fof(f10,axiom,(
% 7.67/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f23,plain,(
% 7.67/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.67/1.49    inference(ennf_transformation,[],[f10])).
% 7.67/1.49  
% 7.67/1.49  fof(f50,plain,(
% 7.67/1.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.67/1.49    inference(nnf_transformation,[],[f23])).
% 7.67/1.49  
% 7.67/1.49  fof(f86,plain,(
% 7.67/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f50])).
% 7.67/1.49  
% 7.67/1.49  fof(f13,axiom,(
% 7.67/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f27,plain,(
% 7.67/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.49    inference(ennf_transformation,[],[f13])).
% 7.67/1.49  
% 7.67/1.49  fof(f95,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.49    inference(cnf_transformation,[],[f27])).
% 7.67/1.49  
% 7.67/1.49  fof(f16,axiom,(
% 7.67/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f30,plain,(
% 7.67/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.49    inference(ennf_transformation,[],[f16])).
% 7.67/1.49  
% 7.67/1.49  fof(f31,plain,(
% 7.67/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.49    inference(flattening,[],[f30])).
% 7.67/1.49  
% 7.67/1.49  fof(f57,plain,(
% 7.67/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.49    inference(nnf_transformation,[],[f31])).
% 7.67/1.49  
% 7.67/1.49  fof(f98,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.49    inference(cnf_transformation,[],[f57])).
% 7.67/1.49  
% 7.67/1.49  fof(f105,plain,(
% 7.67/1.49    v1_funct_2(sK10,sK7,k1_tarski(sK8))),
% 7.67/1.49    inference(cnf_transformation,[],[f59])).
% 7.67/1.49  
% 7.67/1.49  fof(f116,plain,(
% 7.67/1.49    v1_funct_2(sK10,sK7,k2_enumset1(sK8,sK8,sK8,sK8))),
% 7.67/1.49    inference(definition_unfolding,[],[f105,f110])).
% 7.67/1.49  
% 7.67/1.49  fof(f15,axiom,(
% 7.67/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f29,plain,(
% 7.67/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.49    inference(ennf_transformation,[],[f15])).
% 7.67/1.49  
% 7.67/1.49  fof(f97,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.49    inference(cnf_transformation,[],[f29])).
% 7.67/1.49  
% 7.67/1.49  fof(f34,plain,(
% 7.67/1.49    ! [X3,X2,X1,X0,X4] : (sP0(X3,X2,X1,X0,X4) <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 7.67/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.67/1.49  
% 7.67/1.49  fof(f44,plain,(
% 7.67/1.49    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 7.67/1.49    inference(nnf_transformation,[],[f34])).
% 7.67/1.49  
% 7.67/1.49  fof(f45,plain,(
% 7.67/1.49    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 7.67/1.49    inference(flattening,[],[f44])).
% 7.67/1.49  
% 7.67/1.49  fof(f46,plain,(
% 7.67/1.49    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 7.67/1.49    inference(rectify,[],[f45])).
% 7.67/1.49  
% 7.67/1.49  fof(f47,plain,(
% 7.67/1.49    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4))) => (((sK3(X0,X1,X2,X3,X4) != X0 & sK3(X0,X1,X2,X3,X4) != X1 & sK3(X0,X1,X2,X3,X4) != X2 & sK3(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK3(X0,X1,X2,X3,X4),X4)) & (sK3(X0,X1,X2,X3,X4) = X0 | sK3(X0,X1,X2,X3,X4) = X1 | sK3(X0,X1,X2,X3,X4) = X2 | sK3(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK3(X0,X1,X2,X3,X4),X4))))),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f48,plain,(
% 7.67/1.49    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | (((sK3(X0,X1,X2,X3,X4) != X0 & sK3(X0,X1,X2,X3,X4) != X1 & sK3(X0,X1,X2,X3,X4) != X2 & sK3(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK3(X0,X1,X2,X3,X4),X4)) & (sK3(X0,X1,X2,X3,X4) = X0 | sK3(X0,X1,X2,X3,X4) = X1 | sK3(X0,X1,X2,X3,X4) = X2 | sK3(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK3(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 7.67/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).
% 7.67/1.49  
% 7.67/1.49  fof(f73,plain,(
% 7.67/1.49    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X3 != X6 | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f48])).
% 7.67/1.49  
% 7.67/1.49  fof(f125,plain,(
% 7.67/1.49    ( ! [X6,X4,X2,X0,X1] : (r2_hidden(X6,X4) | ~sP0(X0,X1,X2,X6,X4)) )),
% 7.67/1.49    inference(equality_resolution,[],[f73])).
% 7.67/1.49  
% 7.67/1.49  fof(f7,axiom,(
% 7.67/1.49    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f20,plain,(
% 7.67/1.49    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 7.67/1.49    inference(ennf_transformation,[],[f7])).
% 7.67/1.49  
% 7.67/1.49  fof(f35,plain,(
% 7.67/1.49    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> sP0(X3,X2,X1,X0,X4))),
% 7.67/1.49    inference(definition_folding,[],[f20,f34])).
% 7.67/1.49  
% 7.67/1.49  fof(f49,plain,(
% 7.67/1.49    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ~sP0(X3,X2,X1,X0,X4)) & (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 7.67/1.49    inference(nnf_transformation,[],[f35])).
% 7.67/1.49  
% 7.67/1.49  fof(f82,plain,(
% 7.67/1.49    ( ! [X4,X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 7.67/1.49    inference(cnf_transformation,[],[f49])).
% 7.67/1.49  
% 7.67/1.49  fof(f126,plain,(
% 7.67/1.49    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,k2_enumset1(X0,X1,X2,X3))) )),
% 7.67/1.49    inference(equality_resolution,[],[f82])).
% 7.67/1.49  
% 7.67/1.49  fof(f12,axiom,(
% 7.67/1.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f26,plain,(
% 7.67/1.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.67/1.49    inference(ennf_transformation,[],[f12])).
% 7.67/1.49  
% 7.67/1.49  fof(f94,plain,(
% 7.67/1.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f26])).
% 7.67/1.49  
% 7.67/1.49  fof(f1,axiom,(
% 7.67/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f60,plain,(
% 7.67/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f1])).
% 7.67/1.49  
% 7.67/1.49  fof(f11,axiom,(
% 7.67/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f24,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.67/1.49    inference(ennf_transformation,[],[f11])).
% 7.67/1.49  
% 7.67/1.49  fof(f25,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.67/1.49    inference(flattening,[],[f24])).
% 7.67/1.49  
% 7.67/1.49  fof(f51,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.67/1.49    inference(nnf_transformation,[],[f25])).
% 7.67/1.49  
% 7.67/1.49  fof(f52,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.67/1.49    inference(rectify,[],[f51])).
% 7.67/1.49  
% 7.67/1.49  fof(f55,plain,(
% 7.67/1.49    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f54,plain,(
% 7.67/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1)) = X2 & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))) )),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f53,plain,(
% 7.67/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f56,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.67/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f52,f55,f54,f53])).
% 7.67/1.49  
% 7.67/1.49  fof(f90,plain,(
% 7.67/1.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f56])).
% 7.67/1.49  
% 7.67/1.49  fof(f127,plain,(
% 7.67/1.49    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.49    inference(equality_resolution,[],[f90])).
% 7.67/1.49  
% 7.67/1.49  fof(f128,plain,(
% 7.67/1.49    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.49    inference(equality_resolution,[],[f127])).
% 7.67/1.49  
% 7.67/1.49  fof(f104,plain,(
% 7.67/1.49    v1_funct_1(sK10)),
% 7.67/1.49    inference(cnf_transformation,[],[f59])).
% 7.67/1.49  
% 7.67/1.49  fof(f6,axiom,(
% 7.67/1.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f40,plain,(
% 7.67/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.67/1.49    inference(nnf_transformation,[],[f6])).
% 7.67/1.49  
% 7.67/1.49  fof(f41,plain,(
% 7.67/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.67/1.49    inference(rectify,[],[f40])).
% 7.67/1.49  
% 7.67/1.49  fof(f42,plain,(
% 7.67/1.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f43,plain,(
% 7.67/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.67/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 7.67/1.49  
% 7.67/1.49  fof(f69,plain,(
% 7.67/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 7.67/1.49    inference(cnf_transformation,[],[f43])).
% 7.67/1.49  
% 7.67/1.49  fof(f120,plain,(
% 7.67/1.49    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 7.67/1.49    inference(equality_resolution,[],[f69])).
% 7.67/1.49  
% 7.67/1.49  fof(f9,axiom,(
% 7.67/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f22,plain,(
% 7.67/1.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 7.67/1.49    inference(ennf_transformation,[],[f9])).
% 7.67/1.49  
% 7.67/1.49  fof(f85,plain,(
% 7.67/1.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f22])).
% 7.67/1.49  
% 7.67/1.49  fof(f8,axiom,(
% 7.67/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f21,plain,(
% 7.67/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.67/1.49    inference(ennf_transformation,[],[f8])).
% 7.67/1.49  
% 7.67/1.49  fof(f84,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.67/1.49    inference(cnf_transformation,[],[f21])).
% 7.67/1.49  
% 7.67/1.49  fof(f2,axiom,(
% 7.67/1.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f36,plain,(
% 7.67/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.67/1.49    inference(nnf_transformation,[],[f2])).
% 7.67/1.49  
% 7.67/1.49  fof(f37,plain,(
% 7.67/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.67/1.49    inference(rectify,[],[f36])).
% 7.67/1.49  
% 7.67/1.49  fof(f38,plain,(
% 7.67/1.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f39,plain,(
% 7.67/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.67/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 7.67/1.49  
% 7.67/1.49  fof(f61,plain,(
% 7.67/1.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.67/1.49    inference(cnf_transformation,[],[f39])).
% 7.67/1.49  
% 7.67/1.49  fof(f114,plain,(
% 7.67/1.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.67/1.49    inference(definition_unfolding,[],[f61,f110])).
% 7.67/1.49  
% 7.67/1.49  fof(f119,plain,(
% 7.67/1.49    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 7.67/1.49    inference(equality_resolution,[],[f114])).
% 7.67/1.49  
% 7.67/1.49  fof(f108,plain,(
% 7.67/1.49    k1_funct_1(sK10,sK9) != sK8),
% 7.67/1.49    inference(cnf_transformation,[],[f59])).
% 7.67/1.49  
% 7.67/1.49  cnf(c_42,negated_conjecture,
% 7.67/1.49      ( r2_hidden(sK9,sK7) ),
% 7.67/1.49      inference(cnf_transformation,[],[f107]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27597,plain,
% 7.67/1.49      ( r2_hidden(sK9,sK7) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_43,negated_conjecture,
% 7.67/1.49      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8)))) ),
% 7.67/1.49      inference(cnf_transformation,[],[f115]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27596,plain,
% 7.67/1.49      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8)))) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_33,plain,
% 7.67/1.49      ( v5_relat_1(X0,X1)
% 7.67/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.67/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24,plain,
% 7.67/1.49      ( ~ v5_relat_1(X0,X1)
% 7.67/1.49      | r1_tarski(k2_relat_1(X0),X1)
% 7.67/1.49      | ~ v1_relat_1(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_599,plain,
% 7.67/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.49      | r1_tarski(k2_relat_1(X0),X2)
% 7.67/1.49      | ~ v1_relat_1(X0) ),
% 7.67/1.49      inference(resolution,[status(thm)],[c_33,c_24]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_32,plain,
% 7.67/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.49      | v1_relat_1(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_603,plain,
% 7.67/1.49      ( r1_tarski(k2_relat_1(X0),X2)
% 7.67/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_599,c_32]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_604,plain,
% 7.67/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.49      | r1_tarski(k2_relat_1(X0),X2) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_603]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27592,plain,
% 7.67/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.67/1.49      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27941,plain,
% 7.67/1.49      ( r1_tarski(k2_relat_1(sK10),k2_enumset1(sK8,sK8,sK8,sK8)) = iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_27596,c_27592]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_40,plain,
% 7.67/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.67/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.67/1.49      | k1_xboole_0 = X2 ),
% 7.67/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_44,negated_conjecture,
% 7.67/1.49      ( v1_funct_2(sK10,sK7,k2_enumset1(sK8,sK8,sK8,sK8)) ),
% 7.67/1.49      inference(cnf_transformation,[],[f116]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1433,plain,
% 7.67/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.49      | k2_enumset1(sK8,sK8,sK8,sK8) != X2
% 7.67/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.67/1.49      | sK7 != X1
% 7.67/1.49      | sK10 != X0
% 7.67/1.49      | k1_xboole_0 = X2 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_40,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1434,plain,
% 7.67/1.49      ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8))))
% 7.67/1.49      | k1_relset_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8),sK10) = sK7
% 7.67/1.49      | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1433]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1436,plain,
% 7.67/1.49      ( k1_relset_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8),sK10) = sK7
% 7.67/1.49      | k1_xboole_0 = k2_enumset1(sK8,sK8,sK8,sK8) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1434,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_34,plain,
% 7.67/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27598,plain,
% 7.67/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.67/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27996,plain,
% 7.67/1.49      ( k1_relset_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8),sK10) = k1_relat_1(sK10) ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_27596,c_27598]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_28036,plain,
% 7.67/1.49      ( k2_enumset1(sK8,sK8,sK8,sK8) = k1_xboole_0
% 7.67/1.49      | k1_relat_1(sK10) = sK7 ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_1436,c_27996]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_17,plain,
% 7.67/1.49      ( ~ sP0(X0,X1,X2,X3,X4) | r2_hidden(X3,X4) ),
% 7.67/1.49      inference(cnf_transformation,[],[f125]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_20,plain,
% 7.67/1.49      ( sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0)) ),
% 7.67/1.49      inference(cnf_transformation,[],[f126]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2134,plain,
% 7.67/1.49      ( r2_hidden(X0,X1)
% 7.67/1.49      | X2 != X3
% 7.67/1.49      | X4 != X0
% 7.67/1.49      | X5 != X6
% 7.67/1.49      | X7 != X8
% 7.67/1.49      | k2_enumset1(X4,X5,X7,X2) != X1 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2135,plain,
% 7.67/1.49      ( r2_hidden(X0,k2_enumset1(X0,X1,X2,X3)) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_2134]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27588,plain,
% 7.67/1.49      ( r2_hidden(X0,k2_enumset1(X0,X1,X2,X3)) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_2135]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_31,negated_conjecture,
% 7.67/1.49      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27600,plain,
% 7.67/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.67/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27793,plain,
% 7.67/1.49      ( r1_tarski(k2_enumset1(X0,X1,X2,X3),X0) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_27588,c_27600]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_28066,plain,
% 7.67/1.49      ( k1_relat_1(sK10) = sK7
% 7.67/1.49      | r1_tarski(k1_xboole_0,sK8) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_28036,c_27793]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_0,plain,
% 7.67/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27608,plain,
% 7.67/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_28127,plain,
% 7.67/1.49      ( k1_relat_1(sK10) = sK7 ),
% 7.67/1.49      inference(forward_subsumption_resolution,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_28066,c_27608]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_28,plain,
% 7.67/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.67/1.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.67/1.49      | ~ v1_funct_1(X1)
% 7.67/1.49      | ~ v1_relat_1(X1) ),
% 7.67/1.49      inference(cnf_transformation,[],[f128]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_45,negated_conjecture,
% 7.67/1.49      ( v1_funct_1(sK10) ),
% 7.67/1.49      inference(cnf_transformation,[],[f104]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_686,plain,
% 7.67/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.67/1.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.67/1.49      | ~ v1_relat_1(X1)
% 7.67/1.49      | sK10 != X1 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_28,c_45]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_687,plain,
% 7.67/1.49      ( ~ r2_hidden(X0,k1_relat_1(sK10))
% 7.67/1.49      | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10))
% 7.67/1.49      | ~ v1_relat_1(sK10) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_686]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27591,plain,
% 7.67/1.49      ( r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
% 7.67/1.49      | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top
% 7.67/1.49      | v1_relat_1(sK10) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_687]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_48,plain,
% 7.67/1.49      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8)))) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_688,plain,
% 7.67/1.49      ( r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
% 7.67/1.49      | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top
% 7.67/1.49      | v1_relat_1(sK10) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_687]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27744,plain,
% 7.67/1.49      ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8))))
% 7.67/1.49      | v1_relat_1(sK10) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_32]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27745,plain,
% 7.67/1.49      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_enumset1(sK8,sK8,sK8,sK8)))) != iProver_top
% 7.67/1.49      | v1_relat_1(sK10) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_27744]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27761,plain,
% 7.67/1.49      ( r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top
% 7.67/1.49      | r2_hidden(X0,k1_relat_1(sK10)) != iProver_top ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_27591,c_48,c_688,c_27745]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27762,plain,
% 7.67/1.49      ( r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
% 7.67/1.49      | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_27761]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_28131,plain,
% 7.67/1.49      ( r2_hidden(X0,sK7) != iProver_top
% 7.67/1.49      | r2_hidden(k1_funct_1(sK10,X0),k2_relat_1(sK10)) = iProver_top ),
% 7.67/1.49      inference(demodulation,[status(thm)],[c_28127,c_27762]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_7,plain,
% 7.67/1.49      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.67/1.49      inference(cnf_transformation,[],[f120]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27606,plain,
% 7.67/1.49      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.67/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_22,plain,
% 7.67/1.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.67/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27601,plain,
% 7.67/1.49      ( m1_subset_1(X0,X1) = iProver_top
% 7.67/1.49      | r2_hidden(X0,X1) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27893,plain,
% 7.67/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.67/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_27606,c_27601]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_21,plain,
% 7.67/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.67/1.49      | ~ r2_hidden(X2,X0)
% 7.67/1.49      | r2_hidden(X2,X1) ),
% 7.67/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27602,plain,
% 7.67/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.67/1.49      | r2_hidden(X2,X0) != iProver_top
% 7.67/1.49      | r2_hidden(X2,X1) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_28257,plain,
% 7.67/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.67/1.49      | r2_hidden(X0,X2) = iProver_top
% 7.67/1.49      | r1_tarski(X1,X2) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_27893,c_27602]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_28628,plain,
% 7.67/1.49      ( r2_hidden(X0,sK7) != iProver_top
% 7.67/1.49      | r2_hidden(k1_funct_1(sK10,X0),X1) = iProver_top
% 7.67/1.49      | r1_tarski(k2_relat_1(sK10),X1) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_28131,c_28257]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_4,plain,
% 7.67/1.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 7.67/1.49      inference(cnf_transformation,[],[f119]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27607,plain,
% 7.67/1.49      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_28761,plain,
% 7.67/1.49      ( k1_funct_1(sK10,X0) = X1
% 7.67/1.49      | r2_hidden(X0,sK7) != iProver_top
% 7.67/1.49      | r1_tarski(k2_relat_1(sK10),k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_28628,c_27607]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_29043,plain,
% 7.67/1.49      ( k1_funct_1(sK10,X0) = sK8 | r2_hidden(X0,sK7) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_27941,c_28761]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_29091,plain,
% 7.67/1.49      ( k1_funct_1(sK10,sK9) = sK8 ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_27597,c_29043]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_41,negated_conjecture,
% 7.67/1.49      ( k1_funct_1(sK10,sK9) != sK8 ),
% 7.67/1.49      inference(cnf_transformation,[],[f108]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(contradiction,plain,
% 7.67/1.49      ( $false ),
% 7.67/1.49      inference(minisat,[status(thm)],[c_29091,c_41]) ).
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.67/1.49  
% 7.67/1.49  ------                               Statistics
% 7.67/1.49  
% 7.67/1.49  ------ Selected
% 7.67/1.49  
% 7.67/1.49  total_time:                             0.611
% 7.67/1.49  
%------------------------------------------------------------------------------
