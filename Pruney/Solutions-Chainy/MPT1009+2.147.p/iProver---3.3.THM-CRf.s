%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:57 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  178 (1608 expanded)
%              Number of clauses        :   82 ( 234 expanded)
%              Number of leaves         :   25 ( 431 expanded)
%              Depth                    :   22
%              Number of atoms          :  521 (3982 expanded)
%              Number of equality atoms :  299 (1986 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f38,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f39,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f52,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2)))
      & k1_xboole_0 != sK3
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK5,k1_tarski(sK2),sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2)))
    & k1_xboole_0 != sK3
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK5,k1_tarski(sK2),sK3)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f39,f52])).

fof(f99,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f103,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f102])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f103])).

fof(f105,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f104])).

fof(f106,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f105])).

fof(f107,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f106])).

fof(f113,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f99,f107])).

fof(f21,axiom,(
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
    inference(ennf_transformation,[],[f21])).

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

fof(f51,plain,(
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

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f98,plain,(
    v1_funct_2(sK5,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f114,plain,(
    v1_funct_2(sK5,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f98,f107])).

fof(f100,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( sP0(X4,X3,X2,X1,X0,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP0(X4,X3,X2,X1,X0,X5) ) ),
    inference(definition_folding,[],[f24,f40])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP0(X4,X3,X2,X1,X0,X5) )
      & ( sP0(X4,X3,X2,X1,X0,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f109,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f76,f103])).

fof(f122,plain,(
    ! [X4,X2,X0,X3,X1] : sP0(X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f109])).

fof(f44,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f45,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(flattening,[],[f44])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6
                & X4 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | X4 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X0 != X6
              & X1 != X6
              & X2 != X6
              & X3 != X6
              & X4 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X0 = X6
            | X1 = X6
            | X2 = X6
            | X3 = X6
            | X4 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK1(X0,X1,X2,X3,X4,X5) != X0
            & sK1(X0,X1,X2,X3,X4,X5) != X1
            & sK1(X0,X1,X2,X3,X4,X5) != X2
            & sK1(X0,X1,X2,X3,X4,X5) != X3
            & sK1(X0,X1,X2,X3,X4,X5) != X4 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK1(X0,X1,X2,X3,X4,X5) = X0
          | sK1(X0,X1,X2,X3,X4,X5) = X1
          | sK1(X0,X1,X2,X3,X4,X5) = X2
          | sK1(X0,X1,X2,X3,X4,X5) = X3
          | sK1(X0,X1,X2,X3,X4,X5) = X4
          | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ( ( ( sK1(X0,X1,X2,X3,X4,X5) != X0
              & sK1(X0,X1,X2,X3,X4,X5) != X1
              & sK1(X0,X1,X2,X3,X4,X5) != X2
              & sK1(X0,X1,X2,X3,X4,X5) != X3
              & sK1(X0,X1,X2,X3,X4,X5) != X4 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK1(X0,X1,X2,X3,X4,X5) = X0
            | sK1(X0,X1,X2,X3,X4,X5) = X1
            | sK1(X0,X1,X2,X3,X4,X5) = X2
            | sK1(X0,X1,X2,X3,X4,X5) = X3
            | sK1(X0,X1,X2,X3,X4,X5) = X4
            | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).

fof(f69,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X0 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f117,plain,(
    ! [X4,X2,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | ~ sP0(X7,X1,X2,X3,X4,X5) ) ),
    inference(equality_resolution,[],[f69])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f83,f107])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f81,f107])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f97,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f101,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2))) ),
    inference(cnf_transformation,[],[f53])).

fof(f112,plain,(
    ~ r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) ),
    inference(definition_unfolding,[],[f101,f107,f107])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f33])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f115,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1589,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1591,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2855,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK3 = k1_xboole_0
    | v1_funct_2(sK5,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_1591])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK5,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_37,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2069,plain,
    ( ~ v1_funct_2(sK5,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
    | k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_3544,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2855,c_39,c_38,c_37,c_2069])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1602,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3175,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1589,c_1602])).

cnf(c_3546,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK5) ),
    inference(light_normalisation,[status(thm)],[c_3544,c_3175])).

cnf(c_16,plain,
    ( sP0(X0,X1,X2,X3,X4,k6_enumset1(X4,X4,X4,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1609,plain,
    ( sP0(X0,X1,X2,X3,X4,k6_enumset1(X4,X4,X4,X4,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3570,plain,
    ( sP0(sK2,sK2,sK2,sK2,sK2,k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3546,c_1609])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | r2_hidden(X0,X5) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1616,plain,
    ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
    | r2_hidden(X0,X5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5338,plain,
    ( r2_hidden(sK2,k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3570,c_1616])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1604,plain,
    ( k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k11_relat_1(X0,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9140,plain,
    ( k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k11_relat_1(sK5,sK2)
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5338,c_1604])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1607,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2087,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_1607])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_17,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_267,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_268,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_267])).

cnf(c_343,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_19,c_268])).

cnf(c_1586,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_2285,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2087,c_1586])).

cnf(c_2051,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(resolution,[status(thm)],[c_18,c_38])).

cnf(c_2102,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | v1_relat_1(sK5) ),
    inference(resolution,[status(thm)],[c_343,c_2051])).

cnf(c_21,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2107,plain,
    ( v1_relat_1(sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2102,c_21])).

cnf(c_2108,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2107])).

cnf(c_2442,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2285,c_2108])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1606,plain,
    ( k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5953,plain,
    ( k9_relat_1(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k11_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_2442,c_1606])).

cnf(c_6473,plain,
    ( k9_relat_1(sK5,k1_relat_1(sK5)) = k11_relat_1(sK5,sK2) ),
    inference(superposition,[status(thm)],[c_3546,c_5953])).

cnf(c_3552,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3546,c_1589])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1597,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4351,plain,
    ( k7_relset_1(k1_relat_1(sK5),sK3,sK5,k1_relat_1(sK5)) = k2_relset_1(k1_relat_1(sK5),sK3,sK5) ),
    inference(superposition,[status(thm)],[c_3552,c_1597])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1601,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2570,plain,
    ( k2_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1589,c_1601])).

cnf(c_3550,plain,
    ( k2_relset_1(k1_relat_1(sK5),sK3,sK5) = k2_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_3546,c_2570])).

cnf(c_4353,plain,
    ( k7_relset_1(k1_relat_1(sK5),sK3,sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
    inference(light_normalisation,[status(thm)],[c_4351,c_3550])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1600,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3306,plain,
    ( k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1589,c_1600])).

cnf(c_3548,plain,
    ( k7_relset_1(k1_relat_1(sK5),sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(demodulation,[status(thm)],[c_3546,c_3306])).

cnf(c_5347,plain,
    ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4353,c_3548])).

cnf(c_6474,plain,
    ( k11_relat_1(sK5,sK2) = k2_relat_1(sK5) ),
    inference(light_normalisation,[status(thm)],[c_6473,c_5347])).

cnf(c_9141,plain,
    ( k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k2_relat_1(sK5)
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9140,c_6474])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_41,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_14334,plain,
    ( k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k2_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9141,c_41,c_2108])).

cnf(c_36,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1590,plain,
    ( r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3400,plain,
    ( r1_tarski(k9_relat_1(sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3306,c_1590])).

cnf(c_14337,plain,
    ( r1_tarski(k9_relat_1(sK5,sK4),k2_relat_1(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14334,c_3400])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1599,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7223,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3552,c_1599])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1623,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8121,plain,
    ( k7_relset_1(k1_relat_1(sK5),X0,sK5,X1) = k9_relat_1(sK5,X1)
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7223,c_1600])).

cnf(c_8661,plain,
    ( k7_relset_1(k1_relat_1(sK5),k2_relat_1(sK5),sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1623,c_8121])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1603,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10450,plain,
    ( m1_subset_1(k9_relat_1(sK5,X0),k1_zfmisc_1(k2_relat_1(sK5))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8661,c_1603])).

cnf(c_12406,plain,
    ( m1_subset_1(k9_relat_1(sK5,X0),k1_zfmisc_1(k2_relat_1(sK5))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7223,c_10450])).

cnf(c_2002,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_10435,plain,
    ( r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2002])).

cnf(c_10436,plain,
    ( r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10435])).

cnf(c_12528,plain,
    ( m1_subset_1(k9_relat_1(sK5,X0),k1_zfmisc_1(k2_relat_1(sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12406,c_10436])).

cnf(c_12537,plain,
    ( r1_tarski(k9_relat_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12528,c_1607])).

cnf(c_14356,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14337,c_12537])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:04:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.08/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.00  
% 4.08/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.08/1.00  
% 4.08/1.00  ------  iProver source info
% 4.08/1.00  
% 4.08/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.08/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.08/1.00  git: non_committed_changes: false
% 4.08/1.00  git: last_make_outside_of_git: false
% 4.08/1.00  
% 4.08/1.00  ------ 
% 4.08/1.00  ------ Parsing...
% 4.08/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.08/1.00  
% 4.08/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.08/1.00  
% 4.08/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.08/1.00  
% 4.08/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.08/1.00  ------ Proving...
% 4.08/1.00  ------ Problem Properties 
% 4.08/1.00  
% 4.08/1.00  
% 4.08/1.00  clauses                                 40
% 4.08/1.00  conjectures                             5
% 4.08/1.00  EPR                                     11
% 4.08/1.00  Horn                                    34
% 4.08/1.00  unary                                   8
% 4.08/1.00  binary                                  15
% 4.08/1.00  lits                                    101
% 4.08/1.00  lits eq                                 34
% 4.08/1.00  fd_pure                                 0
% 4.08/1.00  fd_pseudo                               0
% 4.08/1.00  fd_cond                                 3
% 4.08/1.00  fd_pseudo_cond                          3
% 4.08/1.00  AC symbols                              0
% 4.08/1.00  
% 4.08/1.00  ------ Input Options Time Limit: Unbounded
% 4.08/1.00  
% 4.08/1.00  
% 4.08/1.00  ------ 
% 4.08/1.00  Current options:
% 4.08/1.00  ------ 
% 4.08/1.00  
% 4.08/1.00  
% 4.08/1.00  
% 4.08/1.00  
% 4.08/1.00  ------ Proving...
% 4.08/1.00  
% 4.08/1.00  
% 4.08/1.00  % SZS status Theorem for theBenchmark.p
% 4.08/1.00  
% 4.08/1.00   Resolution empty clause
% 4.08/1.00  
% 4.08/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.08/1.00  
% 4.08/1.00  fof(f22,conjecture,(
% 4.08/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f23,negated_conjecture,(
% 4.08/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 4.08/1.00    inference(negated_conjecture,[],[f22])).
% 4.08/1.00  
% 4.08/1.00  fof(f38,plain,(
% 4.08/1.00    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 4.08/1.00    inference(ennf_transformation,[],[f23])).
% 4.08/1.00  
% 4.08/1.00  fof(f39,plain,(
% 4.08/1.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 4.08/1.00    inference(flattening,[],[f38])).
% 4.08/1.00  
% 4.08/1.00  fof(f52,plain,(
% 4.08/1.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2))) & k1_xboole_0 != sK3 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK5,k1_tarski(sK2),sK3) & v1_funct_1(sK5))),
% 4.08/1.00    introduced(choice_axiom,[])).
% 4.08/1.00  
% 4.08/1.00  fof(f53,plain,(
% 4.08/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2))) & k1_xboole_0 != sK3 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK5,k1_tarski(sK2),sK3) & v1_funct_1(sK5)),
% 4.08/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f39,f52])).
% 4.08/1.00  
% 4.08/1.00  fof(f99,plain,(
% 4.08/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 4.08/1.00    inference(cnf_transformation,[],[f53])).
% 4.08/1.00  
% 4.08/1.00  fof(f2,axiom,(
% 4.08/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f57,plain,(
% 4.08/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f2])).
% 4.08/1.00  
% 4.08/1.00  fof(f3,axiom,(
% 4.08/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f58,plain,(
% 4.08/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f3])).
% 4.08/1.00  
% 4.08/1.00  fof(f4,axiom,(
% 4.08/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f59,plain,(
% 4.08/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f4])).
% 4.08/1.00  
% 4.08/1.00  fof(f5,axiom,(
% 4.08/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f60,plain,(
% 4.08/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f5])).
% 4.08/1.00  
% 4.08/1.00  fof(f6,axiom,(
% 4.08/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f61,plain,(
% 4.08/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f6])).
% 4.08/1.00  
% 4.08/1.00  fof(f7,axiom,(
% 4.08/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f62,plain,(
% 4.08/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f7])).
% 4.08/1.00  
% 4.08/1.00  fof(f8,axiom,(
% 4.08/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f63,plain,(
% 4.08/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f8])).
% 4.08/1.00  
% 4.08/1.00  fof(f102,plain,(
% 4.08/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 4.08/1.00    inference(definition_unfolding,[],[f62,f63])).
% 4.08/1.00  
% 4.08/1.00  fof(f103,plain,(
% 4.08/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 4.08/1.00    inference(definition_unfolding,[],[f61,f102])).
% 4.08/1.00  
% 4.08/1.00  fof(f104,plain,(
% 4.08/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 4.08/1.00    inference(definition_unfolding,[],[f60,f103])).
% 4.08/1.00  
% 4.08/1.00  fof(f105,plain,(
% 4.08/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 4.08/1.00    inference(definition_unfolding,[],[f59,f104])).
% 4.08/1.00  
% 4.08/1.00  fof(f106,plain,(
% 4.08/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 4.08/1.00    inference(definition_unfolding,[],[f58,f105])).
% 4.08/1.00  
% 4.08/1.00  fof(f107,plain,(
% 4.08/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 4.08/1.00    inference(definition_unfolding,[],[f57,f106])).
% 4.08/1.00  
% 4.08/1.00  fof(f113,plain,(
% 4.08/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))),
% 4.08/1.00    inference(definition_unfolding,[],[f99,f107])).
% 4.08/1.00  
% 4.08/1.00  fof(f21,axiom,(
% 4.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f36,plain,(
% 4.08/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.00    inference(ennf_transformation,[],[f21])).
% 4.08/1.00  
% 4.08/1.00  fof(f37,plain,(
% 4.08/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.00    inference(flattening,[],[f36])).
% 4.08/1.00  
% 4.08/1.00  fof(f51,plain,(
% 4.08/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.00    inference(nnf_transformation,[],[f37])).
% 4.08/1.00  
% 4.08/1.00  fof(f91,plain,(
% 4.08/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.08/1.00    inference(cnf_transformation,[],[f51])).
% 4.08/1.00  
% 4.08/1.00  fof(f98,plain,(
% 4.08/1.00    v1_funct_2(sK5,k1_tarski(sK2),sK3)),
% 4.08/1.00    inference(cnf_transformation,[],[f53])).
% 4.08/1.00  
% 4.08/1.00  fof(f114,plain,(
% 4.08/1.00    v1_funct_2(sK5,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),
% 4.08/1.00    inference(definition_unfolding,[],[f98,f107])).
% 4.08/1.00  
% 4.08/1.00  fof(f100,plain,(
% 4.08/1.00    k1_xboole_0 != sK3),
% 4.08/1.00    inference(cnf_transformation,[],[f53])).
% 4.08/1.00  
% 4.08/1.00  fof(f16,axiom,(
% 4.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f30,plain,(
% 4.08/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.00    inference(ennf_transformation,[],[f16])).
% 4.08/1.00  
% 4.08/1.00  fof(f85,plain,(
% 4.08/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.08/1.00    inference(cnf_transformation,[],[f30])).
% 4.08/1.00  
% 4.08/1.00  fof(f9,axiom,(
% 4.08/1.00    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f24,plain,(
% 4.08/1.00    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 4.08/1.00    inference(ennf_transformation,[],[f9])).
% 4.08/1.00  
% 4.08/1.00  fof(f40,plain,(
% 4.08/1.00    ! [X4,X3,X2,X1,X0,X5] : (sP0(X4,X3,X2,X1,X0,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 4.08/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.08/1.00  
% 4.08/1.00  fof(f41,plain,(
% 4.08/1.00    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP0(X4,X3,X2,X1,X0,X5))),
% 4.08/1.00    inference(definition_folding,[],[f24,f40])).
% 4.08/1.00  
% 4.08/1.00  fof(f49,plain,(
% 4.08/1.00    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP0(X4,X3,X2,X1,X0,X5)) & (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 4.08/1.00    inference(nnf_transformation,[],[f41])).
% 4.08/1.00  
% 4.08/1.00  fof(f76,plain,(
% 4.08/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 4.08/1.00    inference(cnf_transformation,[],[f49])).
% 4.08/1.00  
% 4.08/1.00  fof(f109,plain,(
% 4.08/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) != X5) )),
% 4.08/1.00    inference(definition_unfolding,[],[f76,f103])).
% 4.08/1.00  
% 4.08/1.00  fof(f122,plain,(
% 4.08/1.00    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) )),
% 4.08/1.00    inference(equality_resolution,[],[f109])).
% 4.08/1.00  
% 4.08/1.00  fof(f44,plain,(
% 4.08/1.00    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 4.08/1.00    inference(nnf_transformation,[],[f40])).
% 4.08/1.00  
% 4.08/1.00  fof(f45,plain,(
% 4.08/1.00    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 4.08/1.00    inference(flattening,[],[f44])).
% 4.08/1.00  
% 4.08/1.00  fof(f46,plain,(
% 4.08/1.00    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | ? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 4.08/1.00    inference(rectify,[],[f45])).
% 4.08/1.00  
% 4.08/1.00  fof(f47,plain,(
% 4.08/1.00    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5))) => (((sK1(X0,X1,X2,X3,X4,X5) != X0 & sK1(X0,X1,X2,X3,X4,X5) != X1 & sK1(X0,X1,X2,X3,X4,X5) != X2 & sK1(X0,X1,X2,X3,X4,X5) != X3 & sK1(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5)) & (sK1(X0,X1,X2,X3,X4,X5) = X0 | sK1(X0,X1,X2,X3,X4,X5) = X1 | sK1(X0,X1,X2,X3,X4,X5) = X2 | sK1(X0,X1,X2,X3,X4,X5) = X3 | sK1(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5))))),
% 4.08/1.00    introduced(choice_axiom,[])).
% 4.08/1.00  
% 4.08/1.00  fof(f48,plain,(
% 4.08/1.00    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | (((sK1(X0,X1,X2,X3,X4,X5) != X0 & sK1(X0,X1,X2,X3,X4,X5) != X1 & sK1(X0,X1,X2,X3,X4,X5) != X2 & sK1(X0,X1,X2,X3,X4,X5) != X3 & sK1(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5)) & (sK1(X0,X1,X2,X3,X4,X5) = X0 | sK1(X0,X1,X2,X3,X4,X5) = X1 | sK1(X0,X1,X2,X3,X4,X5) = X2 | sK1(X0,X1,X2,X3,X4,X5) = X3 | sK1(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 4.08/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).
% 4.08/1.00  
% 4.08/1.00  fof(f69,plain,(
% 4.08/1.00    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X0 != X7 | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f48])).
% 4.08/1.00  
% 4.08/1.00  fof(f117,plain,(
% 4.08/1.00    ( ! [X4,X2,X7,X5,X3,X1] : (r2_hidden(X7,X5) | ~sP0(X7,X1,X2,X3,X4,X5)) )),
% 4.08/1.00    inference(equality_resolution,[],[f69])).
% 4.08/1.00  
% 4.08/1.00  fof(f14,axiom,(
% 4.08/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f27,plain,(
% 4.08/1.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.08/1.00    inference(ennf_transformation,[],[f14])).
% 4.08/1.00  
% 4.08/1.00  fof(f28,plain,(
% 4.08/1.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.08/1.00    inference(flattening,[],[f27])).
% 4.08/1.00  
% 4.08/1.00  fof(f83,plain,(
% 4.08/1.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f28])).
% 4.08/1.00  
% 4.08/1.00  fof(f111,plain,(
% 4.08/1.00    ( ! [X0,X1] : (k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.08/1.00    inference(definition_unfolding,[],[f83,f107])).
% 4.08/1.00  
% 4.08/1.00  fof(f10,axiom,(
% 4.08/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f50,plain,(
% 4.08/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.08/1.00    inference(nnf_transformation,[],[f10])).
% 4.08/1.00  
% 4.08/1.00  fof(f78,plain,(
% 4.08/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.08/1.00    inference(cnf_transformation,[],[f50])).
% 4.08/1.00  
% 4.08/1.00  fof(f11,axiom,(
% 4.08/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f25,plain,(
% 4.08/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 4.08/1.00    inference(ennf_transformation,[],[f11])).
% 4.08/1.00  
% 4.08/1.00  fof(f80,plain,(
% 4.08/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f25])).
% 4.08/1.00  
% 4.08/1.00  fof(f79,plain,(
% 4.08/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f50])).
% 4.08/1.00  
% 4.08/1.00  fof(f13,axiom,(
% 4.08/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f82,plain,(
% 4.08/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 4.08/1.00    inference(cnf_transformation,[],[f13])).
% 4.08/1.00  
% 4.08/1.00  fof(f12,axiom,(
% 4.08/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f26,plain,(
% 4.08/1.00    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 4.08/1.00    inference(ennf_transformation,[],[f12])).
% 4.08/1.00  
% 4.08/1.00  fof(f81,plain,(
% 4.08/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f26])).
% 4.08/1.00  
% 4.08/1.00  fof(f110,plain,(
% 4.08/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 4.08/1.00    inference(definition_unfolding,[],[f81,f107])).
% 4.08/1.00  
% 4.08/1.00  fof(f20,axiom,(
% 4.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f35,plain,(
% 4.08/1.00    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.00    inference(ennf_transformation,[],[f20])).
% 4.08/1.00  
% 4.08/1.00  fof(f89,plain,(
% 4.08/1.00    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.08/1.00    inference(cnf_transformation,[],[f35])).
% 4.08/1.00  
% 4.08/1.00  fof(f17,axiom,(
% 4.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f31,plain,(
% 4.08/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.00    inference(ennf_transformation,[],[f17])).
% 4.08/1.00  
% 4.08/1.00  fof(f86,plain,(
% 4.08/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.08/1.00    inference(cnf_transformation,[],[f31])).
% 4.08/1.00  
% 4.08/1.00  fof(f18,axiom,(
% 4.08/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f32,plain,(
% 4.08/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.00    inference(ennf_transformation,[],[f18])).
% 4.08/1.00  
% 4.08/1.00  fof(f87,plain,(
% 4.08/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.08/1.00    inference(cnf_transformation,[],[f32])).
% 4.08/1.00  
% 4.08/1.00  fof(f97,plain,(
% 4.08/1.00    v1_funct_1(sK5)),
% 4.08/1.00    inference(cnf_transformation,[],[f53])).
% 4.08/1.00  
% 4.08/1.00  fof(f101,plain,(
% 4.08/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK2),sK3,sK5,sK4),k1_tarski(k1_funct_1(sK5,sK2)))),
% 4.08/1.00    inference(cnf_transformation,[],[f53])).
% 4.08/1.00  
% 4.08/1.00  fof(f112,plain,(
% 4.08/1.00    ~r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)))),
% 4.08/1.00    inference(definition_unfolding,[],[f101,f107,f107])).
% 4.08/1.00  
% 4.08/1.00  fof(f19,axiom,(
% 4.08/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f33,plain,(
% 4.08/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 4.08/1.00    inference(ennf_transformation,[],[f19])).
% 4.08/1.00  
% 4.08/1.00  fof(f34,plain,(
% 4.08/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 4.08/1.00    inference(flattening,[],[f33])).
% 4.08/1.00  
% 4.08/1.00  fof(f88,plain,(
% 4.08/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 4.08/1.00    inference(cnf_transformation,[],[f34])).
% 4.08/1.00  
% 4.08/1.00  fof(f1,axiom,(
% 4.08/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f42,plain,(
% 4.08/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.08/1.00    inference(nnf_transformation,[],[f1])).
% 4.08/1.00  
% 4.08/1.00  fof(f43,plain,(
% 4.08/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.08/1.00    inference(flattening,[],[f42])).
% 4.08/1.00  
% 4.08/1.00  fof(f55,plain,(
% 4.08/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.08/1.00    inference(cnf_transformation,[],[f43])).
% 4.08/1.00  
% 4.08/1.00  fof(f115,plain,(
% 4.08/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.08/1.00    inference(equality_resolution,[],[f55])).
% 4.08/1.00  
% 4.08/1.00  fof(f15,axiom,(
% 4.08/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 4.08/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f29,plain,(
% 4.08/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.00    inference(ennf_transformation,[],[f15])).
% 4.08/1.00  
% 4.08/1.00  fof(f84,plain,(
% 4.08/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.08/1.00    inference(cnf_transformation,[],[f29])).
% 4.08/1.00  
% 4.08/1.00  cnf(c_38,negated_conjecture,
% 4.08/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
% 4.08/1.00      inference(cnf_transformation,[],[f113]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1589,plain,
% 4.08/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_35,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.08/1.00      | k1_relset_1(X1,X2,X0) = X1
% 4.08/1.00      | k1_xboole_0 = X2 ),
% 4.08/1.00      inference(cnf_transformation,[],[f91]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1591,plain,
% 4.08/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 4.08/1.00      | k1_xboole_0 = X1
% 4.08/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.08/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2855,plain,
% 4.08/1.00      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 4.08/1.00      | sK3 = k1_xboole_0
% 4.08/1.00      | v1_funct_2(sK5,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_1589,c_1591]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_39,negated_conjecture,
% 4.08/1.00      ( v1_funct_2(sK5,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
% 4.08/1.00      inference(cnf_transformation,[],[f114]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_37,negated_conjecture,
% 4.08/1.00      ( k1_xboole_0 != sK3 ),
% 4.08/1.00      inference(cnf_transformation,[],[f100]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2069,plain,
% 4.08/1.00      ( ~ v1_funct_2(sK5,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)
% 4.08/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
% 4.08/1.00      | k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 4.08/1.00      | k1_xboole_0 = sK3 ),
% 4.08/1.00      inference(instantiation,[status(thm)],[c_35]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3544,plain,
% 4.08/1.00      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_2855,c_39,c_38,c_37,c_2069]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_24,plain,
% 4.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.08/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f85]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1602,plain,
% 4.08/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.08/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3175,plain,
% 4.08/1.00      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5) = k1_relat_1(sK5) ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_1589,c_1602]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3546,plain,
% 4.08/1.00      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK5) ),
% 4.08/1.00      inference(light_normalisation,[status(thm)],[c_3544,c_3175]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_16,plain,
% 4.08/1.00      ( sP0(X0,X1,X2,X3,X4,k6_enumset1(X4,X4,X4,X4,X3,X2,X1,X0)) ),
% 4.08/1.00      inference(cnf_transformation,[],[f122]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1609,plain,
% 4.08/1.00      ( sP0(X0,X1,X2,X3,X4,k6_enumset1(X4,X4,X4,X4,X3,X2,X1,X0)) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3570,plain,
% 4.08/1.00      ( sP0(sK2,sK2,sK2,sK2,sK2,k1_relat_1(sK5)) = iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_3546,c_1609]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_9,plain,
% 4.08/1.00      ( ~ sP0(X0,X1,X2,X3,X4,X5) | r2_hidden(X0,X5) ),
% 4.08/1.00      inference(cnf_transformation,[],[f117]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1616,plain,
% 4.08/1.00      ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
% 4.08/1.00      | r2_hidden(X0,X5) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5338,plain,
% 4.08/1.00      ( r2_hidden(sK2,k1_relat_1(sK5)) = iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_3570,c_1616]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_22,plain,
% 4.08/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.08/1.00      | ~ v1_funct_1(X1)
% 4.08/1.00      | ~ v1_relat_1(X1)
% 4.08/1.00      | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f111]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1604,plain,
% 4.08/1.00      ( k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k11_relat_1(X0,X1)
% 4.08/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 4.08/1.00      | v1_funct_1(X0) != iProver_top
% 4.08/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_9140,plain,
% 4.08/1.00      ( k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k11_relat_1(sK5,sK2)
% 4.08/1.00      | v1_funct_1(sK5) != iProver_top
% 4.08/1.00      | v1_relat_1(sK5) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_5338,c_1604]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_18,plain,
% 4.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.08/1.00      inference(cnf_transformation,[],[f78]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1607,plain,
% 4.08/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.08/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2087,plain,
% 4.08/1.00      ( r1_tarski(sK5,k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_1589,c_1607]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_19,plain,
% 4.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f80]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_17,plain,
% 4.08/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.08/1.00      inference(cnf_transformation,[],[f79]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_267,plain,
% 4.08/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 4.08/1.00      inference(prop_impl,[status(thm)],[c_17]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_268,plain,
% 4.08/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_267]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_343,plain,
% 4.08/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 4.08/1.00      inference(bin_hyper_res,[status(thm)],[c_19,c_268]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1586,plain,
% 4.08/1.00      ( r1_tarski(X0,X1) != iProver_top
% 4.08/1.00      | v1_relat_1(X1) != iProver_top
% 4.08/1.00      | v1_relat_1(X0) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2285,plain,
% 4.08/1.00      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 4.08/1.00      | v1_relat_1(sK5) = iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_2087,c_1586]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2051,plain,
% 4.08/1.00      ( r1_tarski(sK5,k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
% 4.08/1.00      inference(resolution,[status(thm)],[c_18,c_38]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2102,plain,
% 4.08/1.00      ( ~ v1_relat_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 4.08/1.00      | v1_relat_1(sK5) ),
% 4.08/1.00      inference(resolution,[status(thm)],[c_343,c_2051]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_21,plain,
% 4.08/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 4.08/1.00      inference(cnf_transformation,[],[f82]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2107,plain,
% 4.08/1.00      ( v1_relat_1(sK5) ),
% 4.08/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2102,c_21]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2108,plain,
% 4.08/1.00      ( v1_relat_1(sK5) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_2107]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2442,plain,
% 4.08/1.00      ( v1_relat_1(sK5) = iProver_top ),
% 4.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2285,c_2108]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_20,plain,
% 4.08/1.00      ( ~ v1_relat_1(X0)
% 4.08/1.00      | k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 4.08/1.00      inference(cnf_transformation,[],[f110]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1606,plain,
% 4.08/1.00      ( k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 4.08/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5953,plain,
% 4.08/1.00      ( k9_relat_1(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k11_relat_1(sK5,X0) ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_2442,c_1606]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6473,plain,
% 4.08/1.00      ( k9_relat_1(sK5,k1_relat_1(sK5)) = k11_relat_1(sK5,sK2) ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_3546,c_5953]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3552,plain,
% 4.08/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK3))) = iProver_top ),
% 4.08/1.00      inference(demodulation,[status(thm)],[c_3546,c_1589]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_29,plain,
% 4.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.08/1.00      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f89]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1597,plain,
% 4.08/1.00      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 4.08/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4351,plain,
% 4.08/1.00      ( k7_relset_1(k1_relat_1(sK5),sK3,sK5,k1_relat_1(sK5)) = k2_relset_1(k1_relat_1(sK5),sK3,sK5) ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_3552,c_1597]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_25,plain,
% 4.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.08/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f86]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1601,plain,
% 4.08/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 4.08/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2570,plain,
% 4.08/1.00      ( k2_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5) = k2_relat_1(sK5) ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_1589,c_1601]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3550,plain,
% 4.08/1.00      ( k2_relset_1(k1_relat_1(sK5),sK3,sK5) = k2_relat_1(sK5) ),
% 4.08/1.00      inference(demodulation,[status(thm)],[c_3546,c_2570]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_4353,plain,
% 4.08/1.00      ( k7_relset_1(k1_relat_1(sK5),sK3,sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
% 4.08/1.00      inference(light_normalisation,[status(thm)],[c_4351,c_3550]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_26,plain,
% 4.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.08/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 4.08/1.00      inference(cnf_transformation,[],[f87]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1600,plain,
% 4.08/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 4.08/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3306,plain,
% 4.08/1.00      ( k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_1589,c_1600]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3548,plain,
% 4.08/1.00      ( k7_relset_1(k1_relat_1(sK5),sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
% 4.08/1.00      inference(demodulation,[status(thm)],[c_3546,c_3306]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5347,plain,
% 4.08/1.00      ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_4353,c_3548]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6474,plain,
% 4.08/1.00      ( k11_relat_1(sK5,sK2) = k2_relat_1(sK5) ),
% 4.08/1.00      inference(light_normalisation,[status(thm)],[c_6473,c_5347]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_9141,plain,
% 4.08/1.00      ( k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k2_relat_1(sK5)
% 4.08/1.00      | v1_funct_1(sK5) != iProver_top
% 4.08/1.00      | v1_relat_1(sK5) != iProver_top ),
% 4.08/1.00      inference(light_normalisation,[status(thm)],[c_9140,c_6474]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_40,negated_conjecture,
% 4.08/1.00      ( v1_funct_1(sK5) ),
% 4.08/1.00      inference(cnf_transformation,[],[f97]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_41,plain,
% 4.08/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_14334,plain,
% 4.08/1.00      ( k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2)) = k2_relat_1(sK5) ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_9141,c_41,c_2108]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_36,negated_conjecture,
% 4.08/1.00      ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) ),
% 4.08/1.00      inference(cnf_transformation,[],[f112]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1590,plain,
% 4.08/1.00      ( r1_tarski(k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_3400,plain,
% 4.08/1.00      ( r1_tarski(k9_relat_1(sK5,sK4),k6_enumset1(k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2),k1_funct_1(sK5,sK2))) != iProver_top ),
% 4.08/1.00      inference(demodulation,[status(thm)],[c_3306,c_1590]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_14337,plain,
% 4.08/1.00      ( r1_tarski(k9_relat_1(sK5,sK4),k2_relat_1(sK5)) != iProver_top ),
% 4.08/1.00      inference(demodulation,[status(thm)],[c_14334,c_3400]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_27,plain,
% 4.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.08/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 4.08/1.00      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 4.08/1.00      inference(cnf_transformation,[],[f88]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1599,plain,
% 4.08/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.08/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 4.08/1.00      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_7223,plain,
% 4.08/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),X0))) = iProver_top
% 4.08/1.00      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_3552,c_1599]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f115]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1623,plain,
% 4.08/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_8121,plain,
% 4.08/1.00      ( k7_relset_1(k1_relat_1(sK5),X0,sK5,X1) = k9_relat_1(sK5,X1)
% 4.08/1.00      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_7223,c_1600]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_8661,plain,
% 4.08/1.00      ( k7_relset_1(k1_relat_1(sK5),k2_relat_1(sK5),sK5,X0) = k9_relat_1(sK5,X0) ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_1623,c_8121]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_23,plain,
% 4.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.08/1.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 4.08/1.00      inference(cnf_transformation,[],[f84]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1603,plain,
% 4.08/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.08/1.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_10450,plain,
% 4.08/1.00      ( m1_subset_1(k9_relat_1(sK5,X0),k1_zfmisc_1(k2_relat_1(sK5))) = iProver_top
% 4.08/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5)))) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_8661,c_1603]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_12406,plain,
% 4.08/1.00      ( m1_subset_1(k9_relat_1(sK5,X0),k1_zfmisc_1(k2_relat_1(sK5))) = iProver_top
% 4.08/1.00      | r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5)) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_7223,c_10450]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2002,plain,
% 4.08/1.00      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X0)) ),
% 4.08/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_10435,plain,
% 4.08/1.00      ( r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5)) ),
% 4.08/1.00      inference(instantiation,[status(thm)],[c_2002]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_10436,plain,
% 4.08/1.00      ( r1_tarski(k2_relat_1(sK5),k2_relat_1(sK5)) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_10435]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_12528,plain,
% 4.08/1.00      ( m1_subset_1(k9_relat_1(sK5,X0),k1_zfmisc_1(k2_relat_1(sK5))) = iProver_top ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_12406,c_10436]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_12537,plain,
% 4.08/1.00      ( r1_tarski(k9_relat_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_12528,c_1607]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_14356,plain,
% 4.08/1.00      ( $false ),
% 4.08/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_14337,c_12537]) ).
% 4.08/1.00  
% 4.08/1.00  
% 4.08/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.08/1.00  
% 4.08/1.00  ------                               Statistics
% 4.08/1.00  
% 4.08/1.00  ------ Selected
% 4.08/1.00  
% 4.08/1.00  total_time:                             0.5
% 4.08/1.00  
%------------------------------------------------------------------------------
