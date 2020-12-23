%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  113 (3588 expanded)
%              Number of leaves         :   14 (1122 expanded)
%              Depth                    :   35
%              Number of atoms          :  566 (15773 expanded)
%              Number of equality atoms :  165 (4574 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(subsumption_resolution,[],[f300,f285])).

fof(f285,plain,(
    ! [X0] : k1_xboole_0 = X0 ),
    inference(subsumption_resolution,[],[f281,f77])).

fof(f77,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f281,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f67,f260])).

fof(f260,plain,(
    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f259,f65])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f36,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f27,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
          & v1_funct_2(X3,sK0,k1_tarski(sK1))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        & v1_funct_2(X3,sK0,k1_tarski(sK1))
        & v1_funct_1(X3) )
   => ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

fof(f259,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(resolution,[],[f239,f124])).

fof(f124,plain,
    ( r2_hidden(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f123,f62])).

fof(f62,plain,(
    k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) != k1_enumset1(sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f40,f61,f61])).

fof(f40,plain,(
    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f123,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = k1_enumset1(sK3,sK3,sK3)
    | r2_hidden(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(resolution,[],[f114,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_enumset1(X0,X0,X0) = X1
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(trivial_inequality_removal,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X0
      | k1_enumset1(X0,X0,X0) = X1
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X0
      | k1_enumset1(X0,X0,X0) = X1
      | k1_enumset1(X0,X0,X0) = X1
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(superposition,[],[f68,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) = X0
      | k1_enumset1(X0,X0,X0) = X1
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f47,f61])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK4(X0,X1) = X0
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | sK4(X0,X1) != X0
      | k1_enumset1(X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f48,f61])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK4(X0,X1) != X0
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f114,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f112,f35])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f112,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | ~ v1_funct_1(sK2)
    | r2_hidden(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(resolution,[],[f110,f65])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),X0)) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) ) ),
    inference(resolution,[],[f107,f63])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f39,f61])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))) ) ),
    inference(subsumption_resolution,[],[f106,f37])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),X0))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))) ) ),
    inference(subsumption_resolution,[],[f105,f63])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))) ) ),
    inference(resolution,[],[f97,f64])).

fof(f64,plain,(
    v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f38,f61])).

fof(f38,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X1,X2,X0)
      | r2_hidden(X1,k5_partfun1(X2,X0,X3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | k1_xboole_0 = X0
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,k1_enumset1(X5,X5,X5))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,k1_enumset1(X5,X5,X5)))) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | r2_hidden(X1,k5_partfun1(X2,X0,X3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_2(X1,X2,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,k1_enumset1(X5,X5,X5))))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,k1_enumset1(X5,X5,X5))))
      | ~ v1_funct_1(X3) ) ),
    inference(resolution,[],[f57,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_enumset1(X1,X1,X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_enumset1(X1,X1,X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f60,f61,f61])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

fof(f239,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k5_partfun1(X0,X1,sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ) ),
    inference(resolution,[],[f236,f35])).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ) ),
    inference(subsumption_resolution,[],[f234,f134])).

fof(f134,plain,
    ( m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f133,f35])).

fof(f133,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f128,f65])).

fof(f128,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f124,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
      | ~ r2_hidden(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f233,f63])).

fof(f233,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_enumset1(X1,X1,X1))))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(X0,k1_enumset1(X1,X1,X1))))
      | ~ r2_hidden(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k5_partfun1(X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(subsumption_resolution,[],[f231,f134])).

fof(f231,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_enumset1(X1,X1,X1))))
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(X0,k1_enumset1(X1,X1,X1))))
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
      | ~ r2_hidden(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k5_partfun1(X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(resolution,[],[f191,f63])).

fof(f191,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))))
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))))
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ r2_hidden(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k5_partfun1(X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f149,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)))
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))))
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f148,f134])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ v1_funct_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))))
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))))
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f147,f132])).

fof(f132,plain,
    ( sK3 != sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f127,f62])).

fof(f127,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | sK3 != sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2))
    | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = k1_enumset1(sK3,sK3,sK3) ),
    inference(resolution,[],[f124,f68])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ v1_funct_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))))
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))))
      | sK3 = sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2))
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ v1_funct_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))))
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | sK3 = sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(resolution,[],[f136,f126])).

fof(f126,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X1,sK0,X4)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | sK3 = X1
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | sK3 = X1
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
      | ~ v1_funct_2(X1,sK0,X4)
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f120,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_partfun1(X0,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | sK3 = X0 ) ),
    inference(subsumption_resolution,[],[f119,f63])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_partfun1(X0,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
      | sK3 = X0 ) ),
    inference(subsumption_resolution,[],[f118,f37])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_partfun1(X0,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
      | sK3 = X0 ) ),
    inference(resolution,[],[f100,f64])).

fof(f100,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] :
      ( ~ v1_funct_2(X7,X8,X12)
      | ~ v1_partfun1(X6,X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X10,k1_enumset1(X11,X11,X11))))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X10,k1_enumset1(X11,X11,X11))))
      | k1_xboole_0 = X12
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X12)))
      | X6 = X7 ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] :
      ( X6 = X7
      | ~ v1_partfun1(X6,X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X10,k1_enumset1(X11,X11,X11))))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X10,k1_enumset1(X11,X11,X11))))
      | k1_xboole_0 = X12
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X12)))
      | ~ v1_funct_2(X7,X8,X12)
      | ~ v1_funct_1(X7) ) ),
    inference(resolution,[],[f95,f80])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_partfun1(X1,X2)
      | X0 = X1
      | ~ v1_partfun1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,k1_enumset1(X5,X5,X5))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,k1_enumset1(X5,X5,X5)))) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X1
      | ~ v1_partfun1(X1,X2)
      | ~ v1_partfun1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,k1_enumset1(X5,X5,X5))))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,k1_enumset1(X5,X5,X5))))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f59,f72])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_partfun1(X2,X3)
      | X2 = X3
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f136,plain,
    ( v1_funct_2(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),sK0,k1_enumset1(sK1,sK1,sK1))
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f135,f35])).

fof(f135,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | v1_funct_2(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),sK0,k1_enumset1(sK1,sK1,sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f129,f65])).

fof(f129,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | v1_funct_2(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),sK0,k1_enumset1(sK1,sK1,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f124,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_enumset1(X1,X1,X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f61])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f300,plain,(
    k1_xboole_0 != k5_partfun1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f261,f285])).

fof(f261,plain,(
    k1_enumset1(sK3,sK3,sK3) != k5_partfun1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f62,f260])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (4873)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.47  % (4881)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (4870)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (4869)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (4865)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (4858)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (4875)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (4860)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (4880)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (4859)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (4878)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (4872)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (4862)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (4887)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (4887)Refutation not found, incomplete strategy% (4887)------------------------------
% 0.21/0.53  % (4887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4887)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4887)Memory used [KB]: 1663
% 0.21/0.53  % (4887)Time elapsed: 0.128 s
% 0.21/0.53  % (4887)------------------------------
% 0.21/0.53  % (4887)------------------------------
% 0.21/0.53  % (4863)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (4861)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (4884)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (4874)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (4876)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (4879)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (4874)Refutation not found, incomplete strategy% (4874)------------------------------
% 0.21/0.54  % (4874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4874)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4874)Memory used [KB]: 10746
% 0.21/0.54  % (4874)Time elapsed: 0.137 s
% 0.21/0.54  % (4874)------------------------------
% 0.21/0.54  % (4874)------------------------------
% 0.21/0.54  % (4867)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (4866)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (4871)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (4886)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (4885)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (4868)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (4885)Refutation not found, incomplete strategy% (4885)------------------------------
% 0.21/0.55  % (4885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4885)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4885)Memory used [KB]: 6140
% 0.21/0.55  % (4885)Time elapsed: 0.138 s
% 0.21/0.55  % (4885)------------------------------
% 0.21/0.55  % (4885)------------------------------
% 0.21/0.55  % (4864)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (4877)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (4882)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (4883)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (4882)Refutation not found, incomplete strategy% (4882)------------------------------
% 0.21/0.56  % (4882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4882)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (4882)Memory used [KB]: 10618
% 0.21/0.56  % (4882)Time elapsed: 0.157 s
% 0.21/0.56  % (4882)------------------------------
% 0.21/0.56  % (4882)------------------------------
% 0.21/0.56  % (4880)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 1.69/0.58  % SZS output start Proof for theBenchmark
% 1.69/0.58  fof(f320,plain,(
% 1.69/0.58    $false),
% 1.69/0.58    inference(subsumption_resolution,[],[f300,f285])).
% 1.69/0.58  fof(f285,plain,(
% 1.69/0.58    ( ! [X0] : (k1_xboole_0 = X0) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f281,f77])).
% 1.69/0.58  fof(f77,plain,(
% 1.69/0.58    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.69/0.58    inference(equality_resolution,[],[f50])).
% 1.69/0.58  fof(f50,plain,(
% 1.69/0.58    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 1.69/0.58    inference(cnf_transformation,[],[f34])).
% 1.69/0.58  fof(f34,plain,(
% 1.69/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.69/0.58    inference(flattening,[],[f33])).
% 1.69/0.58  fof(f33,plain,(
% 1.69/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.69/0.58    inference(nnf_transformation,[],[f4])).
% 1.69/0.58  fof(f4,axiom,(
% 1.69/0.58    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.69/0.58  fof(f281,plain,(
% 1.69/0.58    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 1.69/0.58    inference(superposition,[],[f67,f260])).
% 1.69/0.58  fof(f260,plain,(
% 1.69/0.58    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 1.69/0.58    inference(subsumption_resolution,[],[f259,f65])).
% 1.69/0.58  fof(f65,plain,(
% 1.69/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))),
% 1.69/0.58    inference(definition_unfolding,[],[f36,f61])).
% 1.69/0.58  fof(f61,plain,(
% 1.69/0.58    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.69/0.58    inference(definition_unfolding,[],[f41,f42])).
% 1.69/0.58  fof(f42,plain,(
% 1.69/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f3])).
% 1.69/0.58  fof(f3,axiom,(
% 1.69/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.69/0.58  fof(f41,plain,(
% 1.69/0.58    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f2])).
% 1.69/0.58  fof(f2,axiom,(
% 1.69/0.58    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.69/0.58  fof(f36,plain,(
% 1.69/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.69/0.58    inference(cnf_transformation,[],[f28])).
% 1.69/0.58  fof(f28,plain,(
% 1.69/0.58    (k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_1(sK2)),
% 1.69/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f27,f26])).
% 1.69/0.58  fof(f26,plain,(
% 1.69/0.58    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_1(sK2))),
% 1.69/0.58    introduced(choice_axiom,[])).
% 1.69/0.58  fof(f27,plain,(
% 1.69/0.58    ? [X3] : (k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) => (k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 1.69/0.58    introduced(choice_axiom,[])).
% 1.69/0.58  fof(f14,plain,(
% 1.69/0.58    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 1.69/0.58    inference(flattening,[],[f13])).
% 1.69/0.58  fof(f13,plain,(
% 1.69/0.58    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 1.69/0.58    inference(ennf_transformation,[],[f12])).
% 1.69/0.58  fof(f12,negated_conjecture,(
% 1.69/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 1.69/0.58    inference(negated_conjecture,[],[f11])).
% 1.69/0.58  fof(f11,conjecture,(
% 1.69/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).
% 1.69/0.58  fof(f259,plain,(
% 1.69/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 1.69/0.58    inference(duplicate_literal_removal,[],[f257])).
% 1.69/0.58  fof(f257,plain,(
% 1.69/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 1.69/0.58    inference(resolution,[],[f239,f124])).
% 1.69/0.58  fof(f124,plain,(
% 1.69/0.58    r2_hidden(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 1.69/0.58    inference(subsumption_resolution,[],[f123,f62])).
% 1.69/0.58  fof(f62,plain,(
% 1.69/0.58    k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) != k1_enumset1(sK3,sK3,sK3)),
% 1.69/0.58    inference(definition_unfolding,[],[f40,f61,f61])).
% 1.69/0.58  fof(f40,plain,(
% 1.69/0.58    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)),
% 1.69/0.58    inference(cnf_transformation,[],[f28])).
% 1.69/0.58  fof(f123,plain,(
% 1.69/0.58    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = k1_enumset1(sK3,sK3,sK3) | r2_hidden(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2))),
% 1.69/0.58    inference(resolution,[],[f114,f92])).
% 1.69/0.58  fof(f92,plain,(
% 1.69/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_enumset1(X0,X0,X0) = X1 | r2_hidden(sK4(X0,X1),X1)) )),
% 1.69/0.58    inference(trivial_inequality_removal,[],[f91])).
% 1.69/0.58  fof(f91,plain,(
% 1.69/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | X0 != X0 | k1_enumset1(X0,X0,X0) = X1 | r2_hidden(sK4(X0,X1),X1)) )),
% 1.69/0.58    inference(duplicate_literal_removal,[],[f90])).
% 1.69/0.58  fof(f90,plain,(
% 1.69/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | X0 != X0 | k1_enumset1(X0,X0,X0) = X1 | k1_enumset1(X0,X0,X0) = X1 | r2_hidden(sK4(X0,X1),X1)) )),
% 1.69/0.58    inference(superposition,[],[f68,f69])).
% 1.69/0.58  fof(f69,plain,(
% 1.69/0.58    ( ! [X0,X1] : (sK4(X0,X1) = X0 | k1_enumset1(X0,X0,X0) = X1 | r2_hidden(sK4(X0,X1),X1)) )),
% 1.69/0.58    inference(definition_unfolding,[],[f47,f61])).
% 1.69/0.58  fof(f47,plain,(
% 1.69/0.58    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f32])).
% 1.69/0.58  fof(f32,plain,(
% 1.69/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.69/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 1.69/0.58  fof(f31,plain,(
% 1.69/0.58    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.69/0.58    introduced(choice_axiom,[])).
% 1.69/0.58  fof(f30,plain,(
% 1.69/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.69/0.58    inference(rectify,[],[f29])).
% 1.69/0.58  fof(f29,plain,(
% 1.69/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.69/0.58    inference(nnf_transformation,[],[f1])).
% 1.69/0.58  fof(f1,axiom,(
% 1.69/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.69/0.58  fof(f68,plain,(
% 1.69/0.58    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | sK4(X0,X1) != X0 | k1_enumset1(X0,X0,X0) = X1) )),
% 1.69/0.58    inference(definition_unfolding,[],[f48,f61])).
% 1.69/0.58  fof(f48,plain,(
% 1.69/0.58    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f32])).
% 1.69/0.58  fof(f114,plain,(
% 1.69/0.58    r2_hidden(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 1.69/0.58    inference(subsumption_resolution,[],[f112,f35])).
% 1.69/0.58  fof(f35,plain,(
% 1.69/0.58    v1_funct_1(sK2)),
% 1.69/0.58    inference(cnf_transformation,[],[f28])).
% 1.69/0.58  fof(f112,plain,(
% 1.69/0.58    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~v1_funct_1(sK2) | r2_hidden(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2))),
% 1.69/0.58    inference(resolution,[],[f110,f65])).
% 1.69/0.58  fof(f110,plain,(
% 1.69/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~v1_funct_1(X0) | r2_hidden(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),X0))) )),
% 1.69/0.58    inference(duplicate_literal_removal,[],[f108])).
% 1.69/0.58  fof(f108,plain,(
% 1.69/0.58    ( ! [X0] : (k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~v1_funct_1(X0) | r2_hidden(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))) )),
% 1.69/0.58    inference(resolution,[],[f107,f63])).
% 1.69/0.58  fof(f63,plain,(
% 1.69/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))),
% 1.69/0.58    inference(definition_unfolding,[],[f39,f61])).
% 1.69/0.58  fof(f39,plain,(
% 1.69/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.69/0.58    inference(cnf_transformation,[],[f28])).
% 1.69/0.58  fof(f107,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~v1_funct_1(X0) | r2_hidden(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))))) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f106,f37])).
% 1.69/0.58  fof(f37,plain,(
% 1.69/0.58    v1_funct_1(sK3)),
% 1.69/0.58    inference(cnf_transformation,[],[f28])).
% 1.69/0.58  fof(f106,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),X0)) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~v1_funct_1(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))))) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f105,f63])).
% 1.69/0.58  fof(f105,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~v1_funct_1(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))))) )),
% 1.69/0.58    inference(resolution,[],[f97,f64])).
% 1.69/0.58  fof(f64,plain,(
% 1.69/0.58    v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1))),
% 1.69/0.58    inference(definition_unfolding,[],[f38,f61])).
% 1.69/0.58  fof(f38,plain,(
% 1.69/0.58    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.69/0.58    inference(cnf_transformation,[],[f28])).
% 1.69/0.58  fof(f97,plain,(
% 1.69/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(X1,X2,X0) | r2_hidden(X1,k5_partfun1(X2,X0,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0 | ~v1_funct_1(X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,k1_enumset1(X5,X5,X5)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,k1_enumset1(X5,X5,X5))))) )),
% 1.69/0.58    inference(duplicate_literal_removal,[],[f96])).
% 1.69/0.58  fof(f96,plain,(
% 1.69/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = X0 | r2_hidden(X1,k5_partfun1(X2,X0,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X1,X2,X0) | ~v1_funct_1(X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,k1_enumset1(X5,X5,X5)))) | ~v1_funct_1(X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,k1_enumset1(X5,X5,X5)))) | ~v1_funct_1(X3)) )),
% 1.69/0.58    inference(resolution,[],[f57,f72])).
% 1.69/0.58  fof(f72,plain,(
% 1.69/0.58    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_enumset1(X1,X1,X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_enumset1(X1,X1,X1)))) | ~v1_funct_1(X2)) )),
% 1.69/0.58    inference(definition_unfolding,[],[f60,f61,f61])).
% 1.69/0.58  fof(f60,plain,(
% 1.69/0.58    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f25])).
% 1.69/0.58  fof(f25,plain,(
% 1.69/0.58    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 1.69/0.58    inference(flattening,[],[f24])).
% 1.69/0.58  fof(f24,plain,(
% 1.69/0.58    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 1.69/0.58    inference(ennf_transformation,[],[f7])).
% 1.69/0.58  fof(f7,axiom,(
% 1.69/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).
% 1.69/0.58  fof(f57,plain,(
% 1.69/0.58    ( ! [X2,X0,X3,X1] : (~r1_partfun1(X2,X3) | k1_xboole_0 = X1 | r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f21])).
% 1.69/0.58  fof(f21,plain,(
% 1.69/0.58    ! [X0,X1,X2] : (! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.69/0.58    inference(flattening,[],[f20])).
% 1.69/0.58  fof(f20,plain,(
% 1.69/0.58    ! [X0,X1,X2] : (! [X3] : (((r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_partfun1(X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.69/0.58    inference(ennf_transformation,[],[f9])).
% 1.69/0.58  fof(f9,axiom,(
% 1.69/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).
% 1.69/0.58  fof(f239,plain,(
% 1.69/0.58    ( ! [X0,X1] : (~r2_hidden(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k5_partfun1(X0,X1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)) )),
% 1.69/0.58    inference(resolution,[],[f236,f35])).
% 1.69/0.58  fof(f236,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f234,f134])).
% 1.69/0.58  fof(f134,plain,(
% 1.69/0.58    m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 1.69/0.58    inference(subsumption_resolution,[],[f133,f35])).
% 1.69/0.58  fof(f133,plain,(
% 1.69/0.58    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~v1_funct_1(sK2)),
% 1.69/0.58    inference(subsumption_resolution,[],[f128,f65])).
% 1.69/0.58  fof(f128,plain,(
% 1.69/0.58    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~v1_funct_1(sK2)),
% 1.69/0.58    inference(resolution,[],[f124,f56])).
% 1.69/0.58  fof(f56,plain,(
% 1.69/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f19])).
% 1.69/0.58  fof(f19,plain,(
% 1.69/0.58    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.69/0.58    inference(flattening,[],[f18])).
% 1.69/0.58  fof(f18,plain,(
% 1.69/0.58    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.69/0.58    inference(ennf_transformation,[],[f10])).
% 1.69/0.58  fof(f10,axiom,(
% 1.69/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).
% 1.69/0.58  fof(f234,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~r2_hidden(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.69/0.58    inference(resolution,[],[f233,f63])).
% 1.69/0.58  fof(f233,plain,(
% 1.69/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_enumset1(X1,X1,X1)))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(X0,k1_enumset1(X1,X1,X1)))) | ~r2_hidden(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k5_partfun1(X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f231,f134])).
% 1.69/0.58  fof(f231,plain,(
% 1.69/0.58    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_enumset1(X1,X1,X1)))) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(X0,k1_enumset1(X1,X1,X1)))) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~r2_hidden(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k5_partfun1(X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.69/0.58    inference(resolution,[],[f191,f63])).
% 1.69/0.58  fof(f191,plain,(
% 1.69/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~r2_hidden(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k5_partfun1(X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 1.69/0.58    inference(resolution,[],[f149,f54])).
% 1.69/0.58  fof(f54,plain,(
% 1.69/0.58    ( ! [X2,X0,X3,X1] : (v1_funct_1(X3) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f19])).
% 1.69/0.58  fof(f149,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~v1_funct_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2))) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f148,f134])).
% 1.69/0.58  fof(f148,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f147,f132])).
% 1.69/0.58  fof(f132,plain,(
% 1.69/0.58    sK3 != sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 1.69/0.58    inference(subsumption_resolution,[],[f127,f62])).
% 1.69/0.58  fof(f127,plain,(
% 1.69/0.58    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | sK3 != sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)) | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = k1_enumset1(sK3,sK3,sK3)),
% 1.69/0.58    inference(resolution,[],[f124,f68])).
% 1.69/0.58  fof(f147,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))) | sK3 = sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 1.69/0.58    inference(duplicate_literal_removal,[],[f141])).
% 1.69/0.58  fof(f141,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | sK3 = sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 1.69/0.58    inference(resolution,[],[f136,f126])).
% 1.69/0.58  fof(f126,plain,(
% 1.69/0.58    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X1,sK0,X4) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3)))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | sK3 = X1 | k1_xboole_0 = X4 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X4))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 1.69/0.58    inference(duplicate_literal_removal,[],[f125])).
% 1.69/0.58  fof(f125,plain,(
% 1.69/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3)))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | sK3 = X1 | k1_xboole_0 = X4 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X4))) | ~v1_funct_2(X1,sK0,X4) | ~v1_funct_1(X1)) )),
% 1.69/0.58    inference(resolution,[],[f120,f80])).
% 1.69/0.58  fof(f80,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.69/0.58    inference(duplicate_literal_removal,[],[f52])).
% 1.69/0.58  fof(f52,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f17])).
% 1.69/0.58  fof(f17,plain,(
% 1.69/0.58    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.69/0.58    inference(flattening,[],[f16])).
% 1.69/0.58  fof(f16,plain,(
% 1.69/0.58    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.69/0.58    inference(ennf_transformation,[],[f6])).
% 1.69/0.58  fof(f6,axiom,(
% 1.69/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 1.69/0.58  fof(f120,plain,(
% 1.69/0.58    ( ! [X2,X0,X3,X1] : (~v1_partfun1(X0,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3)))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | sK3 = X0) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f119,f63])).
% 1.69/0.58  fof(f119,plain,(
% 1.69/0.58    ( ! [X2,X0,X3,X1] : (~v1_partfun1(X0,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3)))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | sK3 = X0) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f118,f37])).
% 1.69/0.58  fof(f118,plain,(
% 1.69/0.58    ( ! [X2,X0,X3,X1] : (~v1_partfun1(X0,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3)))) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | sK3 = X0) )),
% 1.69/0.58    inference(resolution,[],[f100,f64])).
% 1.69/0.58  fof(f100,plain,(
% 1.69/0.58    ( ! [X6,X12,X10,X8,X7,X11,X9] : (~v1_funct_2(X7,X8,X12) | ~v1_partfun1(X6,X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X6) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X10,k1_enumset1(X11,X11,X11)))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X10,k1_enumset1(X11,X11,X11)))) | k1_xboole_0 = X12 | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X12))) | X6 = X7) )),
% 1.69/0.58    inference(duplicate_literal_removal,[],[f99])).
% 1.69/0.58  fof(f99,plain,(
% 1.69/0.58    ( ! [X6,X12,X10,X8,X7,X11,X9] : (X6 = X7 | ~v1_partfun1(X6,X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X6) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X10,k1_enumset1(X11,X11,X11)))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X10,k1_enumset1(X11,X11,X11)))) | k1_xboole_0 = X12 | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X12))) | ~v1_funct_2(X7,X8,X12) | ~v1_funct_1(X7)) )),
% 1.69/0.58    inference(resolution,[],[f95,f80])).
% 1.69/0.58  fof(f95,plain,(
% 1.69/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_partfun1(X1,X2) | X0 = X1 | ~v1_partfun1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,k1_enumset1(X5,X5,X5)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,k1_enumset1(X5,X5,X5))))) )),
% 1.69/0.58    inference(duplicate_literal_removal,[],[f94])).
% 1.69/0.58  fof(f94,plain,(
% 1.69/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X1 | ~v1_partfun1(X1,X2) | ~v1_partfun1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,k1_enumset1(X5,X5,X5)))) | ~v1_funct_1(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,k1_enumset1(X5,X5,X5)))) | ~v1_funct_1(X0)) )),
% 1.69/0.58    inference(resolution,[],[f59,f72])).
% 1.69/0.58  fof(f59,plain,(
% 1.69/0.58    ( ! [X2,X0,X3,X1] : (~r1_partfun1(X2,X3) | X2 = X3 | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f23])).
% 1.69/0.58  fof(f23,plain,(
% 1.69/0.58    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.69/0.58    inference(flattening,[],[f22])).
% 1.69/0.58  fof(f22,plain,(
% 1.69/0.58    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.69/0.58    inference(ennf_transformation,[],[f8])).
% 1.69/0.58  fof(f8,axiom,(
% 1.69/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 1.69/0.58  fof(f136,plain,(
% 1.69/0.58    v1_funct_2(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),sK0,k1_enumset1(sK1,sK1,sK1)) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 1.69/0.58    inference(subsumption_resolution,[],[f135,f35])).
% 1.69/0.58  fof(f135,plain,(
% 1.69/0.58    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | v1_funct_2(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),sK0,k1_enumset1(sK1,sK1,sK1)) | ~v1_funct_1(sK2)),
% 1.69/0.58    inference(subsumption_resolution,[],[f129,f65])).
% 1.69/0.58  fof(f129,plain,(
% 1.69/0.58    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | v1_funct_2(sK4(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2)),sK0,k1_enumset1(sK1,sK1,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~v1_funct_1(sK2)),
% 1.69/0.58    inference(resolution,[],[f124,f55])).
% 1.69/0.58  fof(f55,plain,(
% 1.69/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_2(X3,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f19])).
% 1.69/0.58  fof(f67,plain,(
% 1.69/0.58    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_enumset1(X1,X1,X1),X0) | k1_xboole_0 = X0) )),
% 1.69/0.58    inference(definition_unfolding,[],[f43,f61])).
% 1.69/0.58  fof(f43,plain,(
% 1.69/0.58    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) | k1_xboole_0 = X0) )),
% 1.69/0.58    inference(cnf_transformation,[],[f15])).
% 1.69/0.58  fof(f15,plain,(
% 1.69/0.58    ! [X0,X1] : ((k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) | k1_xboole_0 = X0)),
% 1.69/0.58    inference(ennf_transformation,[],[f5])).
% 1.69/0.58  fof(f5,axiom,(
% 1.69/0.58    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 1.69/0.58  fof(f300,plain,(
% 1.69/0.58    k1_xboole_0 != k5_partfun1(sK0,k1_xboole_0,sK2)),
% 1.69/0.58    inference(backward_demodulation,[],[f261,f285])).
% 1.69/0.58  fof(f261,plain,(
% 1.69/0.58    k1_enumset1(sK3,sK3,sK3) != k5_partfun1(sK0,k1_xboole_0,sK2)),
% 1.69/0.58    inference(backward_demodulation,[],[f62,f260])).
% 1.69/0.58  % SZS output end Proof for theBenchmark
% 1.69/0.58  % (4880)------------------------------
% 1.69/0.58  % (4880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.58  % (4880)Termination reason: Refutation
% 1.69/0.58  
% 1.69/0.58  % (4880)Memory used [KB]: 6524
% 1.69/0.58  % (4880)Time elapsed: 0.125 s
% 1.69/0.58  % (4880)------------------------------
% 1.69/0.58  % (4880)------------------------------
% 1.69/0.58  % (4857)Success in time 0.223 s
%------------------------------------------------------------------------------
