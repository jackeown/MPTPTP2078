%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:11 EST 2020

% Result     : Theorem 2.28s
% Output     : Refutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 140 expanded)
%              Number of leaves         :   20 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  254 ( 492 expanded)
%              Number of equality atoms :   25 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1015,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f124,f240,f1012])).

fof(f1012,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f1011])).

fof(f1011,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f998,f122])).

fof(f122,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f998,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl5_1 ),
    inference(resolution,[],[f958,f242])).

fof(f242,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK1,sK3))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f241,f55])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ r1_tarski(sK2,sK3)
      | ~ r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) )
    & ( r1_tarski(sK2,sK3)
      | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f45,f44])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,X2)
              | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK2,X2)
            | ~ r1_xboole_0(sK2,k3_subset_1(sK1,X2)) )
          & ( r1_tarski(sK2,X2)
            | r1_xboole_0(sK2,k3_subset_1(sK1,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK2,X2)
          | ~ r1_xboole_0(sK2,k3_subset_1(sK1,X2)) )
        & ( r1_tarski(sK2,X2)
          | r1_xboole_0(sK2,k3_subset_1(sK1,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
   => ( ( ~ r1_tarski(sK2,sK3)
        | ~ r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) )
      & ( r1_tarski(sK2,sK3)
        | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f241,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ spl5_1 ),
    inference(superposition,[],[f117,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f117,plain,
    ( r1_xboole_0(sK2,k3_subset_1(sK1,sK3))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_1
  <=> r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f958,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK2,k4_xboole_0(sK1,X0))
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f835,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f835,plain,(
    ! [X12] :
      ( ~ r1_xboole_0(sK1,k4_xboole_0(sK2,X12))
      | r1_tarski(sK2,X12) ) ),
    inference(resolution,[],[f460,f172])).

fof(f172,plain,(
    ! [X8] :
      ( r1_xboole_0(sK2,X8)
      | ~ r1_xboole_0(sK1,X8) ) ),
    inference(resolution,[],[f91,f161])).

fof(f161,plain,(
    r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f160,f150])).

fof(f150,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f147,f58])).

fof(f58,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f147,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f71,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f78,f114])).

fof(f114,plain,(
    ! [X0] : sP0(X0,k1_zfmisc_1(X0)) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f25,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | r1_tarski(X3,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f460,plain,(
    ! [X45,X44] :
      ( ~ r1_xboole_0(X44,k4_xboole_0(X44,X45))
      | r1_tarski(X44,X45) ) ),
    inference(superposition,[],[f310,f278])).

fof(f278,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = X1
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(forward_demodulation,[],[f272,f59])).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f272,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_xboole_0)
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(superposition,[],[f102,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f102,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f68,f70])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f310,plain,(
    ! [X8,X7] : r1_tarski(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X7) ),
    inference(superposition,[],[f104,f106])).

fof(f106,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f64,f70,f70])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f104,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f61,f70])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f240,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f238,f121])).

fof(f121,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f238,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl5_1 ),
    inference(resolution,[],[f234,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f234,plain,
    ( ~ r1_xboole_0(sK2,k4_xboole_0(sK1,sK3))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f231,f55])).

fof(f231,plain,
    ( ~ r1_xboole_0(sK2,k4_xboole_0(sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | spl5_1 ),
    inference(superposition,[],[f118,f75])).

fof(f118,plain,
    ( ~ r1_xboole_0(sK2,k3_subset_1(sK1,sK3))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f124,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f56,f120,f116])).

fof(f56,plain,
    ( r1_tarski(sK2,sK3)
    | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f123,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f57,f120,f116])).

fof(f57,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:18:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.56  % (533)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (515)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.48/0.57  % (523)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.72/0.58  % (518)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.72/0.59  % (525)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.72/0.59  % (512)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.72/0.59  % (513)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.72/0.60  % (514)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.72/0.60  % (517)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.72/0.60  % (521)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.72/0.60  % (524)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.72/0.60  % (532)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.72/0.61  % (520)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.72/0.61  % (535)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.72/0.61  % (541)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.72/0.61  % (531)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.72/0.61  % (527)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.72/0.62  % (536)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.72/0.62  % (537)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.72/0.62  % (529)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.72/0.62  % (526)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.72/0.62  % (540)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.72/0.62  % (534)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.72/0.62  % (516)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.72/0.62  % (528)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.72/0.63  % (519)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.72/0.63  % (538)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.72/0.64  % (522)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.72/0.64  % (539)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.16/0.64  % (530)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.16/0.65  % (534)Refutation not found, incomplete strategy% (534)------------------------------
% 2.16/0.65  % (534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.65  % (534)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.65  
% 2.16/0.65  % (534)Memory used [KB]: 10746
% 2.16/0.65  % (534)Time elapsed: 0.221 s
% 2.16/0.65  % (534)------------------------------
% 2.16/0.65  % (534)------------------------------
% 2.28/0.69  % (539)Refutation found. Thanks to Tanya!
% 2.28/0.69  % SZS status Theorem for theBenchmark
% 2.28/0.69  % SZS output start Proof for theBenchmark
% 2.28/0.69  fof(f1015,plain,(
% 2.28/0.69    $false),
% 2.28/0.69    inference(avatar_sat_refutation,[],[f123,f124,f240,f1012])).
% 2.28/0.69  fof(f1012,plain,(
% 2.28/0.69    ~spl5_1 | spl5_2),
% 2.28/0.69    inference(avatar_contradiction_clause,[],[f1011])).
% 2.28/0.69  fof(f1011,plain,(
% 2.28/0.69    $false | (~spl5_1 | spl5_2)),
% 2.28/0.69    inference(subsumption_resolution,[],[f998,f122])).
% 2.28/0.69  fof(f122,plain,(
% 2.28/0.69    ~r1_tarski(sK2,sK3) | spl5_2),
% 2.28/0.69    inference(avatar_component_clause,[],[f120])).
% 2.28/0.69  fof(f120,plain,(
% 2.28/0.69    spl5_2 <=> r1_tarski(sK2,sK3)),
% 2.28/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.28/0.69  fof(f998,plain,(
% 2.28/0.69    r1_tarski(sK2,sK3) | ~spl5_1),
% 2.28/0.69    inference(resolution,[],[f958,f242])).
% 2.28/0.69  fof(f242,plain,(
% 2.28/0.69    r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) | ~spl5_1),
% 2.28/0.69    inference(subsumption_resolution,[],[f241,f55])).
% 2.28/0.69  fof(f55,plain,(
% 2.28/0.69    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 2.28/0.69    inference(cnf_transformation,[],[f46])).
% 2.28/0.69  fof(f46,plain,(
% 2.28/0.69    ((~r1_tarski(sK2,sK3) | ~r1_xboole_0(sK2,k3_subset_1(sK1,sK3))) & (r1_tarski(sK2,sK3) | r1_xboole_0(sK2,k3_subset_1(sK1,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.28/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f45,f44])).
% 2.28/0.69  fof(f44,plain,(
% 2.28/0.69    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK2,X2) | ~r1_xboole_0(sK2,k3_subset_1(sK1,X2))) & (r1_tarski(sK2,X2) | r1_xboole_0(sK2,k3_subset_1(sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 2.28/0.69    introduced(choice_axiom,[])).
% 2.28/0.69  fof(f45,plain,(
% 2.28/0.69    ? [X2] : ((~r1_tarski(sK2,X2) | ~r1_xboole_0(sK2,k3_subset_1(sK1,X2))) & (r1_tarski(sK2,X2) | r1_xboole_0(sK2,k3_subset_1(sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK1))) => ((~r1_tarski(sK2,sK3) | ~r1_xboole_0(sK2,k3_subset_1(sK1,sK3))) & (r1_tarski(sK2,sK3) | r1_xboole_0(sK2,k3_subset_1(sK1,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(sK1)))),
% 2.28/0.69    introduced(choice_axiom,[])).
% 2.28/0.69  fof(f43,plain,(
% 2.28/0.69    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.28/0.69    inference(flattening,[],[f42])).
% 2.28/0.69  fof(f42,plain,(
% 2.28/0.69    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.28/0.69    inference(nnf_transformation,[],[f33])).
% 2.28/0.69  fof(f33,plain,(
% 2.28/0.69    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.28/0.69    inference(ennf_transformation,[],[f31])).
% 2.28/0.69  fof(f31,negated_conjecture,(
% 2.28/0.69    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 2.28/0.69    inference(negated_conjecture,[],[f30])).
% 2.28/0.69  fof(f30,conjecture,(
% 2.28/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).
% 2.28/0.69  fof(f241,plain,(
% 2.28/0.69    r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK1)) | ~spl5_1),
% 2.28/0.69    inference(superposition,[],[f117,f75])).
% 2.28/0.69  fof(f75,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.28/0.69    inference(cnf_transformation,[],[f35])).
% 2.28/0.69  fof(f35,plain,(
% 2.28/0.69    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.28/0.69    inference(ennf_transformation,[],[f28])).
% 2.28/0.69  fof(f28,axiom,(
% 2.28/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.28/0.69  fof(f117,plain,(
% 2.28/0.69    r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) | ~spl5_1),
% 2.28/0.69    inference(avatar_component_clause,[],[f116])).
% 2.28/0.69  fof(f116,plain,(
% 2.28/0.69    spl5_1 <=> r1_xboole_0(sK2,k3_subset_1(sK1,sK3))),
% 2.28/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.28/0.69  fof(f958,plain,(
% 2.28/0.69    ( ! [X0] : (~r1_xboole_0(sK2,k4_xboole_0(sK1,X0)) | r1_tarski(sK2,X0)) )),
% 2.28/0.69    inference(resolution,[],[f835,f90])).
% 2.28/0.69  fof(f90,plain,(
% 2.28/0.69    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 2.28/0.69    inference(cnf_transformation,[],[f37])).
% 2.28/0.69  fof(f37,plain,(
% 2.28/0.69    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 2.28/0.69    inference(ennf_transformation,[],[f16])).
% 2.28/0.69  fof(f16,axiom,(
% 2.28/0.69    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 2.28/0.69  fof(f835,plain,(
% 2.28/0.69    ( ! [X12] : (~r1_xboole_0(sK1,k4_xboole_0(sK2,X12)) | r1_tarski(sK2,X12)) )),
% 2.28/0.69    inference(resolution,[],[f460,f172])).
% 2.28/0.69  fof(f172,plain,(
% 2.28/0.69    ( ! [X8] : (r1_xboole_0(sK2,X8) | ~r1_xboole_0(sK1,X8)) )),
% 2.28/0.69    inference(resolution,[],[f91,f161])).
% 2.28/0.69  fof(f161,plain,(
% 2.28/0.69    r1_tarski(sK2,sK1)),
% 2.28/0.69    inference(resolution,[],[f160,f150])).
% 2.28/0.69  fof(f150,plain,(
% 2.28/0.69    r2_hidden(sK2,k1_zfmisc_1(sK1))),
% 2.28/0.69    inference(subsumption_resolution,[],[f147,f58])).
% 2.28/0.69  fof(f58,plain,(
% 2.28/0.69    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.28/0.69    inference(cnf_transformation,[],[f29])).
% 2.28/0.69  fof(f29,axiom,(
% 2.28/0.69    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.28/0.69  fof(f147,plain,(
% 2.28/0.69    r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1))),
% 2.28/0.69    inference(resolution,[],[f71,f54])).
% 2.28/0.69  fof(f54,plain,(
% 2.28/0.69    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.28/0.69    inference(cnf_transformation,[],[f46])).
% 2.28/0.69  fof(f71,plain,(
% 2.28/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f47])).
% 2.28/0.69  fof(f47,plain,(
% 2.28/0.69    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.28/0.69    inference(nnf_transformation,[],[f34])).
% 2.28/0.69  fof(f34,plain,(
% 2.28/0.69    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.28/0.69    inference(ennf_transformation,[],[f27])).
% 2.28/0.69  fof(f27,axiom,(
% 2.28/0.69    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.28/0.69  fof(f160,plain,(
% 2.28/0.69    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.28/0.69    inference(resolution,[],[f78,f114])).
% 2.28/0.69  fof(f114,plain,(
% 2.28/0.69    ( ! [X0] : (sP0(X0,k1_zfmisc_1(X0))) )),
% 2.28/0.69    inference(equality_resolution,[],[f82])).
% 2.28/0.69  fof(f82,plain,(
% 2.28/0.69    ( ! [X0,X1] : (sP0(X0,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.28/0.69    inference(cnf_transformation,[],[f53])).
% 2.28/0.69  fof(f53,plain,(
% 2.28/0.69    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_zfmisc_1(X0) != X1))),
% 2.28/0.69    inference(nnf_transformation,[],[f41])).
% 2.28/0.69  fof(f41,plain,(
% 2.28/0.69    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> sP0(X0,X1))),
% 2.28/0.69    inference(definition_folding,[],[f25,f40])).
% 2.28/0.69  fof(f40,plain,(
% 2.28/0.69    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.28/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.28/0.69  fof(f25,axiom,(
% 2.28/0.69    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.28/0.69  fof(f78,plain,(
% 2.28/0.69    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r2_hidden(X3,X1) | r1_tarski(X3,X0)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f52])).
% 2.28/0.69  fof(f52,plain,(
% 2.28/0.69    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 2.28/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).
% 2.28/0.69  fof(f51,plain,(
% 2.28/0.69    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 2.28/0.69    introduced(choice_axiom,[])).
% 2.28/0.69  fof(f50,plain,(
% 2.28/0.69    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 2.28/0.69    inference(rectify,[],[f49])).
% 2.28/0.69  fof(f49,plain,(
% 2.28/0.69    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 2.28/0.69    inference(nnf_transformation,[],[f40])).
% 2.28/0.69  fof(f91,plain,(
% 2.28/0.69    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f39])).
% 2.28/0.69  fof(f39,plain,(
% 2.28/0.69    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.28/0.69    inference(flattening,[],[f38])).
% 2.28/0.69  fof(f38,plain,(
% 2.28/0.69    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.28/0.69    inference(ennf_transformation,[],[f15])).
% 2.28/0.69  fof(f15,axiom,(
% 2.28/0.69    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.28/0.69  fof(f460,plain,(
% 2.28/0.69    ( ! [X45,X44] : (~r1_xboole_0(X44,k4_xboole_0(X44,X45)) | r1_tarski(X44,X45)) )),
% 2.28/0.69    inference(superposition,[],[f310,f278])).
% 2.28/0.69  fof(f278,plain,(
% 2.28/0.69    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | ~r1_xboole_0(X1,X2)) )),
% 2.28/0.69    inference(forward_demodulation,[],[f272,f59])).
% 2.28/0.69  fof(f59,plain,(
% 2.28/0.69    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.28/0.69    inference(cnf_transformation,[],[f14])).
% 2.28/0.69  fof(f14,axiom,(
% 2.28/0.69    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.28/0.69  fof(f272,plain,(
% 2.28/0.69    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_xboole_0) | ~r1_xboole_0(X1,X2)) )),
% 2.28/0.69    inference(superposition,[],[f102,f110])).
% 2.28/0.69  fof(f110,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.28/0.69    inference(definition_unfolding,[],[f76,f70])).
% 2.28/0.69  fof(f70,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.28/0.69    inference(cnf_transformation,[],[f12])).
% 2.28/0.69  fof(f12,axiom,(
% 2.28/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.28/0.69  fof(f76,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f48])).
% 2.28/0.69  fof(f48,plain,(
% 2.28/0.69    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.28/0.69    inference(nnf_transformation,[],[f3])).
% 2.28/0.69  fof(f3,axiom,(
% 2.28/0.69    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.28/0.69  fof(f102,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.28/0.69    inference(definition_unfolding,[],[f68,f70])).
% 2.28/0.69  fof(f68,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.28/0.69    inference(cnf_transformation,[],[f5])).
% 2.28/0.69  fof(f5,axiom,(
% 2.28/0.69    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.28/0.69  fof(f310,plain,(
% 2.28/0.69    ( ! [X8,X7] : (r1_tarski(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X7)) )),
% 2.28/0.69    inference(superposition,[],[f104,f106])).
% 2.28/0.69  fof(f106,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.28/0.69    inference(definition_unfolding,[],[f64,f70,f70])).
% 2.28/0.69  fof(f64,plain,(
% 2.28/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f1])).
% 2.28/0.69  fof(f1,axiom,(
% 2.28/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.28/0.69  fof(f104,plain,(
% 2.28/0.69    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 2.28/0.69    inference(definition_unfolding,[],[f61,f70])).
% 2.28/0.69  fof(f61,plain,(
% 2.28/0.69    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f8])).
% 2.28/0.69  fof(f8,axiom,(
% 2.28/0.69    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.28/0.69  fof(f240,plain,(
% 2.28/0.69    spl5_1 | ~spl5_2),
% 2.28/0.69    inference(avatar_contradiction_clause,[],[f239])).
% 2.28/0.69  fof(f239,plain,(
% 2.28/0.69    $false | (spl5_1 | ~spl5_2)),
% 2.28/0.69    inference(subsumption_resolution,[],[f238,f121])).
% 2.28/0.69  fof(f121,plain,(
% 2.28/0.69    r1_tarski(sK2,sK3) | ~spl5_2),
% 2.28/0.69    inference(avatar_component_clause,[],[f120])).
% 2.28/0.69  fof(f238,plain,(
% 2.28/0.69    ~r1_tarski(sK2,sK3) | spl5_1),
% 2.28/0.69    inference(resolution,[],[f234,f89])).
% 2.28/0.69  fof(f89,plain,(
% 2.28/0.69    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.28/0.69    inference(cnf_transformation,[],[f36])).
% 2.28/0.69  fof(f36,plain,(
% 2.28/0.69    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.28/0.69    inference(ennf_transformation,[],[f17])).
% 2.28/0.69  fof(f17,axiom,(
% 2.28/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.28/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 2.28/0.69  fof(f234,plain,(
% 2.28/0.69    ~r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) | spl5_1),
% 2.28/0.69    inference(subsumption_resolution,[],[f231,f55])).
% 2.28/0.69  fof(f231,plain,(
% 2.28/0.69    ~r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK1)) | spl5_1),
% 2.28/0.69    inference(superposition,[],[f118,f75])).
% 2.28/0.69  fof(f118,plain,(
% 2.28/0.69    ~r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) | spl5_1),
% 2.28/0.69    inference(avatar_component_clause,[],[f116])).
% 2.28/0.69  fof(f124,plain,(
% 2.28/0.69    spl5_1 | spl5_2),
% 2.28/0.69    inference(avatar_split_clause,[],[f56,f120,f116])).
% 2.28/0.69  fof(f56,plain,(
% 2.28/0.69    r1_tarski(sK2,sK3) | r1_xboole_0(sK2,k3_subset_1(sK1,sK3))),
% 2.28/0.69    inference(cnf_transformation,[],[f46])).
% 2.28/0.69  fof(f123,plain,(
% 2.28/0.69    ~spl5_1 | ~spl5_2),
% 2.28/0.69    inference(avatar_split_clause,[],[f57,f120,f116])).
% 2.28/0.69  fof(f57,plain,(
% 2.28/0.69    ~r1_tarski(sK2,sK3) | ~r1_xboole_0(sK2,k3_subset_1(sK1,sK3))),
% 2.28/0.69    inference(cnf_transformation,[],[f46])).
% 2.28/0.69  % SZS output end Proof for theBenchmark
% 2.28/0.69  % (539)------------------------------
% 2.28/0.69  % (539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.69  % (539)Termination reason: Refutation
% 2.28/0.69  
% 2.28/0.69  % (539)Memory used [KB]: 6780
% 2.28/0.69  % (539)Time elapsed: 0.269 s
% 2.28/0.69  % (539)------------------------------
% 2.28/0.69  % (539)------------------------------
% 2.28/0.70  % (511)Success in time 0.339 s
%------------------------------------------------------------------------------
