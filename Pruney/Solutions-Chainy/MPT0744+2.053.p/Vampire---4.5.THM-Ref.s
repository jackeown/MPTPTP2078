%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:37 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 995 expanded)
%              Number of leaves         :   19 ( 295 expanded)
%              Depth                    :   25
%              Number of atoms          :  432 (3808 expanded)
%              Number of equality atoms :  145 ( 991 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f221,plain,(
    $false ),
    inference(subsumption_resolution,[],[f220,f103])).

fof(f103,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f72,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

% (25796)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (25792)Refutation not found, incomplete strategy% (25792)------------------------------
% (25792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25792)Termination reason: Refutation not found, incomplete strategy

% (25792)Memory used [KB]: 10746
% (25792)Time elapsed: 0.121 s
% (25792)------------------------------
% (25792)------------------------------
% (25818)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f40,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f220,plain,(
    ~ r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f208,f109])).

fof(f109,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f65,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f74,f82])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f73,f81])).

fof(f73,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f208,plain,(
    ~ r2_hidden(sK0,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(forward_demodulation,[],[f207,f186])).

fof(f186,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f184,f172])).

fof(f172,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f171,f150])).

fof(f150,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f147,f48])).

fof(f48,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r1_ordinal1(sK0,sK1)
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( r1_ordinal1(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK0,X1)
            | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK0,X1)
            | r2_hidden(sK0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK0,X1)
          | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK0,X1)
          | r2_hidden(sK0,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK0,sK1)
        | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
      & ( r1_ordinal1(sK0,sK1)
        | r2_hidden(sK0,k1_ordinal1(sK1)) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f147,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(sK0,X0)
      | sK0 = X0
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f69,f47])).

fof(f47,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f171,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,sK0)
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,sK0)
    | sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1 ),
    inference(resolution,[],[f169,f108])).

fof(f108,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f55,f81])).

fof(f55,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f169,plain,
    ( r2_hidden(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f168,f111])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f63,f83])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f168,plain,
    ( r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f166,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f166,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(subsumption_resolution,[],[f165,f47])).

fof(f165,plain,
    ( r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f164,f48])).

fof(f164,plain,
    ( r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f87,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f87,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f49,f85])).

fof(f85,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f70,f83,f84])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f75,f82])).

fof(f75,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f70,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f49,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f184,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f174,f110])).

fof(f110,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f64,f83])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f174,plain,
    ( ~ r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | sK0 = sK1 ),
    inference(resolution,[],[f173,f86])).

fof(f86,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f50,f85])).

fof(f50,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

% (25797)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f173,plain,
    ( r1_ordinal1(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f172,f127])).

fof(f127,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r1_ordinal1(sK0,sK1) ),
    inference(resolution,[],[f125,f71])).

fof(f125,plain,
    ( r1_tarski(sK1,sK0)
    | r1_ordinal1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f124,f48])).

fof(f124,plain,
    ( r1_ordinal1(sK0,sK1)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f123,f47])).

fof(f123,plain,
    ( r1_ordinal1(sK0,sK1)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f115,f51])).

fof(f115,plain,
    ( r1_ordinal1(sK1,sK0)
    | r1_ordinal1(sK0,sK1) ),
    inference(resolution,[],[f112,f48])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_ordinal1(sK0,X0)
      | r1_ordinal1(X0,sK0) ) ),
    inference(resolution,[],[f53,f47])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f207,plain,(
    ~ r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(subsumption_resolution,[],[f188,f116])).

fof(f116,plain,(
    r1_ordinal1(sK0,sK0) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,
    ( r1_ordinal1(sK0,sK0)
    | r1_ordinal1(sK0,sK0) ),
    inference(resolution,[],[f112,f47])).

fof(f188,plain,
    ( ~ r1_ordinal1(sK0,sK0)
    | ~ r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(backward_demodulation,[],[f86,f186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n012.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:13:07 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.52  % (25813)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (25805)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (25795)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (25793)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.53  % (25799)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.54  % (25798)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.54  % (25792)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.54  % (25795)Refutation found. Thanks to Tanya!
% 1.35/0.54  % SZS status Theorem for theBenchmark
% 1.35/0.54  % SZS output start Proof for theBenchmark
% 1.35/0.54  fof(f221,plain,(
% 1.35/0.54    $false),
% 1.35/0.54    inference(subsumption_resolution,[],[f220,f103])).
% 1.35/0.54  fof(f103,plain,(
% 1.35/0.54    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 1.35/0.54    inference(equality_resolution,[],[f102])).
% 1.35/0.54  fof(f102,plain,(
% 1.35/0.54    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 1.35/0.54    inference(equality_resolution,[],[f92])).
% 1.35/0.54  fof(f92,plain,(
% 1.35/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.35/0.54    inference(definition_unfolding,[],[f58,f81])).
% 1.35/0.54  fof(f81,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f72,f80])).
% 1.35/0.54  fof(f80,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f76,f79])).
% 1.35/0.54  fof(f79,plain,(
% 1.35/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f77,f78])).
% 1.35/0.54  fof(f78,plain,(
% 1.35/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f8])).
% 1.35/0.54  fof(f8,axiom,(
% 1.35/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.35/0.54  fof(f77,plain,(
% 1.35/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f7])).
% 1.35/0.54  fof(f7,axiom,(
% 1.35/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.35/0.54  fof(f76,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f6])).
% 1.35/0.54  fof(f6,axiom,(
% 1.35/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.35/0.54  fof(f72,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f5])).
% 1.35/0.54  fof(f5,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.35/0.54  fof(f58,plain,(
% 1.35/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.35/0.54    inference(cnf_transformation,[],[f41])).
% 1.35/0.54  % (25796)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.54  % (25792)Refutation not found, incomplete strategy% (25792)------------------------------
% 1.35/0.54  % (25792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (25792)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (25792)Memory used [KB]: 10746
% 1.35/0.54  % (25792)Time elapsed: 0.121 s
% 1.35/0.54  % (25792)------------------------------
% 1.35/0.54  % (25792)------------------------------
% 1.35/0.54  % (25818)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.54  fof(f41,plain,(
% 1.35/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.35/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 1.35/0.54  fof(f40,plain,(
% 1.35/0.54    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f39,plain,(
% 1.35/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.35/0.54    inference(rectify,[],[f38])).
% 1.35/0.54  fof(f38,plain,(
% 1.35/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.35/0.54    inference(flattening,[],[f37])).
% 1.35/0.54  fof(f37,plain,(
% 1.35/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.35/0.54    inference(nnf_transformation,[],[f27])).
% 1.35/0.54  fof(f27,plain,(
% 1.35/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.35/0.54    inference(ennf_transformation,[],[f2])).
% 1.35/0.54  fof(f2,axiom,(
% 1.35/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.35/0.54  fof(f220,plain,(
% 1.35/0.54    ~r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.35/0.54    inference(resolution,[],[f208,f109])).
% 1.35/0.54  fof(f109,plain,(
% 1.35/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.35/0.54    inference(equality_resolution,[],[f99])).
% 1.35/0.54  fof(f99,plain,(
% 1.35/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.35/0.54    inference(definition_unfolding,[],[f65,f83])).
% 1.35/0.54  fof(f83,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 1.35/0.54    inference(definition_unfolding,[],[f74,f82])).
% 1.35/0.54  fof(f82,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f73,f81])).
% 1.35/0.54  fof(f73,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f4])).
% 1.35/0.54  fof(f4,axiom,(
% 1.35/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.35/0.54  fof(f74,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f10])).
% 1.35/0.54  fof(f10,axiom,(
% 1.35/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.35/0.54  fof(f65,plain,(
% 1.35/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.35/0.54    inference(cnf_transformation,[],[f46])).
% 1.35/0.54  fof(f46,plain,(
% 1.35/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.35/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 1.35/0.54  fof(f45,plain,(
% 1.35/0.54    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f44,plain,(
% 1.35/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.35/0.54    inference(rectify,[],[f43])).
% 1.35/0.54  fof(f43,plain,(
% 1.35/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.35/0.54    inference(flattening,[],[f42])).
% 1.35/0.54  fof(f42,plain,(
% 1.35/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.35/0.54    inference(nnf_transformation,[],[f1])).
% 1.35/0.54  fof(f1,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.35/0.54  fof(f208,plain,(
% 1.35/0.54    ~r2_hidden(sK0,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.35/0.54    inference(forward_demodulation,[],[f207,f186])).
% 1.35/0.54  fof(f186,plain,(
% 1.35/0.54    sK0 = sK1),
% 1.35/0.54    inference(subsumption_resolution,[],[f184,f172])).
% 1.35/0.54  fof(f172,plain,(
% 1.35/0.54    r2_hidden(sK0,sK1) | sK0 = sK1),
% 1.35/0.54    inference(subsumption_resolution,[],[f171,f150])).
% 1.35/0.54  fof(f150,plain,(
% 1.35/0.54    r2_hidden(sK1,sK0) | sK0 = sK1 | r2_hidden(sK0,sK1)),
% 1.35/0.54    inference(resolution,[],[f147,f48])).
% 1.35/0.54  fof(f48,plain,(
% 1.35/0.54    v3_ordinal1(sK1)),
% 1.35/0.54    inference(cnf_transformation,[],[f35])).
% 1.35/0.54  fof(f35,plain,(
% 1.35/0.54    ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 1.35/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 1.35/0.54  fof(f33,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f34,plain,(
% 1.35/0.54    ? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f32,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.35/0.54    inference(flattening,[],[f31])).
% 1.35/0.54  fof(f31,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.35/0.54    inference(nnf_transformation,[],[f20])).
% 1.35/0.54  fof(f20,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.35/0.54    inference(ennf_transformation,[],[f19])).
% 1.35/0.54  fof(f19,negated_conjecture,(
% 1.35/0.54    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.35/0.54    inference(negated_conjecture,[],[f18])).
% 1.35/0.54  fof(f18,conjecture,(
% 1.35/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.35/0.54  fof(f147,plain,(
% 1.35/0.54    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(sK0,X0) | sK0 = X0 | r2_hidden(X0,sK0)) )),
% 1.35/0.54    inference(resolution,[],[f69,f47])).
% 1.35/0.54  fof(f47,plain,(
% 1.35/0.54    v3_ordinal1(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f35])).
% 1.35/0.54  fof(f69,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | r2_hidden(X1,X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f29])).
% 1.35/0.54  fof(f29,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.35/0.54    inference(flattening,[],[f28])).
% 1.35/0.54  fof(f28,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.35/0.54    inference(ennf_transformation,[],[f15])).
% 1.35/0.54  fof(f15,axiom,(
% 1.35/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 1.35/0.54  fof(f171,plain,(
% 1.35/0.54    r2_hidden(sK0,sK1) | ~r2_hidden(sK1,sK0) | sK0 = sK1),
% 1.35/0.54    inference(duplicate_literal_removal,[],[f170])).
% 1.35/0.54  fof(f170,plain,(
% 1.35/0.54    r2_hidden(sK0,sK1) | ~r2_hidden(sK1,sK0) | sK0 = sK1 | sK0 = sK1 | sK0 = sK1),
% 1.35/0.54    inference(resolution,[],[f169,f108])).
% 1.35/0.54  fof(f108,plain,(
% 1.35/0.54    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 1.35/0.54    inference(equality_resolution,[],[f95])).
% 1.35/0.54  fof(f95,plain,(
% 1.35/0.54    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.35/0.54    inference(definition_unfolding,[],[f55,f81])).
% 1.35/0.54  fof(f55,plain,(
% 1.35/0.54    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.35/0.54    inference(cnf_transformation,[],[f41])).
% 1.35/0.54  fof(f169,plain,(
% 1.35/0.54    r2_hidden(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | r2_hidden(sK0,sK1) | ~r2_hidden(sK1,sK0)),
% 1.35/0.54    inference(resolution,[],[f168,f111])).
% 1.35/0.54  fof(f111,plain,(
% 1.35/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 1.35/0.54    inference(equality_resolution,[],[f101])).
% 1.35/0.54  fof(f101,plain,(
% 1.35/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.35/0.54    inference(definition_unfolding,[],[f63,f83])).
% 1.35/0.54  fof(f63,plain,(
% 1.35/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.35/0.54    inference(cnf_transformation,[],[f46])).
% 1.35/0.54  fof(f168,plain,(
% 1.35/0.54    r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | ~r2_hidden(sK1,sK0)),
% 1.35/0.54    inference(resolution,[],[f166,f71])).
% 1.35/0.54  fof(f71,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f30])).
% 1.35/0.54  fof(f30,plain,(
% 1.35/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.35/0.54    inference(ennf_transformation,[],[f17])).
% 1.35/0.54  fof(f17,axiom,(
% 1.35/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.35/0.54  fof(f166,plain,(
% 1.35/0.54    r1_tarski(sK0,sK1) | r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 1.35/0.54    inference(subsumption_resolution,[],[f165,f47])).
% 1.35/0.54  fof(f165,plain,(
% 1.35/0.54    r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 1.35/0.54    inference(subsumption_resolution,[],[f164,f48])).
% 1.35/0.54  fof(f164,plain,(
% 1.35/0.54    r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 1.35/0.54    inference(resolution,[],[f87,f51])).
% 1.35/0.54  fof(f51,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f36])).
% 1.35/0.54  fof(f36,plain,(
% 1.35/0.54    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.35/0.54    inference(nnf_transformation,[],[f22])).
% 1.35/0.54  fof(f22,plain,(
% 1.35/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.35/0.54    inference(flattening,[],[f21])).
% 1.35/0.54  fof(f21,plain,(
% 1.35/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f14])).
% 1.35/0.54  fof(f14,axiom,(
% 1.35/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.35/0.54  fof(f87,plain,(
% 1.35/0.54    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 1.35/0.54    inference(definition_unfolding,[],[f49,f85])).
% 1.35/0.54  fof(f85,plain,(
% 1.35/0.54    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) )),
% 1.35/0.54    inference(definition_unfolding,[],[f70,f83,f84])).
% 1.35/0.54  fof(f84,plain,(
% 1.35/0.54    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f75,f82])).
% 1.35/0.54  fof(f75,plain,(
% 1.35/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f3])).
% 1.35/0.54  fof(f3,axiom,(
% 1.35/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.35/0.54  fof(f70,plain,(
% 1.35/0.54    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f13])).
% 1.35/0.54  fof(f13,axiom,(
% 1.35/0.54    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.35/0.54  fof(f49,plain,(
% 1.35/0.54    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.35/0.54    inference(cnf_transformation,[],[f35])).
% 1.35/0.54  fof(f184,plain,(
% 1.35/0.54    sK0 = sK1 | ~r2_hidden(sK0,sK1)),
% 1.35/0.54    inference(resolution,[],[f174,f110])).
% 1.35/0.54  fof(f110,plain,(
% 1.35/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 1.35/0.54    inference(equality_resolution,[],[f100])).
% 1.35/0.54  fof(f100,plain,(
% 1.35/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.35/0.54    inference(definition_unfolding,[],[f64,f83])).
% 1.35/0.54  fof(f64,plain,(
% 1.35/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 1.35/0.54    inference(cnf_transformation,[],[f46])).
% 1.35/0.54  fof(f174,plain,(
% 1.35/0.54    ~r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | sK0 = sK1),
% 1.35/0.54    inference(resolution,[],[f173,f86])).
% 1.35/0.54  fof(f86,plain,(
% 1.35/0.54    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 1.35/0.54    inference(definition_unfolding,[],[f50,f85])).
% 1.35/0.54  fof(f50,plain,(
% 1.35/0.54    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.35/0.54    inference(cnf_transformation,[],[f35])).
% 1.35/0.54  % (25797)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.54  fof(f173,plain,(
% 1.35/0.54    r1_ordinal1(sK0,sK1) | sK0 = sK1),
% 1.35/0.54    inference(resolution,[],[f172,f127])).
% 1.35/0.54  fof(f127,plain,(
% 1.35/0.54    ~r2_hidden(sK0,sK1) | r1_ordinal1(sK0,sK1)),
% 1.35/0.54    inference(resolution,[],[f125,f71])).
% 1.35/0.54  fof(f125,plain,(
% 1.35/0.54    r1_tarski(sK1,sK0) | r1_ordinal1(sK0,sK1)),
% 1.35/0.54    inference(subsumption_resolution,[],[f124,f48])).
% 1.35/0.54  fof(f124,plain,(
% 1.35/0.54    r1_ordinal1(sK0,sK1) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 1.35/0.54    inference(subsumption_resolution,[],[f123,f47])).
% 1.35/0.54  fof(f123,plain,(
% 1.35/0.54    r1_ordinal1(sK0,sK1) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 1.35/0.54    inference(resolution,[],[f115,f51])).
% 1.35/0.54  fof(f115,plain,(
% 1.35/0.54    r1_ordinal1(sK1,sK0) | r1_ordinal1(sK0,sK1)),
% 1.35/0.54    inference(resolution,[],[f112,f48])).
% 1.35/0.54  fof(f112,plain,(
% 1.35/0.54    ( ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(sK0,X0) | r1_ordinal1(X0,sK0)) )),
% 1.35/0.54    inference(resolution,[],[f53,f47])).
% 1.35/0.54  fof(f53,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_ordinal1(X1,X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f24])).
% 1.35/0.54  fof(f24,plain,(
% 1.35/0.54    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.35/0.54    inference(flattening,[],[f23])).
% 1.35/0.54  fof(f23,plain,(
% 1.35/0.54    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f12])).
% 1.35/0.54  fof(f12,axiom,(
% 1.35/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 1.35/0.54  fof(f207,plain,(
% 1.35/0.54    ~r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 1.35/0.54    inference(subsumption_resolution,[],[f188,f116])).
% 1.35/0.54  fof(f116,plain,(
% 1.35/0.54    r1_ordinal1(sK0,sK0)),
% 1.35/0.54    inference(duplicate_literal_removal,[],[f114])).
% 1.35/0.54  fof(f114,plain,(
% 1.35/0.54    r1_ordinal1(sK0,sK0) | r1_ordinal1(sK0,sK0)),
% 1.35/0.54    inference(resolution,[],[f112,f47])).
% 1.35/0.54  fof(f188,plain,(
% 1.35/0.54    ~r1_ordinal1(sK0,sK0) | ~r2_hidden(sK0,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 1.35/0.54    inference(backward_demodulation,[],[f86,f186])).
% 1.35/0.54  % SZS output end Proof for theBenchmark
% 1.35/0.54  % (25795)------------------------------
% 1.35/0.54  % (25795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (25795)Termination reason: Refutation
% 1.35/0.54  
% 1.35/0.54  % (25795)Memory used [KB]: 6268
% 1.35/0.54  % (25795)Time elapsed: 0.079 s
% 1.35/0.54  % (25795)------------------------------
% 1.35/0.54  % (25795)------------------------------
% 1.35/0.54  % (25794)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.54  % (25811)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.54  % (25802)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.54  % (25781)Success in time 0.184 s
%------------------------------------------------------------------------------
