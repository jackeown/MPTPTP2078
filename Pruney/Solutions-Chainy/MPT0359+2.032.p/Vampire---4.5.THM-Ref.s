%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:42 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 592 expanded)
%              Number of leaves         :   19 ( 153 expanded)
%              Depth                    :   25
%              Number of atoms          :  425 (2444 expanded)
%              Number of equality atoms :   83 ( 516 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (9263)------------------------------
% (9263)------------------------------
fof(f568,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f95,f131,f566])).

% (9256)Termination reason: Refutation not found, incomplete strategy

% (9256)Memory used [KB]: 10618
% (9256)Time elapsed: 0.172 s
% (9256)------------------------------
% (9256)------------------------------
% (9246)Refutation not found, incomplete strategy% (9246)------------------------------
% (9246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9246)Termination reason: Refutation not found, incomplete strategy

% (9246)Memory used [KB]: 1663
% (9246)Time elapsed: 0.174 s
% (9246)------------------------------
% (9246)------------------------------
% (9261)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (9255)Refutation not found, incomplete strategy% (9255)------------------------------
% (9255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9255)Termination reason: Refutation not found, incomplete strategy

% (9255)Memory used [KB]: 10618
% (9255)Time elapsed: 0.171 s
% (9255)------------------------------
% (9255)------------------------------
% (9254)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (9250)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f566,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f558])).

fof(f558,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f90,f552])).

fof(f552,plain,
    ( sK0 = sK1
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f530,f70])).

fof(f70,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f44,f67])).

fof(f67,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f46,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f530,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f236,f516])).

fof(f516,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,sK0)
    | ~ spl5_1 ),
    inference(superposition,[],[f443,f398])).

fof(f398,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)
    | ~ spl5_1 ),
    inference(superposition,[],[f393,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f393,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)
    | ~ spl5_1 ),
    inference(resolution,[],[f353,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

% (9253)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f353,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl5_1 ),
    inference(resolution,[],[f337,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f337,plain,
    ( ! [X12,X11] :
        ( r1_tarski(X11,X12)
        | ~ r1_tarski(X11,k1_xboole_0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f316,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f316,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,k1_xboole_0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f295,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f295,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f284])).

fof(f284,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f263,f226])).

fof(f226,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f138,f42])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f135,f52])).

fof(f135,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_subset_1(sK0,sK1))
      | r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f80,f133])).

fof(f133,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f39,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f55,f48])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

% (9269)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f263,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f227,f189])).

fof(f189,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,sK0)
        | r2_hidden(X1,sK1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f137,f156])).

fof(f156,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k3_subset_1(sK0,sK1))
        | r2_hidden(X4,sK1) )
    | ~ spl5_1 ),
    inference(superposition,[],[f82,f134])).

fof(f134,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f93,f49])).

fof(f93,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_1
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f137,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_subset_1(sK0,sK1))
      | r2_hidden(X2,sK1)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(superposition,[],[f78,f133])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f57,f48])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f227,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f158,f42])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f136,f52])).

fof(f136,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_subset_1(sK0,sK1))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(superposition,[],[f79,f133])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f56,f48])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f443,plain,
    ( ! [X0] : k5_xboole_0(sK0,sK0) = k3_xboole_0(k5_xboole_0(sK0,sK0),X0)
    | ~ spl5_1 ),
    inference(resolution,[],[f438,f49])).

fof(f438,plain,
    ( ! [X2] : r1_tarski(k5_xboole_0(sK0,sK0),X2)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f297,f307])).

fof(f307,plain,
    ( ! [X2] :
        ( r2_hidden(sK2(k5_xboole_0(sK0,sK0),X2),sK1)
        | r1_tarski(k5_xboole_0(sK0,sK0),X2) )
    | ~ spl5_1 ),
    inference(resolution,[],[f245,f53])).

fof(f245,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k5_xboole_0(sK0,sK0))
        | r2_hidden(X4,sK1) )
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f156,f228])).

fof(f228,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f133,f225])).

fof(f225,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f214,f49])).

fof(f214,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f190,f53])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(X0,sK1),sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f189,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f297,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK2(k5_xboole_0(sK0,sK0),X2),sK1)
        | r1_tarski(k5_xboole_0(sK0,sK0),X2) )
    | ~ spl5_1 ),
    inference(resolution,[],[f239,f53])).

fof(f239,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_xboole_0(sK0,sK0))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f136,f228])).

fof(f236,plain,
    ( sK1 = k3_subset_1(sK0,k5_xboole_0(sK0,sK0))
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f132,f228])).

fof(f132,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f39,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f90,plain,
    ( sK0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f131,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f99,f128])).

fof(f128,plain,
    ( r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,
    ( r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f104,f54])).

fof(f104,plain,
    ( ! [X2] :
        ( r2_hidden(sK2(k3_subset_1(sK0,sK0),X2),sK0)
        | r1_tarski(k3_subset_1(sK0,sK0),X2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f100,f53])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_subset_1(sK0,sK0))
        | r2_hidden(X0,sK0) )
    | ~ spl5_2 ),
    inference(superposition,[],[f80,f98])).

fof(f98,plain,
    ( k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f96,f71])).

fof(f96,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f39,f94])).

fof(f94,plain,
    ( sK0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f99,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f87,f94])).

fof(f87,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f95,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f92,f89,f86])).

fof(f92,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f69,f70])).

fof(f69,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f40,f67])).

fof(f40,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f91,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f84,f89,f86])).

fof(f84,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f68,f70])).

fof(f68,plain,
    ( sK1 != k3_subset_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f41,f67])).

fof(f41,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:51:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 1.53/0.56  % (9248)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.53/0.57  % (9257)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.53/0.57  % (9252)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.53/0.57  % (9257)Refutation not found, incomplete strategy% (9257)------------------------------
% 1.53/0.57  % (9257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (9257)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (9257)Memory used [KB]: 10618
% 1.53/0.57  % (9257)Time elapsed: 0.148 s
% 1.53/0.57  % (9257)------------------------------
% 1.53/0.57  % (9257)------------------------------
% 1.53/0.57  % (9251)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.53/0.58  % (9255)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.53/0.59  % (9275)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.53/0.59  % (9271)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.59  % (9256)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.53/0.59  % (9264)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.53/0.59  % (9247)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.53/0.59  % (9249)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.53/0.60  % (9258)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.53/0.60  % (9256)Refutation not found, incomplete strategy% (9256)------------------------------
% 1.53/0.60  % (9256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.60  % (9263)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.53/0.60  % (9263)Refutation not found, incomplete strategy% (9263)------------------------------
% 1.53/0.60  % (9263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.60  % (9246)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.53/0.60  % (9263)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.60  
% 1.53/0.60  % (9263)Memory used [KB]: 10618
% 1.53/0.60  % (9263)Time elapsed: 0.171 s
% 1.53/0.60  % (9248)Refutation found. Thanks to Tanya!
% 1.53/0.60  % SZS status Theorem for theBenchmark
% 1.53/0.60  % SZS output start Proof for theBenchmark
% 1.53/0.60  % (9263)------------------------------
% 1.53/0.60  % (9263)------------------------------
% 1.53/0.60  fof(f568,plain,(
% 1.53/0.60    $false),
% 1.53/0.60    inference(avatar_sat_refutation,[],[f91,f95,f131,f566])).
% 1.53/0.60  % (9256)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.60  
% 1.53/0.60  % (9256)Memory used [KB]: 10618
% 1.53/0.60  % (9256)Time elapsed: 0.172 s
% 1.53/0.60  % (9256)------------------------------
% 1.53/0.60  % (9256)------------------------------
% 1.53/0.60  % (9246)Refutation not found, incomplete strategy% (9246)------------------------------
% 1.53/0.60  % (9246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.60  % (9246)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.60  
% 1.53/0.60  % (9246)Memory used [KB]: 1663
% 1.53/0.60  % (9246)Time elapsed: 0.174 s
% 1.53/0.60  % (9246)------------------------------
% 1.53/0.60  % (9246)------------------------------
% 1.53/0.60  % (9261)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.53/0.60  % (9255)Refutation not found, incomplete strategy% (9255)------------------------------
% 1.53/0.60  % (9255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.60  % (9255)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.60  
% 1.53/0.60  % (9255)Memory used [KB]: 10618
% 1.53/0.60  % (9255)Time elapsed: 0.171 s
% 1.53/0.60  % (9255)------------------------------
% 1.53/0.60  % (9255)------------------------------
% 1.53/0.61  % (9254)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.53/0.61  % (9250)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.53/0.61  fof(f566,plain,(
% 1.53/0.61    ~spl5_1 | spl5_2),
% 1.53/0.61    inference(avatar_contradiction_clause,[],[f558])).
% 1.53/0.61  fof(f558,plain,(
% 1.53/0.61    $false | (~spl5_1 | spl5_2)),
% 1.53/0.61    inference(subsumption_resolution,[],[f90,f552])).
% 1.53/0.61  fof(f552,plain,(
% 1.53/0.61    sK0 = sK1 | ~spl5_1),
% 1.53/0.61    inference(forward_demodulation,[],[f530,f70])).
% 1.53/0.61  fof(f70,plain,(
% 1.53/0.61    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.53/0.61    inference(definition_unfolding,[],[f44,f67])).
% 1.53/0.61  fof(f67,plain,(
% 1.53/0.61    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.53/0.61    inference(definition_unfolding,[],[f46,f43])).
% 1.53/0.61  fof(f43,plain,(
% 1.53/0.61    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f8])).
% 1.53/0.61  fof(f8,axiom,(
% 1.53/0.61    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.53/0.61  fof(f46,plain,(
% 1.53/0.61    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.53/0.61    inference(cnf_transformation,[],[f12])).
% 1.53/0.61  fof(f12,axiom,(
% 1.53/0.61    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 1.53/0.61  fof(f44,plain,(
% 1.53/0.61    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.53/0.61    inference(cnf_transformation,[],[f9])).
% 1.53/0.61  fof(f9,axiom,(
% 1.53/0.61    ! [X0] : k2_subset_1(X0) = X0),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.53/0.61  fof(f530,plain,(
% 1.53/0.61    sK1 = k3_subset_1(sK0,k1_xboole_0) | ~spl5_1),
% 1.53/0.61    inference(backward_demodulation,[],[f236,f516])).
% 1.53/0.61  fof(f516,plain,(
% 1.53/0.61    k1_xboole_0 = k5_xboole_0(sK0,sK0) | ~spl5_1),
% 1.53/0.61    inference(superposition,[],[f443,f398])).
% 1.53/0.61  fof(f398,plain,(
% 1.53/0.61    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) ) | ~spl5_1),
% 1.53/0.61    inference(superposition,[],[f393,f47])).
% 1.53/0.61  fof(f47,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f1])).
% 1.53/0.61  fof(f1,axiom,(
% 1.53/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.53/0.61  fof(f393,plain,(
% 1.53/0.61    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) ) | ~spl5_1),
% 1.53/0.61    inference(resolution,[],[f353,f42])).
% 1.53/0.61  fof(f42,plain,(
% 1.53/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f7])).
% 1.53/0.61  % (9253)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.53/0.61  fof(f7,axiom,(
% 1.53/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.53/0.61  fof(f353,plain,(
% 1.53/0.61    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | k3_xboole_0(X0,X1) = X0) ) | ~spl5_1),
% 1.53/0.61    inference(resolution,[],[f337,f49])).
% 1.53/0.61  fof(f49,plain,(
% 1.53/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.53/0.61    inference(cnf_transformation,[],[f17])).
% 1.53/0.61  fof(f17,plain,(
% 1.53/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.53/0.61    inference(ennf_transformation,[],[f6])).
% 1.53/0.61  fof(f6,axiom,(
% 1.53/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.53/0.61  fof(f337,plain,(
% 1.53/0.61    ( ! [X12,X11] : (r1_tarski(X11,X12) | ~r1_tarski(X11,k1_xboole_0)) ) | ~spl5_1),
% 1.53/0.61    inference(resolution,[],[f316,f53])).
% 1.53/0.61  fof(f53,plain,(
% 1.53/0.61    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f28])).
% 1.53/0.61  fof(f28,plain,(
% 1.53/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.53/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 1.53/0.61  fof(f27,plain,(
% 1.53/0.61    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.53/0.61    introduced(choice_axiom,[])).
% 1.53/0.61  fof(f26,plain,(
% 1.53/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.53/0.61    inference(rectify,[],[f25])).
% 1.53/0.61  fof(f25,plain,(
% 1.53/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.53/0.61    inference(nnf_transformation,[],[f20])).
% 1.53/0.61  fof(f20,plain,(
% 1.53/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.53/0.61    inference(ennf_transformation,[],[f2])).
% 1.53/0.61  fof(f2,axiom,(
% 1.53/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.53/0.61  fof(f316,plain,(
% 1.53/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,k1_xboole_0)) ) | ~spl5_1),
% 1.53/0.61    inference(resolution,[],[f295,f52])).
% 1.53/0.61  fof(f52,plain,(
% 1.53/0.61    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f28])).
% 1.53/0.61  fof(f295,plain,(
% 1.53/0.61    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_1),
% 1.53/0.61    inference(duplicate_literal_removal,[],[f284])).
% 1.53/0.61  fof(f284,plain,(
% 1.53/0.61    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_1),
% 1.53/0.61    inference(resolution,[],[f263,f226])).
% 1.53/0.61  fof(f226,plain,(
% 1.53/0.61    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.53/0.61    inference(resolution,[],[f138,f42])).
% 1.53/0.61  fof(f138,plain,(
% 1.53/0.61    ( ! [X0,X1] : (~r1_tarski(X1,k3_subset_1(sK0,sK1)) | ~r2_hidden(X0,X1) | r2_hidden(X0,sK0)) )),
% 1.53/0.61    inference(resolution,[],[f135,f52])).
% 1.53/0.61  fof(f135,plain,(
% 1.53/0.61    ( ! [X0] : (~r2_hidden(X0,k3_subset_1(sK0,sK1)) | r2_hidden(X0,sK0)) )),
% 1.53/0.61    inference(superposition,[],[f80,f133])).
% 1.53/0.61  fof(f133,plain,(
% 1.53/0.61    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.53/0.61    inference(resolution,[],[f39,f71])).
% 1.53/0.61  fof(f71,plain,(
% 1.53/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.53/0.61    inference(definition_unfolding,[],[f50,f48])).
% 1.53/0.61  fof(f48,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.53/0.61    inference(cnf_transformation,[],[f5])).
% 1.53/0.61  fof(f5,axiom,(
% 1.53/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.53/0.61  fof(f50,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.53/0.61    inference(cnf_transformation,[],[f18])).
% 1.53/0.61  fof(f18,plain,(
% 1.53/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.61    inference(ennf_transformation,[],[f10])).
% 1.53/0.61  fof(f10,axiom,(
% 1.53/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.53/0.61  fof(f39,plain,(
% 1.53/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.53/0.61    inference(cnf_transformation,[],[f24])).
% 1.53/0.61  fof(f24,plain,(
% 1.53/0.61    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.53/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 1.53/0.61  fof(f23,plain,(
% 1.53/0.61    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.53/0.61    introduced(choice_axiom,[])).
% 1.53/0.61  fof(f22,plain,(
% 1.53/0.61    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.61    inference(flattening,[],[f21])).
% 1.53/0.61  fof(f21,plain,(
% 1.53/0.61    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.61    inference(nnf_transformation,[],[f16])).
% 1.53/0.61  fof(f16,plain,(
% 1.53/0.61    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.61    inference(ennf_transformation,[],[f15])).
% 1.53/0.61  fof(f15,negated_conjecture,(
% 1.53/0.61    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.53/0.61    inference(negated_conjecture,[],[f14])).
% 1.53/0.61  fof(f14,conjecture,(
% 1.53/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 1.53/0.61  fof(f80,plain,(
% 1.53/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 1.53/0.61    inference(equality_resolution,[],[f77])).
% 1.53/0.61  fof(f77,plain,(
% 1.53/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.53/0.61    inference(definition_unfolding,[],[f55,f48])).
% 1.53/0.61  fof(f55,plain,(
% 1.53/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.53/0.61    inference(cnf_transformation,[],[f33])).
% 1.53/0.61  fof(f33,plain,(
% 1.53/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.53/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.53/0.61  fof(f32,plain,(
% 1.53/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.53/0.61    introduced(choice_axiom,[])).
% 1.53/0.61  fof(f31,plain,(
% 1.53/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.53/0.61    inference(rectify,[],[f30])).
% 1.53/0.61  fof(f30,plain,(
% 1.53/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.53/0.61    inference(flattening,[],[f29])).
% 1.53/0.61  % (9269)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.53/0.61  fof(f29,plain,(
% 1.53/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.53/0.61    inference(nnf_transformation,[],[f4])).
% 1.53/0.61  fof(f4,axiom,(
% 1.53/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.53/0.61  fof(f263,plain,(
% 1.53/0.61    ( ! [X0] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_1),
% 1.53/0.61    inference(resolution,[],[f227,f189])).
% 1.53/0.61  fof(f189,plain,(
% 1.53/0.61    ( ! [X1] : (r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl5_1),
% 1.53/0.61    inference(duplicate_literal_removal,[],[f185])).
% 1.53/0.61  fof(f185,plain,(
% 1.53/0.61    ( ! [X1] : (r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0) | r2_hidden(X1,sK1)) ) | ~spl5_1),
% 1.53/0.61    inference(resolution,[],[f137,f156])).
% 1.53/0.61  fof(f156,plain,(
% 1.53/0.61    ( ! [X4] : (~r2_hidden(X4,k3_subset_1(sK0,sK1)) | r2_hidden(X4,sK1)) ) | ~spl5_1),
% 1.53/0.61    inference(superposition,[],[f82,f134])).
% 1.53/0.61  fof(f134,plain,(
% 1.53/0.61    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl5_1),
% 1.53/0.61    inference(resolution,[],[f93,f49])).
% 1.53/0.61  fof(f93,plain,(
% 1.53/0.61    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl5_1),
% 1.53/0.61    inference(avatar_component_clause,[],[f86])).
% 1.53/0.61  fof(f86,plain,(
% 1.53/0.61    spl5_1 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.53/0.61  fof(f82,plain,(
% 1.53/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 1.53/0.61    inference(equality_resolution,[],[f62])).
% 1.53/0.61  fof(f62,plain,(
% 1.53/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.53/0.61    inference(cnf_transformation,[],[f38])).
% 1.53/0.61  fof(f38,plain,(
% 1.53/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.53/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 1.53/0.61  fof(f37,plain,(
% 1.53/0.61    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.53/0.61    introduced(choice_axiom,[])).
% 1.53/0.61  fof(f36,plain,(
% 1.53/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.53/0.61    inference(rectify,[],[f35])).
% 1.53/0.61  fof(f35,plain,(
% 1.53/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.53/0.61    inference(flattening,[],[f34])).
% 1.53/0.61  fof(f34,plain,(
% 1.53/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.53/0.61    inference(nnf_transformation,[],[f3])).
% 1.53/0.61  fof(f3,axiom,(
% 1.53/0.61    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.53/0.61  fof(f137,plain,(
% 1.53/0.61    ( ! [X2] : (r2_hidden(X2,k3_subset_1(sK0,sK1)) | r2_hidden(X2,sK1) | ~r2_hidden(X2,sK0)) )),
% 1.53/0.61    inference(superposition,[],[f78,f133])).
% 1.53/0.61  fof(f78,plain,(
% 1.53/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.53/0.61    inference(equality_resolution,[],[f75])).
% 1.53/0.61  fof(f75,plain,(
% 1.53/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.53/0.61    inference(definition_unfolding,[],[f57,f48])).
% 1.53/0.61  fof(f57,plain,(
% 1.53/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.53/0.61    inference(cnf_transformation,[],[f33])).
% 1.53/0.61  fof(f227,plain,(
% 1.53/0.61    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.53/0.61    inference(resolution,[],[f158,f42])).
% 1.53/0.61  fof(f158,plain,(
% 1.53/0.61    ( ! [X0,X1] : (~r1_tarski(X1,k3_subset_1(sK0,sK1)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,sK1)) )),
% 1.53/0.61    inference(resolution,[],[f136,f52])).
% 1.53/0.61  fof(f136,plain,(
% 1.53/0.61    ( ! [X1] : (~r2_hidden(X1,k3_subset_1(sK0,sK1)) | ~r2_hidden(X1,sK1)) )),
% 1.53/0.61    inference(superposition,[],[f79,f133])).
% 1.53/0.61  fof(f79,plain,(
% 1.53/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.53/0.61    inference(equality_resolution,[],[f76])).
% 1.53/0.61  fof(f76,plain,(
% 1.53/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.53/0.61    inference(definition_unfolding,[],[f56,f48])).
% 1.53/0.61  fof(f56,plain,(
% 1.53/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.53/0.61    inference(cnf_transformation,[],[f33])).
% 1.53/0.61  fof(f443,plain,(
% 1.53/0.61    ( ! [X0] : (k5_xboole_0(sK0,sK0) = k3_xboole_0(k5_xboole_0(sK0,sK0),X0)) ) | ~spl5_1),
% 1.53/0.61    inference(resolution,[],[f438,f49])).
% 1.53/0.61  fof(f438,plain,(
% 1.53/0.61    ( ! [X2] : (r1_tarski(k5_xboole_0(sK0,sK0),X2)) ) | ~spl5_1),
% 1.53/0.61    inference(subsumption_resolution,[],[f297,f307])).
% 1.53/0.61  fof(f307,plain,(
% 1.53/0.61    ( ! [X2] : (r2_hidden(sK2(k5_xboole_0(sK0,sK0),X2),sK1) | r1_tarski(k5_xboole_0(sK0,sK0),X2)) ) | ~spl5_1),
% 1.53/0.61    inference(resolution,[],[f245,f53])).
% 1.53/0.61  fof(f245,plain,(
% 1.53/0.61    ( ! [X4] : (~r2_hidden(X4,k5_xboole_0(sK0,sK0)) | r2_hidden(X4,sK1)) ) | ~spl5_1),
% 1.53/0.61    inference(backward_demodulation,[],[f156,f228])).
% 1.53/0.61  fof(f228,plain,(
% 1.53/0.61    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK0) | ~spl5_1),
% 1.53/0.61    inference(backward_demodulation,[],[f133,f225])).
% 1.53/0.61  fof(f225,plain,(
% 1.53/0.61    sK0 = k3_xboole_0(sK0,sK1) | ~spl5_1),
% 1.53/0.61    inference(resolution,[],[f214,f49])).
% 1.53/0.61  fof(f214,plain,(
% 1.53/0.61    r1_tarski(sK0,sK1) | ~spl5_1),
% 1.53/0.61    inference(duplicate_literal_removal,[],[f212])).
% 1.53/0.61  fof(f212,plain,(
% 1.53/0.61    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1) | ~spl5_1),
% 1.53/0.61    inference(resolution,[],[f190,f53])).
% 1.53/0.61  fof(f190,plain,(
% 1.53/0.61    ( ! [X0] : (~r2_hidden(sK2(X0,sK1),sK0) | r1_tarski(X0,sK1)) ) | ~spl5_1),
% 1.53/0.61    inference(resolution,[],[f189,f54])).
% 1.53/0.61  fof(f54,plain,(
% 1.53/0.61    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f28])).
% 1.53/0.61  fof(f297,plain,(
% 1.53/0.61    ( ! [X2] : (~r2_hidden(sK2(k5_xboole_0(sK0,sK0),X2),sK1) | r1_tarski(k5_xboole_0(sK0,sK0),X2)) ) | ~spl5_1),
% 1.53/0.61    inference(resolution,[],[f239,f53])).
% 1.53/0.61  fof(f239,plain,(
% 1.53/0.61    ( ! [X1] : (~r2_hidden(X1,k5_xboole_0(sK0,sK0)) | ~r2_hidden(X1,sK1)) ) | ~spl5_1),
% 1.53/0.61    inference(backward_demodulation,[],[f136,f228])).
% 1.53/0.61  fof(f236,plain,(
% 1.53/0.61    sK1 = k3_subset_1(sK0,k5_xboole_0(sK0,sK0)) | ~spl5_1),
% 1.53/0.61    inference(backward_demodulation,[],[f132,f228])).
% 1.53/0.61  fof(f132,plain,(
% 1.53/0.61    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 1.53/0.61    inference(resolution,[],[f39,f51])).
% 1.53/0.61  fof(f51,plain,(
% 1.53/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.53/0.61    inference(cnf_transformation,[],[f19])).
% 1.53/0.61  fof(f19,plain,(
% 1.53/0.61    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.61    inference(ennf_transformation,[],[f11])).
% 1.53/0.61  fof(f11,axiom,(
% 1.53/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.53/0.61  fof(f90,plain,(
% 1.53/0.61    sK0 != sK1 | spl5_2),
% 1.53/0.61    inference(avatar_component_clause,[],[f89])).
% 1.53/0.61  fof(f89,plain,(
% 1.53/0.61    spl5_2 <=> sK0 = sK1),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.53/0.61  fof(f131,plain,(
% 1.53/0.61    spl5_1 | ~spl5_2),
% 1.53/0.61    inference(avatar_contradiction_clause,[],[f129])).
% 1.53/0.61  fof(f129,plain,(
% 1.53/0.61    $false | (spl5_1 | ~spl5_2)),
% 1.53/0.61    inference(subsumption_resolution,[],[f99,f128])).
% 1.53/0.61  fof(f128,plain,(
% 1.53/0.61    r1_tarski(k3_subset_1(sK0,sK0),sK0) | ~spl5_2),
% 1.53/0.61    inference(duplicate_literal_removal,[],[f127])).
% 1.53/0.61  fof(f127,plain,(
% 1.53/0.61    r1_tarski(k3_subset_1(sK0,sK0),sK0) | r1_tarski(k3_subset_1(sK0,sK0),sK0) | ~spl5_2),
% 1.53/0.61    inference(resolution,[],[f104,f54])).
% 1.53/0.61  fof(f104,plain,(
% 1.53/0.61    ( ! [X2] : (r2_hidden(sK2(k3_subset_1(sK0,sK0),X2),sK0) | r1_tarski(k3_subset_1(sK0,sK0),X2)) ) | ~spl5_2),
% 1.53/0.61    inference(resolution,[],[f100,f53])).
% 1.53/0.61  fof(f100,plain,(
% 1.53/0.61    ( ! [X0] : (~r2_hidden(X0,k3_subset_1(sK0,sK0)) | r2_hidden(X0,sK0)) ) | ~spl5_2),
% 1.53/0.61    inference(superposition,[],[f80,f98])).
% 1.53/0.61  fof(f98,plain,(
% 1.53/0.61    k3_subset_1(sK0,sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) | ~spl5_2),
% 1.53/0.61    inference(resolution,[],[f96,f71])).
% 1.53/0.61  fof(f96,plain,(
% 1.53/0.61    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl5_2),
% 1.53/0.61    inference(forward_demodulation,[],[f39,f94])).
% 1.53/0.61  fof(f94,plain,(
% 1.53/0.61    sK0 = sK1 | ~spl5_2),
% 1.53/0.61    inference(avatar_component_clause,[],[f89])).
% 1.53/0.61  fof(f99,plain,(
% 1.53/0.61    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (spl5_1 | ~spl5_2)),
% 1.53/0.61    inference(forward_demodulation,[],[f87,f94])).
% 1.53/0.61  fof(f87,plain,(
% 1.53/0.61    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl5_1),
% 1.53/0.61    inference(avatar_component_clause,[],[f86])).
% 1.53/0.61  fof(f95,plain,(
% 1.53/0.61    spl5_1 | spl5_2),
% 1.53/0.61    inference(avatar_split_clause,[],[f92,f89,f86])).
% 1.53/0.61  fof(f92,plain,(
% 1.53/0.61    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.53/0.61    inference(forward_demodulation,[],[f69,f70])).
% 1.53/0.61  fof(f69,plain,(
% 1.53/0.61    sK1 = k3_subset_1(sK0,k1_xboole_0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.53/0.61    inference(definition_unfolding,[],[f40,f67])).
% 1.53/0.61  fof(f40,plain,(
% 1.53/0.61    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.53/0.61    inference(cnf_transformation,[],[f24])).
% 1.53/0.61  fof(f91,plain,(
% 1.53/0.61    ~spl5_1 | ~spl5_2),
% 1.53/0.61    inference(avatar_split_clause,[],[f84,f89,f86])).
% 1.53/0.61  fof(f84,plain,(
% 1.53/0.61    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.53/0.61    inference(forward_demodulation,[],[f68,f70])).
% 1.53/0.61  fof(f68,plain,(
% 1.53/0.61    sK1 != k3_subset_1(sK0,k1_xboole_0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.53/0.61    inference(definition_unfolding,[],[f41,f67])).
% 1.53/0.61  fof(f41,plain,(
% 1.53/0.61    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.53/0.61    inference(cnf_transformation,[],[f24])).
% 1.53/0.61  % SZS output end Proof for theBenchmark
% 1.53/0.61  % (9248)------------------------------
% 1.53/0.61  % (9248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.61  % (9248)Termination reason: Refutation
% 1.53/0.61  
% 1.53/0.61  % (9248)Memory used [KB]: 11001
% 1.53/0.61  % (9248)Time elapsed: 0.179 s
% 1.53/0.61  % (9248)------------------------------
% 1.53/0.61  % (9248)------------------------------
% 1.53/0.61  % (9262)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.62  % (9245)Success in time 0.255 s
%------------------------------------------------------------------------------
