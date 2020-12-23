%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0875+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:48 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 159 expanded)
%              Number of leaves         :    4 (  33 expanded)
%              Depth                    :   22
%              Number of atoms          :  137 ( 704 expanded)
%              Number of equality atoms :  136 ( 703 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,plain,(
    $false ),
    inference(subsumption_resolution,[],[f45,f25])).

% (30700)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (30713)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (30694)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (30717)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (30717)Refutation not found, incomplete strategy% (30717)------------------------------
% (30717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30717)Termination reason: Refutation not found, incomplete strategy

% (30717)Memory used [KB]: 1663
% (30717)Time elapsed: 0.113 s
% (30717)------------------------------
% (30717)------------------------------
% (30696)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (30709)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (30709)Refutation not found, incomplete strategy% (30709)------------------------------
% (30709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30709)Termination reason: Refutation not found, incomplete strategy

% (30709)Memory used [KB]: 6140
% (30709)Time elapsed: 0.004 s
% (30709)------------------------------
% (30709)------------------------------
fof(f25,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f45,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f44,f25])).

fof(f44,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2) ),
    inference(forward_demodulation,[],[f41,f40])).

fof(f40,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f39,f25])).

fof(f39,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f38,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f37])).

fof(f37,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f22,f35])).

fof(f35,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f34,f24])).

fof(f34,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f33])).

fof(f33,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f21,f31])).

fof(f31,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f30,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f29])).

fof(f29,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f28])).

fof(f28,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f17,f20])).

fof(f20,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f15,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 )
    & ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
      | ( k1_xboole_0 != sK2
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( ( k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 )
        & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
          | ( k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) )
   => ( ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
      & ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
        | ( k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 ) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <~> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
      <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f21,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f14,f16])).

fof(f14,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f13,f16])).

fof(f13,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f23,f40])).

fof(f23,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f12,f16])).

fof(f12,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
