%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:02 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 271 expanded)
%              Number of leaves         :   12 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  155 (1073 expanded)
%              Number of equality atoms :  124 ( 960 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(subsumption_resolution,[],[f324,f294])).

fof(f294,plain,(
    sK2 != k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f35,f293])).

fof(f293,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f292,f110])).

fof(f110,plain,
    ( sK1 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f100])).

fof(f100,plain,
    ( sK1 != sK2
    | sK1 != sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f34,f99])).

fof(f99,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f50,f63])).

fof(f63,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f44,f33])).

fof(f33,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f34,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f292,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f284,f109])).

fof(f109,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f102])).

fof(f102,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f36,f99])).

fof(f36,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f284,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f160,f244])).

fof(f244,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f105,f133])).

fof(f133,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f111,f68])).

fof(f68,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f46,f38])).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

% (19608)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f111,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f54,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f105,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f90,f99])).

fof(f90,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f84,f46])).

fof(f84,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0)) ),
    inference(superposition,[],[f49,f33])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f160,plain,(
    ! [X0] :
      ( sK1 = k3_xboole_0(sK1,X0)
      | k1_xboole_0 = k3_xboole_0(sK1,X0)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f106,f45])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f106,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | k1_xboole_0 = X0
      | sK1 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f50,f99])).

fof(f35,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f324,plain,(
    sK2 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f321,f38])).

fof(f321,plain,(
    k1_tarski(sK0) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f133,f306])).

fof(f306,plain,(
    k1_xboole_0 = k5_xboole_0(sK2,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f305,f143])).

fof(f143,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f45,f45,f60,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f60,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f305,plain,(
    k5_xboole_0(sK2,k1_tarski(sK0)) = k3_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f299,f68])).

fof(f299,plain,(
    k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f84,f293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:10:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (19591)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.49  % (19599)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.50  % (19577)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (19582)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (19583)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (19595)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (19583)Refutation not found, incomplete strategy% (19583)------------------------------
% 0.20/0.51  % (19583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19583)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19583)Memory used [KB]: 10618
% 0.20/0.51  % (19583)Time elapsed: 0.106 s
% 0.20/0.51  % (19583)------------------------------
% 0.20/0.51  % (19583)------------------------------
% 0.20/0.51  % (19581)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (19581)Refutation not found, incomplete strategy% (19581)------------------------------
% 0.20/0.51  % (19581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19581)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19581)Memory used [KB]: 10746
% 0.20/0.51  % (19581)Time elapsed: 0.116 s
% 0.20/0.51  % (19581)------------------------------
% 0.20/0.51  % (19581)------------------------------
% 0.20/0.51  % (19578)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (19584)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (19584)Refutation not found, incomplete strategy% (19584)------------------------------
% 0.20/0.52  % (19584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19584)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (19584)Memory used [KB]: 10618
% 0.20/0.52  % (19584)Time elapsed: 0.116 s
% 0.20/0.52  % (19584)------------------------------
% 0.20/0.52  % (19584)------------------------------
% 0.20/0.52  % (19593)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (19595)Refutation not found, incomplete strategy% (19595)------------------------------
% 0.20/0.52  % (19595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19595)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (19595)Memory used [KB]: 10746
% 0.20/0.52  % (19595)Time elapsed: 0.076 s
% 0.20/0.52  % (19595)------------------------------
% 0.20/0.52  % (19595)------------------------------
% 0.20/0.52  % (19587)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (19579)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (19585)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (19573)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (19576)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.53  % (19574)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.53  % (19602)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.53  % (19601)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.53  % (19598)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.53  % (19575)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.54  % (19588)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.54  % (19588)Refutation not found, incomplete strategy% (19588)------------------------------
% 1.35/0.54  % (19588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (19588)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (19588)Memory used [KB]: 6140
% 1.35/0.54  % (19588)Time elapsed: 0.001 s
% 1.35/0.54  % (19588)------------------------------
% 1.35/0.54  % (19588)------------------------------
% 1.35/0.54  % (19592)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.54  % (19580)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.54  % (19594)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.54  % (19600)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.54  % (19575)Refutation not found, incomplete strategy% (19575)------------------------------
% 1.35/0.54  % (19575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (19594)Refutation not found, incomplete strategy% (19594)------------------------------
% 1.35/0.54  % (19594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (19594)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (19594)Memory used [KB]: 1791
% 1.35/0.54  % (19594)Time elapsed: 0.140 s
% 1.35/0.54  % (19594)------------------------------
% 1.35/0.54  % (19594)------------------------------
% 1.35/0.54  % (19575)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (19575)Memory used [KB]: 10746
% 1.35/0.54  % (19575)Time elapsed: 0.138 s
% 1.35/0.54  % (19575)------------------------------
% 1.35/0.54  % (19575)------------------------------
% 1.35/0.54  % (19586)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.54  % (19596)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.54  % (19590)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.54  % (19597)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.55  % (19590)Refutation not found, incomplete strategy% (19590)------------------------------
% 1.35/0.55  % (19590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (19590)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (19590)Memory used [KB]: 10618
% 1.35/0.55  % (19590)Time elapsed: 0.145 s
% 1.35/0.55  % (19590)------------------------------
% 1.35/0.55  % (19590)------------------------------
% 1.35/0.55  % (19589)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.02/0.65  % (19604)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.02/0.65  % (19607)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.02/0.66  % (19609)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.02/0.66  % (19610)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.02/0.67  % (19603)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.02/0.67  % (19606)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.02/0.67  % (19605)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.02/0.67  % (19609)Refutation found. Thanks to Tanya!
% 2.02/0.67  % SZS status Theorem for theBenchmark
% 2.02/0.68  % SZS output start Proof for theBenchmark
% 2.02/0.68  fof(f325,plain,(
% 2.02/0.68    $false),
% 2.02/0.68    inference(subsumption_resolution,[],[f324,f294])).
% 2.02/0.68  fof(f294,plain,(
% 2.02/0.68    sK2 != k1_tarski(sK0)),
% 2.02/0.68    inference(subsumption_resolution,[],[f35,f293])).
% 2.02/0.68  fof(f293,plain,(
% 2.02/0.68    k1_xboole_0 = sK1),
% 2.02/0.68    inference(subsumption_resolution,[],[f292,f110])).
% 2.02/0.68  fof(f110,plain,(
% 2.02/0.68    sK1 != sK2 | k1_xboole_0 = sK1),
% 2.02/0.68    inference(trivial_inequality_removal,[],[f100])).
% 2.02/0.68  fof(f100,plain,(
% 2.02/0.68    sK1 != sK2 | sK1 != sK1 | k1_xboole_0 = sK1),
% 2.02/0.68    inference(superposition,[],[f34,f99])).
% 2.02/0.68  fof(f99,plain,(
% 2.02/0.68    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 2.02/0.68    inference(resolution,[],[f50,f63])).
% 2.02/0.68  fof(f63,plain,(
% 2.02/0.68    r1_tarski(sK1,k1_tarski(sK0))),
% 2.02/0.68    inference(superposition,[],[f44,f33])).
% 2.02/0.68  fof(f33,plain,(
% 2.02/0.68    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.02/0.68    inference(cnf_transformation,[],[f30])).
% 2.02/0.68  fof(f30,plain,(
% 2.02/0.68    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.02/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f29])).
% 2.02/0.68  fof(f29,plain,(
% 2.02/0.68    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.02/0.68    introduced(choice_axiom,[])).
% 2.02/0.68  fof(f25,plain,(
% 2.02/0.68    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.02/0.68    inference(ennf_transformation,[],[f22])).
% 2.02/0.68  fof(f22,negated_conjecture,(
% 2.02/0.68    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.02/0.68    inference(negated_conjecture,[],[f21])).
% 2.02/0.68  fof(f21,conjecture,(
% 2.02/0.68    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.02/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.02/0.68  fof(f44,plain,(
% 2.02/0.68    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.02/0.68    inference(cnf_transformation,[],[f8])).
% 2.02/0.68  fof(f8,axiom,(
% 2.02/0.68    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.02/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.02/0.68  fof(f50,plain,(
% 2.02/0.68    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.02/0.68    inference(cnf_transformation,[],[f32])).
% 2.02/0.68  fof(f32,plain,(
% 2.02/0.68    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.02/0.68    inference(flattening,[],[f31])).
% 2.02/0.68  fof(f31,plain,(
% 2.02/0.68    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.02/0.68    inference(nnf_transformation,[],[f19])).
% 2.02/0.68  fof(f19,axiom,(
% 2.02/0.68    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.02/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.02/0.68  fof(f34,plain,(
% 2.02/0.68    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.02/0.68    inference(cnf_transformation,[],[f30])).
% 2.02/0.68  fof(f292,plain,(
% 2.02/0.68    sK1 = sK2 | k1_xboole_0 = sK1),
% 2.02/0.68    inference(subsumption_resolution,[],[f284,f109])).
% 2.02/0.68  fof(f109,plain,(
% 2.02/0.68    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 2.02/0.68    inference(trivial_inequality_removal,[],[f102])).
% 2.02/0.68  fof(f102,plain,(
% 2.02/0.68    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 2.02/0.68    inference(superposition,[],[f36,f99])).
% 2.02/0.68  fof(f36,plain,(
% 2.02/0.68    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.02/0.68    inference(cnf_transformation,[],[f30])).
% 2.02/0.68  fof(f284,plain,(
% 2.02/0.68    sK1 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 2.02/0.68    inference(duplicate_literal_removal,[],[f282])).
% 2.02/0.68  fof(f282,plain,(
% 2.02/0.68    sK1 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 2.02/0.68    inference(superposition,[],[f160,f244])).
% 2.02/0.68  fof(f244,plain,(
% 2.02/0.68    sK2 = k3_xboole_0(sK1,sK2) | k1_xboole_0 = sK1),
% 2.02/0.68    inference(backward_demodulation,[],[f105,f133])).
% 2.02/0.68  fof(f133,plain,(
% 2.02/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.02/0.68    inference(forward_demodulation,[],[f111,f68])).
% 2.02/0.68  fof(f68,plain,(
% 2.02/0.68    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.02/0.68    inference(superposition,[],[f46,f38])).
% 2.02/0.68  fof(f38,plain,(
% 2.02/0.68    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.02/0.68    inference(cnf_transformation,[],[f5])).
% 2.02/0.68  % (19608)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.30/0.68  fof(f5,axiom,(
% 2.30/0.68    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.30/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.30/0.68  fof(f46,plain,(
% 2.30/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f1])).
% 2.30/0.68  fof(f1,axiom,(
% 2.30/0.68    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.30/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.30/0.68  fof(f111,plain,(
% 2.30/0.68    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.30/0.68    inference(superposition,[],[f54,f37])).
% 2.30/0.68  fof(f37,plain,(
% 2.30/0.68    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f10])).
% 2.30/0.68  fof(f10,axiom,(
% 2.30/0.68    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.30/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.30/0.68  fof(f54,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.30/0.68    inference(cnf_transformation,[],[f9])).
% 2.30/0.68  fof(f9,axiom,(
% 2.30/0.68    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.30/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.30/0.68  fof(f105,plain,(
% 2.30/0.68    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | k1_xboole_0 = sK1),
% 2.30/0.68    inference(superposition,[],[f90,f99])).
% 2.30/0.68  fof(f90,plain,(
% 2.30/0.68    k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2))),
% 2.30/0.68    inference(superposition,[],[f84,f46])).
% 2.30/0.68  fof(f84,plain,(
% 2.30/0.68    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0))),
% 2.30/0.68    inference(superposition,[],[f49,f33])).
% 2.30/0.68  fof(f49,plain,(
% 2.30/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.30/0.68    inference(cnf_transformation,[],[f11])).
% 2.30/0.68  fof(f11,axiom,(
% 2.30/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.30/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.30/0.68  fof(f160,plain,(
% 2.30/0.68    ( ! [X0] : (sK1 = k3_xboole_0(sK1,X0) | k1_xboole_0 = k3_xboole_0(sK1,X0) | k1_xboole_0 = sK1) )),
% 2.30/0.68    inference(resolution,[],[f106,f45])).
% 2.30/0.68  fof(f45,plain,(
% 2.30/0.68    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f4])).
% 2.30/0.68  fof(f4,axiom,(
% 2.30/0.68    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.30/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.30/0.68  fof(f106,plain,(
% 2.30/0.68    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | sK1 = X0 | k1_xboole_0 = sK1) )),
% 2.30/0.68    inference(superposition,[],[f50,f99])).
% 2.30/0.68  fof(f35,plain,(
% 2.30/0.68    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.30/0.68    inference(cnf_transformation,[],[f30])).
% 2.30/0.68  fof(f324,plain,(
% 2.30/0.68    sK2 = k1_tarski(sK0)),
% 2.30/0.68    inference(forward_demodulation,[],[f321,f38])).
% 2.30/0.68  fof(f321,plain,(
% 2.30/0.68    k1_tarski(sK0) = k5_xboole_0(sK2,k1_xboole_0)),
% 2.30/0.68    inference(superposition,[],[f133,f306])).
% 2.30/0.68  fof(f306,plain,(
% 2.30/0.68    k1_xboole_0 = k5_xboole_0(sK2,k1_tarski(sK0))),
% 2.30/0.68    inference(forward_demodulation,[],[f305,f143])).
% 2.30/0.68  fof(f143,plain,(
% 2.30/0.68    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 2.30/0.68    inference(unit_resulting_resolution,[],[f45,f45,f60,f55])).
% 2.30/0.68  fof(f55,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f28])).
% 2.30/0.68  fof(f28,plain,(
% 2.30/0.68    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.30/0.68    inference(flattening,[],[f27])).
% 2.30/0.68  fof(f27,plain,(
% 2.30/0.68    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.30/0.68    inference(ennf_transformation,[],[f7])).
% 2.30/0.68  fof(f7,axiom,(
% 2.30/0.68    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 2.30/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 2.30/0.68  fof(f60,plain,(
% 2.30/0.68    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.30/0.68    inference(equality_resolution,[],[f40])).
% 2.30/0.68  fof(f40,plain,(
% 2.30/0.68    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f26])).
% 2.30/0.68  fof(f26,plain,(
% 2.30/0.68    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 2.30/0.68    inference(ennf_transformation,[],[f6])).
% 2.30/0.68  fof(f6,axiom,(
% 2.30/0.68    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 2.30/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 2.30/0.68  fof(f305,plain,(
% 2.30/0.68    k5_xboole_0(sK2,k1_tarski(sK0)) = k3_xboole_0(k1_xboole_0,sK2)),
% 2.30/0.68    inference(forward_demodulation,[],[f299,f68])).
% 2.30/0.68  fof(f299,plain,(
% 2.30/0.68    k3_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k1_tarski(sK0))),
% 2.30/0.68    inference(backward_demodulation,[],[f84,f293])).
% 2.30/0.68  % SZS output end Proof for theBenchmark
% 2.30/0.68  % (19609)------------------------------
% 2.30/0.68  % (19609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.68  % (19609)Termination reason: Refutation
% 2.30/0.68  
% 2.30/0.68  % (19609)Memory used [KB]: 1918
% 2.30/0.68  % (19609)Time elapsed: 0.077 s
% 2.30/0.68  % (19609)------------------------------
% 2.30/0.68  % (19609)------------------------------
% 2.30/0.68  % (19572)Success in time 0.319 s
%------------------------------------------------------------------------------
