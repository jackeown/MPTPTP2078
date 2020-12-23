%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:55 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   41 (  64 expanded)
%              Number of leaves         :   11 (  18 expanded)
%              Depth                    :   14
%              Number of atoms          :  126 ( 223 expanded)
%              Number of equality atoms :   52 (  76 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f506,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f503])).

fof(f503,plain,(
    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f41,f497])).

fof(f497,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(forward_demodulation,[],[f496,f44])).

fof(f44,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f496,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,k1_setfam_1(k1_tarski(X1))) ),
    inference(subsumption_resolution,[],[f491,f111])).

fof(f111,plain,(
    ! [X5] : k1_xboole_0 != k1_tarski(X5) ),
    inference(subsumption_resolution,[],[f109,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f80,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f109,plain,(
    ! [X5] :
      ( k1_xboole_0 != k1_tarski(X5)
      | r2_hidden(X5,k1_xboole_0) ) ),
    inference(superposition,[],[f52,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f49,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(f491,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,k1_setfam_1(k1_tarski(X1)))
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(superposition,[],[f202,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f202,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1))
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f190,f111])).

fof(f190,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f57,f44])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f41,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).

fof(f23,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

% (26717)Refutation not found, incomplete strategy% (26717)------------------------------
% (26717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26717)Termination reason: Refutation not found, incomplete strategy

% (26717)Memory used [KB]: 6140
% (26717)Time elapsed: 0.175 s
% (26717)------------------------------
% (26717)------------------------------
fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.56  % (26704)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (26706)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (26696)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (26704)Refutation not found, incomplete strategy% (26704)------------------------------
% 0.22/0.56  % (26704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (26699)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (26694)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.56  % (26714)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (26714)Refutation not found, incomplete strategy% (26714)------------------------------
% 0.22/0.56  % (26714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (26714)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (26714)Memory used [KB]: 10618
% 0.22/0.56  % (26714)Time elapsed: 0.111 s
% 0.22/0.56  % (26714)------------------------------
% 0.22/0.56  % (26714)------------------------------
% 0.22/0.57  % (26704)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (26704)Memory used [KB]: 1663
% 0.22/0.57  % (26704)Time elapsed: 0.129 s
% 0.22/0.57  % (26704)------------------------------
% 0.22/0.57  % (26704)------------------------------
% 0.22/0.58  % (26712)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.71/0.58  % (26707)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.71/0.58  % (26707)Refutation not found, incomplete strategy% (26707)------------------------------
% 1.71/0.58  % (26707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.58  % (26707)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.58  
% 1.71/0.58  % (26707)Memory used [KB]: 1663
% 1.71/0.58  % (26707)Time elapsed: 0.108 s
% 1.71/0.58  % (26707)------------------------------
% 1.71/0.58  % (26707)------------------------------
% 1.71/0.58  % (26711)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.71/0.58  % (26700)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.71/0.59  % (26705)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.71/0.59  % (26693)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.71/0.59  % (26706)Refutation not found, incomplete strategy% (26706)------------------------------
% 1.71/0.59  % (26706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.59  % (26706)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.59  
% 1.71/0.59  % (26706)Memory used [KB]: 10618
% 1.71/0.59  % (26706)Time elapsed: 0.150 s
% 1.71/0.59  % (26706)------------------------------
% 1.71/0.59  % (26706)------------------------------
% 1.71/0.59  % (26713)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.71/0.59  % (26719)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.71/0.59  % (26697)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.71/0.59  % (26719)Refutation not found, incomplete strategy% (26719)------------------------------
% 1.71/0.59  % (26719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.59  % (26719)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.59  
% 1.71/0.59  % (26719)Memory used [KB]: 1663
% 1.71/0.59  % (26719)Time elapsed: 0.168 s
% 1.71/0.59  % (26719)------------------------------
% 1.71/0.59  % (26719)------------------------------
% 1.71/0.59  % (26716)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.71/0.59  % (26715)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.85/0.60  % (26703)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.85/0.60  % (26708)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.85/0.60  % (26690)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.85/0.60  % (26708)Refutation not found, incomplete strategy% (26708)------------------------------
% 1.85/0.60  % (26708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.60  % (26708)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.60  
% 1.85/0.60  % (26708)Memory used [KB]: 1663
% 1.85/0.60  % (26708)Time elapsed: 0.172 s
% 1.85/0.60  % (26708)------------------------------
% 1.85/0.60  % (26708)------------------------------
% 1.85/0.60  % (26692)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.85/0.60  % (26699)Refutation found. Thanks to Tanya!
% 1.85/0.60  % SZS status Theorem for theBenchmark
% 1.85/0.60  % (26695)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.85/0.60  % (26717)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.85/0.60  % (26698)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.85/0.60  % SZS output start Proof for theBenchmark
% 1.85/0.60  fof(f506,plain,(
% 1.85/0.60    $false),
% 1.85/0.60    inference(trivial_inequality_removal,[],[f503])).
% 1.85/0.60  fof(f503,plain,(
% 1.85/0.60    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1)),
% 1.85/0.60    inference(superposition,[],[f41,f497])).
% 1.85/0.60  fof(f497,plain,(
% 1.85/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.85/0.60    inference(forward_demodulation,[],[f496,f44])).
% 1.85/0.60  fof(f44,plain,(
% 1.85/0.60    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.85/0.60    inference(cnf_transformation,[],[f16])).
% 1.85/0.60  fof(f16,axiom,(
% 1.85/0.60    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.85/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.85/0.60  fof(f496,plain,(
% 1.85/0.60    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,k1_setfam_1(k1_tarski(X1)))) )),
% 1.85/0.60    inference(subsumption_resolution,[],[f491,f111])).
% 1.85/0.60  fof(f111,plain,(
% 1.85/0.60    ( ! [X5] : (k1_xboole_0 != k1_tarski(X5)) )),
% 1.85/0.60    inference(subsumption_resolution,[],[f109,f91])).
% 1.85/0.60  fof(f91,plain,(
% 1.85/0.60    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 1.85/0.60    inference(superposition,[],[f80,f42])).
% 1.85/0.60  fof(f42,plain,(
% 1.85/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.85/0.60    inference(cnf_transformation,[],[f8])).
% 1.85/0.60  fof(f8,axiom,(
% 1.85/0.60    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.85/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.85/0.60  fof(f80,plain,(
% 1.85/0.60    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.85/0.60    inference(equality_resolution,[],[f65])).
% 1.85/0.60  fof(f65,plain,(
% 1.85/0.60    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.85/0.60    inference(cnf_transformation,[],[f38])).
% 1.85/0.60  fof(f38,plain,(
% 1.85/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.85/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 1.85/0.60  fof(f37,plain,(
% 1.85/0.60    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.85/0.60    introduced(choice_axiom,[])).
% 1.85/0.60  fof(f36,plain,(
% 1.85/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.85/0.60    inference(rectify,[],[f35])).
% 1.85/0.60  fof(f35,plain,(
% 1.85/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.85/0.60    inference(flattening,[],[f34])).
% 1.85/0.60  fof(f34,plain,(
% 1.85/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.85/0.60    inference(nnf_transformation,[],[f3])).
% 1.85/0.60  fof(f3,axiom,(
% 1.85/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.85/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.85/0.60  fof(f109,plain,(
% 1.85/0.60    ( ! [X5] : (k1_xboole_0 != k1_tarski(X5) | r2_hidden(X5,k1_xboole_0)) )),
% 1.85/0.60    inference(superposition,[],[f52,f82])).
% 1.85/0.60  fof(f82,plain,(
% 1.85/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.85/0.60    inference(superposition,[],[f49,f43])).
% 1.85/0.60  fof(f43,plain,(
% 1.85/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.85/0.60    inference(cnf_transformation,[],[f5])).
% 1.85/0.60  fof(f5,axiom,(
% 1.85/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.85/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.85/0.60  fof(f49,plain,(
% 1.85/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.85/0.60    inference(cnf_transformation,[],[f1])).
% 1.85/0.60  fof(f1,axiom,(
% 1.85/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.85/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.85/0.60  fof(f52,plain,(
% 1.85/0.60    ( ! [X0,X1] : (k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) | r2_hidden(X1,X0)) )),
% 1.85/0.60    inference(cnf_transformation,[],[f21])).
% 1.85/0.60  fof(f21,plain,(
% 1.85/0.60    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 1.85/0.60    inference(ennf_transformation,[],[f13])).
% 1.85/0.60  fof(f13,axiom,(
% 1.85/0.60    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 1.85/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).
% 1.85/0.60  fof(f491,plain,(
% 1.85/0.60    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,k1_setfam_1(k1_tarski(X1))) | k1_xboole_0 = k1_tarski(X1)) )),
% 1.85/0.60    inference(superposition,[],[f202,f50])).
% 1.85/0.60  fof(f50,plain,(
% 1.85/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.85/0.60    inference(cnf_transformation,[],[f11])).
% 1.85/0.60  fof(f11,axiom,(
% 1.85/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.85/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 1.85/0.60  fof(f202,plain,(
% 1.85/0.60    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1)) | k1_xboole_0 = X1) )),
% 1.85/0.60    inference(subsumption_resolution,[],[f190,f111])).
% 1.85/0.60  fof(f190,plain,(
% 1.85/0.60    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = k1_tarski(X0)) )),
% 1.85/0.60    inference(superposition,[],[f57,f44])).
% 1.85/0.60  fof(f57,plain,(
% 1.85/0.60    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.85/0.60    inference(cnf_transformation,[],[f22])).
% 1.85/0.60  fof(f22,plain,(
% 1.85/0.60    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.85/0.60    inference(ennf_transformation,[],[f15])).
% 1.85/0.60  fof(f15,axiom,(
% 1.85/0.60    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.85/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).
% 1.85/0.60  fof(f41,plain,(
% 1.85/0.60    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.85/0.60    inference(cnf_transformation,[],[f24])).
% 1.85/0.60  fof(f24,plain,(
% 1.85/0.60    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.85/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).
% 1.85/0.60  fof(f23,plain,(
% 1.85/0.60    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.85/0.60    introduced(choice_axiom,[])).
% 1.85/0.60  fof(f20,plain,(
% 1.85/0.60    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 1.85/0.60    inference(ennf_transformation,[],[f18])).
% 1.85/0.60  % (26717)Refutation not found, incomplete strategy% (26717)------------------------------
% 1.85/0.60  % (26717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.60  % (26717)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.60  
% 1.85/0.60  % (26717)Memory used [KB]: 6140
% 1.85/0.60  % (26717)Time elapsed: 0.175 s
% 1.85/0.60  % (26717)------------------------------
% 1.85/0.60  % (26717)------------------------------
% 1.85/0.60  fof(f18,negated_conjecture,(
% 1.85/0.60    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.85/0.60    inference(negated_conjecture,[],[f17])).
% 1.85/0.60  fof(f17,conjecture,(
% 1.85/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.85/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.85/0.60  % SZS output end Proof for theBenchmark
% 1.85/0.60  % (26699)------------------------------
% 1.85/0.60  % (26699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.60  % (26699)Termination reason: Refutation
% 1.85/0.60  
% 1.85/0.60  % (26699)Memory used [KB]: 2046
% 1.85/0.60  % (26699)Time elapsed: 0.154 s
% 1.85/0.60  % (26699)------------------------------
% 1.85/0.60  % (26699)------------------------------
% 1.85/0.60  % (26691)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.85/0.60  % (26689)Success in time 0.233 s
%------------------------------------------------------------------------------
