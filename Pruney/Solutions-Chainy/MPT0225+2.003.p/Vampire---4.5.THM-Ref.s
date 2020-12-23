%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 139 expanded)
%              Number of leaves         :   11 (  42 expanded)
%              Depth                    :   16
%              Number of atoms          :  117 ( 225 expanded)
%              Number of equality atoms :   65 ( 146 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f313,plain,(
    $false ),
    inference(subsumption_resolution,[],[f306,f107])).

fof(f107,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f100,f105])).

fof(f105,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f100,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f100,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f45,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f306,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f69,f293])).

fof(f293,plain,(
    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f292,f170])).

fof(f170,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | k4_xboole_0(X1,X1) != X1 ) ),
    inference(resolution,[],[f96,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f96,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f90,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f70,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f292,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f283])).

fof(f283,plain,
    ( sK0 != sK0
    | k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    inference(superposition,[],[f61,f271])).

fof(f271,plain,
    ( sK0 = sK1
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    inference(resolution,[],[f259,f67])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_enumset1(X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f37,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f58])).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f259,plain,
    ( r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    inference(resolution,[],[f238,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_enumset1(X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f238,plain,
    ( ~ r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f237])).

fof(f237,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0)
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | ~ r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(superposition,[],[f110,f31])).

fof(f110,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f109,f90])).

fof(f109,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))
    | k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,
    ( sK0 != sK0
    | k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))
    | k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(superposition,[],[f61,f60])).

fof(f60,plain,
    ( sK0 = sK1
    | k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f29,f59,f59,f59])).

fof(f29,plain,
    ( sK0 = sK1
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f61,plain,
    ( sK0 != sK1
    | k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f28,f59,f59,f59])).

fof(f28,plain,
    ( sK0 != sK1
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X2] : r2_hidden(X2,k1_enumset1(X2,X2,X2)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_enumset1(X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f36,f59])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:43:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (7475)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (7482)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (7470)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (7486)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (7472)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (7469)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (7474)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (7483)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (7484)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (7478)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (7478)Refutation not found, incomplete strategy% (7478)------------------------------
% 0.21/0.55  % (7478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7478)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7478)Memory used [KB]: 6268
% 0.21/0.55  % (7478)Time elapsed: 0.128 s
% 0.21/0.55  % (7478)------------------------------
% 0.21/0.55  % (7478)------------------------------
% 0.21/0.55  % (7468)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (7471)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (7493)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (7467)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (7468)Refutation not found, incomplete strategy% (7468)------------------------------
% 0.21/0.55  % (7468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7493)Refutation not found, incomplete strategy% (7493)------------------------------
% 0.21/0.55  % (7493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7493)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7493)Memory used [KB]: 6268
% 0.21/0.55  % (7493)Time elapsed: 0.137 s
% 0.21/0.55  % (7493)------------------------------
% 0.21/0.55  % (7493)------------------------------
% 0.21/0.55  % (7468)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7468)Memory used [KB]: 1663
% 0.21/0.55  % (7468)Time elapsed: 0.117 s
% 0.21/0.55  % (7468)------------------------------
% 0.21/0.55  % (7468)------------------------------
% 0.21/0.55  % (7495)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (7490)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (7483)Refutation not found, incomplete strategy% (7483)------------------------------
% 0.21/0.55  % (7483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7483)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7483)Memory used [KB]: 10618
% 0.21/0.55  % (7483)Time elapsed: 0.123 s
% 0.21/0.55  % (7483)------------------------------
% 0.21/0.55  % (7483)------------------------------
% 0.21/0.55  % (7496)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (7496)Refutation not found, incomplete strategy% (7496)------------------------------
% 0.21/0.55  % (7496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7496)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7496)Memory used [KB]: 1663
% 0.21/0.55  % (7496)Time elapsed: 0.001 s
% 0.21/0.55  % (7496)------------------------------
% 0.21/0.55  % (7496)------------------------------
% 0.21/0.55  % (7491)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (7477)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (7485)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (7484)Refutation not found, incomplete strategy% (7484)------------------------------
% 0.21/0.55  % (7484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7484)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7484)Memory used [KB]: 1791
% 0.21/0.55  % (7484)Time elapsed: 0.137 s
% 0.21/0.55  % (7484)------------------------------
% 0.21/0.55  % (7484)------------------------------
% 0.21/0.55  % (7491)Refutation not found, incomplete strategy% (7491)------------------------------
% 0.21/0.55  % (7491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7491)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7491)Memory used [KB]: 10746
% 0.21/0.55  % (7491)Time elapsed: 0.121 s
% 0.21/0.55  % (7491)------------------------------
% 0.21/0.55  % (7491)------------------------------
% 0.21/0.56  % (7485)Refutation not found, incomplete strategy% (7485)------------------------------
% 0.21/0.56  % (7485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7485)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7485)Memory used [KB]: 1663
% 0.21/0.56  % (7485)Time elapsed: 0.139 s
% 0.21/0.56  % (7485)------------------------------
% 0.21/0.56  % (7485)------------------------------
% 0.21/0.56  % (7476)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (7479)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (7494)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (7473)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (7494)Refutation not found, incomplete strategy% (7494)------------------------------
% 0.21/0.56  % (7494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7494)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7494)Memory used [KB]: 6268
% 0.21/0.56  % (7494)Time elapsed: 0.146 s
% 0.21/0.56  % (7494)------------------------------
% 0.21/0.56  % (7494)------------------------------
% 0.21/0.56  % (7487)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (7480)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (7486)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f313,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(subsumption_resolution,[],[f306,f107])).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(backward_demodulation,[],[f100,f105])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f100,f49])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f45,f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(rectify,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.56  fof(f306,plain,(
% 0.21/0.56    r2_hidden(sK0,k1_xboole_0)),
% 0.21/0.56    inference(superposition,[],[f69,f293])).
% 0.21/0.56  fof(f293,plain,(
% 0.21/0.56    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 0.21/0.56    inference(subsumption_resolution,[],[f292,f170])).
% 0.21/0.56  fof(f170,plain,(
% 0.21/0.56    ( ! [X1] : (k1_xboole_0 = X1 | k4_xboole_0(X1,X1) != X1) )),
% 0.21/0.56    inference(resolution,[],[f96,f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(superposition,[],[f90,f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f70,f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.56  fof(f292,plain,(
% 0.21/0.56    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f283])).
% 0.21/0.56  fof(f283,plain,(
% 0.21/0.56    sK0 != sK0 | k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 0.21/0.56    inference(superposition,[],[f61,f271])).
% 0.21/0.56  fof(f271,plain,(
% 0.21/0.56    sK0 = sK1 | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 0.21/0.56    inference(resolution,[],[f259,f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_enumset1(X0,X0,X0)) | X0 = X2) )),
% 0.21/0.56    inference(equality_resolution,[],[f64])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.21/0.56    inference(definition_unfolding,[],[f37,f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f41,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,axiom,(
% 0.21/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.59/0.56  fof(f41,plain,(
% 1.59/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f14])).
% 1.59/0.56  fof(f14,axiom,(
% 1.59/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.59/0.56  fof(f37,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.59/0.56    inference(cnf_transformation,[],[f13])).
% 1.59/0.56  fof(f13,axiom,(
% 1.59/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.59/0.56  fof(f259,plain,(
% 1.59/0.56    r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 1.59/0.56    inference(resolution,[],[f238,f66])).
% 1.59/0.56  fof(f66,plain,(
% 1.59/0.56    ( ! [X0,X1] : (r1_xboole_0(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.59/0.56    inference(definition_unfolding,[],[f40,f59])).
% 1.59/0.56  fof(f40,plain,(
% 1.59/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f23])).
% 1.59/0.56  fof(f23,plain,(
% 1.59/0.56    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.59/0.56    inference(ennf_transformation,[],[f18])).
% 1.59/0.56  fof(f18,axiom,(
% 1.59/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.59/0.56  fof(f238,plain,(
% 1.59/0.56    ~r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 1.59/0.56    inference(trivial_inequality_removal,[],[f237])).
% 1.59/0.56  fof(f237,plain,(
% 1.59/0.56    k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | ~r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 1.59/0.56    inference(superposition,[],[f110,f31])).
% 1.59/0.56  fof(f110,plain,(
% 1.59/0.56    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 1.59/0.56    inference(forward_demodulation,[],[f109,f90])).
% 1.59/0.56  fof(f109,plain,(
% 1.59/0.56    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) | k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 1.59/0.56    inference(trivial_inequality_removal,[],[f108])).
% 1.59/0.56  fof(f108,plain,(
% 1.59/0.56    sK0 != sK0 | k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) | k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 1.59/0.56    inference(superposition,[],[f61,f60])).
% 1.59/0.56  fof(f60,plain,(
% 1.59/0.56    sK0 = sK1 | k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 1.59/0.56    inference(definition_unfolding,[],[f29,f59,f59,f59])).
% 1.59/0.56  fof(f29,plain,(
% 1.59/0.56    sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.59/0.56    inference(cnf_transformation,[],[f22])).
% 1.59/0.56  fof(f22,plain,(
% 1.59/0.56    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 1.59/0.56    inference(ennf_transformation,[],[f20])).
% 1.59/0.56  fof(f20,negated_conjecture,(
% 1.59/0.56    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.59/0.56    inference(negated_conjecture,[],[f19])).
% 1.59/0.56  fof(f19,conjecture,(
% 1.59/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.59/0.56  fof(f61,plain,(
% 1.59/0.56    sK0 != sK1 | k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 1.59/0.56    inference(definition_unfolding,[],[f28,f59,f59,f59])).
% 1.59/0.56  fof(f28,plain,(
% 1.59/0.56    sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.59/0.56    inference(cnf_transformation,[],[f22])).
% 1.59/0.56  fof(f69,plain,(
% 1.59/0.56    ( ! [X2] : (r2_hidden(X2,k1_enumset1(X2,X2,X2))) )),
% 1.59/0.56    inference(equality_resolution,[],[f68])).
% 1.59/0.56  fof(f68,plain,(
% 1.59/0.56    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_enumset1(X2,X2,X2) != X1) )),
% 1.59/0.56    inference(equality_resolution,[],[f65])).
% 1.59/0.56  fof(f65,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 1.59/0.56    inference(definition_unfolding,[],[f36,f59])).
% 1.59/0.56  fof(f36,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.59/0.56    inference(cnf_transformation,[],[f13])).
% 1.59/0.56  % SZS output end Proof for theBenchmark
% 1.59/0.56  % (7486)------------------------------
% 1.59/0.56  % (7486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.56  % (7486)Termination reason: Refutation
% 1.59/0.56  
% 1.59/0.56  % (7486)Memory used [KB]: 1791
% 1.59/0.56  % (7486)Time elapsed: 0.150 s
% 1.59/0.56  % (7486)------------------------------
% 1.59/0.56  % (7486)------------------------------
% 1.59/0.57  % (7466)Success in time 0.199 s
%------------------------------------------------------------------------------
