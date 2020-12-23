%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:30 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   63 (  77 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :   15
%              Number of atoms          :  147 ( 167 expanded)
%              Number of equality atoms :   75 (  91 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f478,plain,(
    $false ),
    inference(resolution,[],[f447,f52])).

fof(f52,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f447,plain,(
    ! [X4] : ~ r1_xboole_0(k1_tarski(sK0),X4) ),
    inference(trivial_inequality_removal,[],[f446])).

fof(f446,plain,(
    ! [X4] :
      ( k1_tarski(sK0) != k1_tarski(sK0)
      | ~ r1_xboole_0(k1_tarski(sK0),X4) ) ),
    inference(superposition,[],[f304,f336])).

fof(f336,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X0) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f327,f53])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f327,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f60,f283])).

fof(f283,plain,(
    ! [X6,X5] :
      ( k1_xboole_0 = k4_xboole_0(X5,X5)
      | ~ r1_xboole_0(X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,(
    ! [X6,X5] :
      ( k1_xboole_0 = k4_xboole_0(X5,X5)
      | ~ r1_xboole_0(X5,X6)
      | ~ r1_xboole_0(X5,X6) ) ),
    inference(superposition,[],[f125,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f64,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f125,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k4_xboole_0(X0,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f62,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f304,plain,(
    k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f302,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f302,plain,(
    k2_tarski(sK0,sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f100,f300])).

fof(f300,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f298,f89])).

fof(f89,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
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

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f298,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f290,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f290,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f289])).

fof(f289,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | sK0 = sK1 ),
    inference(superposition,[],[f251,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f251,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f100,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = k5_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f60,f68])).

fof(f100,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f51,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f51,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f35])).

fof(f35,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.56  % (21495)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (21494)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (21503)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.57  % (21510)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.58  % (21511)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.58  % (21502)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.58  % (21502)Refutation not found, incomplete strategy% (21502)------------------------------
% 0.21/0.58  % (21502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (21502)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (21502)Memory used [KB]: 1663
% 0.21/0.59  % (21502)Time elapsed: 0.147 s
% 0.21/0.59  % (21502)------------------------------
% 0.21/0.59  % (21502)------------------------------
% 0.21/0.60  % (21488)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.60  % (21500)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.60  % (21506)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.60  % (21501)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.60  % (21507)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.69/0.60  % (21515)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.69/0.60  % (21512)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.69/0.60  % (21492)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.69/0.61  % (21512)Refutation not found, incomplete strategy% (21512)------------------------------
% 1.69/0.61  % (21512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.61  % (21512)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.61  
% 1.69/0.61  % (21512)Memory used [KB]: 10746
% 1.69/0.61  % (21512)Time elapsed: 0.170 s
% 1.69/0.61  % (21512)------------------------------
% 1.69/0.61  % (21512)------------------------------
% 1.69/0.61  % (21514)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.69/0.61  % (21493)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.69/0.61  % (21491)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.69/0.61  % (21514)Refutation not found, incomplete strategy% (21514)------------------------------
% 1.69/0.61  % (21514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.61  % (21514)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.61  
% 1.69/0.61  % (21514)Memory used [KB]: 6268
% 1.69/0.61  % (21514)Time elapsed: 0.179 s
% 1.69/0.61  % (21514)------------------------------
% 1.69/0.61  % (21514)------------------------------
% 1.69/0.61  % (21489)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.69/0.61  % (21489)Refutation not found, incomplete strategy% (21489)------------------------------
% 1.69/0.61  % (21489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.61  % (21489)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.61  
% 1.69/0.61  % (21489)Memory used [KB]: 1663
% 1.69/0.61  % (21489)Time elapsed: 0.131 s
% 1.69/0.61  % (21489)------------------------------
% 1.69/0.61  % (21489)------------------------------
% 1.69/0.61  % (21499)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.69/0.61  % (21504)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.69/0.61  % (21497)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.69/0.61  % (21513)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.69/0.61  % (21505)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.69/0.61  % (21508)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.69/0.61  % (21490)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.69/0.61  % (21496)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.69/0.61  % (21509)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.69/0.62  % (21498)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.69/0.62  % (21516)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.69/0.62  % (21517)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.69/0.62  % (21517)Refutation not found, incomplete strategy% (21517)------------------------------
% 1.69/0.62  % (21517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.62  % (21517)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.62  
% 1.69/0.62  % (21517)Memory used [KB]: 1663
% 1.69/0.62  % (21517)Time elapsed: 0.189 s
% 1.69/0.62  % (21517)------------------------------
% 1.69/0.62  % (21517)------------------------------
% 1.69/0.62  % (21506)Refutation not found, incomplete strategy% (21506)------------------------------
% 1.69/0.62  % (21506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.62  % (21506)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.62  
% 1.69/0.62  % (21506)Memory used [KB]: 1663
% 1.69/0.62  % (21506)Time elapsed: 0.189 s
% 1.99/0.62  % (21506)------------------------------
% 1.99/0.62  % (21506)------------------------------
% 1.99/0.62  % (21515)Refutation not found, incomplete strategy% (21515)------------------------------
% 1.99/0.62  % (21515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.62  % (21515)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.62  
% 1.99/0.62  % (21515)Memory used [KB]: 6268
% 1.99/0.62  % (21515)Time elapsed: 0.194 s
% 1.99/0.62  % (21515)------------------------------
% 1.99/0.62  % (21515)------------------------------
% 1.99/0.63  % (21504)Refutation not found, incomplete strategy% (21504)------------------------------
% 1.99/0.63  % (21504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.63  % (21504)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.63  
% 1.99/0.63  % (21504)Memory used [KB]: 10618
% 1.99/0.63  % (21504)Time elapsed: 0.188 s
% 1.99/0.63  % (21504)------------------------------
% 1.99/0.63  % (21504)------------------------------
% 1.99/0.63  % (21497)Refutation found. Thanks to Tanya!
% 1.99/0.63  % SZS status Theorem for theBenchmark
% 1.99/0.63  % (21505)Refutation not found, incomplete strategy% (21505)------------------------------
% 1.99/0.63  % (21505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.63  % (21505)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.63  
% 1.99/0.63  % (21505)Memory used [KB]: 1791
% 1.99/0.63  % (21505)Time elapsed: 0.146 s
% 1.99/0.63  % (21505)------------------------------
% 1.99/0.63  % (21505)------------------------------
% 1.99/0.63  % SZS output start Proof for theBenchmark
% 1.99/0.63  fof(f478,plain,(
% 1.99/0.63    $false),
% 1.99/0.63    inference(resolution,[],[f447,f52])).
% 1.99/0.63  fof(f52,plain,(
% 1.99/0.63    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f8])).
% 1.99/0.63  fof(f8,axiom,(
% 1.99/0.63    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.99/0.63  fof(f447,plain,(
% 1.99/0.63    ( ! [X4] : (~r1_xboole_0(k1_tarski(sK0),X4)) )),
% 1.99/0.63    inference(trivial_inequality_removal,[],[f446])).
% 1.99/0.63  fof(f446,plain,(
% 1.99/0.63    ( ! [X4] : (k1_tarski(sK0) != k1_tarski(sK0) | ~r1_xboole_0(k1_tarski(sK0),X4)) )),
% 1.99/0.63    inference(superposition,[],[f304,f336])).
% 1.99/0.63  fof(f336,plain,(
% 1.99/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X0) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.99/0.63    inference(forward_demodulation,[],[f327,f53])).
% 1.99/0.63  fof(f53,plain,(
% 1.99/0.63    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.99/0.63    inference(cnf_transformation,[],[f7])).
% 1.99/0.63  fof(f7,axiom,(
% 1.99/0.63    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.99/0.63  fof(f327,plain,(
% 1.99/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.99/0.63    inference(superposition,[],[f60,f283])).
% 1.99/0.63  fof(f283,plain,(
% 1.99/0.63    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,X5) | ~r1_xboole_0(X5,X6)) )),
% 1.99/0.63    inference(duplicate_literal_removal,[],[f257])).
% 1.99/0.63  fof(f257,plain,(
% 1.99/0.63    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,X5) | ~r1_xboole_0(X5,X6) | ~r1_xboole_0(X5,X6)) )),
% 1.99/0.63    inference(superposition,[],[f125,f105])).
% 1.99/0.63  fof(f105,plain,(
% 1.99/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.99/0.63    inference(resolution,[],[f64,f55])).
% 1.99/0.63  fof(f55,plain,(
% 1.99/0.63    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.99/0.63    inference(cnf_transformation,[],[f38])).
% 1.99/0.63  fof(f38,plain,(
% 1.99/0.63    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.99/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f37])).
% 1.99/0.63  fof(f37,plain,(
% 1.99/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.99/0.63    introduced(choice_axiom,[])).
% 1.99/0.63  fof(f29,plain,(
% 1.99/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.99/0.63    inference(ennf_transformation,[],[f4])).
% 1.99/0.63  fof(f4,axiom,(
% 1.99/0.63    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.99/0.63  fof(f64,plain,(
% 1.99/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f40])).
% 1.99/0.63  fof(f40,plain,(
% 1.99/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.99/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f39])).
% 1.99/0.63  fof(f39,plain,(
% 1.99/0.63    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.99/0.63    introduced(choice_axiom,[])).
% 1.99/0.63  fof(f30,plain,(
% 1.99/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.99/0.63    inference(ennf_transformation,[],[f27])).
% 1.99/0.63  fof(f27,plain,(
% 1.99/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.99/0.63    inference(rectify,[],[f3])).
% 1.99/0.63  fof(f3,axiom,(
% 1.99/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.99/0.63  fof(f125,plain,(
% 1.99/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.99/0.63    inference(superposition,[],[f62,f68])).
% 1.99/0.63  fof(f68,plain,(
% 1.99/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f41])).
% 1.99/0.63  fof(f41,plain,(
% 1.99/0.63    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.99/0.63    inference(nnf_transformation,[],[f9])).
% 1.99/0.63  fof(f9,axiom,(
% 1.99/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.99/0.63  fof(f62,plain,(
% 1.99/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.99/0.63    inference(cnf_transformation,[],[f6])).
% 1.99/0.63  fof(f6,axiom,(
% 1.99/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.99/0.63  fof(f60,plain,(
% 1.99/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.99/0.63    inference(cnf_transformation,[],[f10])).
% 1.99/0.63  fof(f10,axiom,(
% 1.99/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.99/0.63  fof(f304,plain,(
% 1.99/0.63    k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 1.99/0.63    inference(forward_demodulation,[],[f302,f54])).
% 1.99/0.63  fof(f54,plain,(
% 1.99/0.63    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f13])).
% 1.99/0.63  fof(f13,axiom,(
% 1.99/0.63    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.99/0.63  fof(f302,plain,(
% 1.99/0.63    k2_tarski(sK0,sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 1.99/0.63    inference(backward_demodulation,[],[f100,f300])).
% 1.99/0.63  fof(f300,plain,(
% 1.99/0.63    sK0 = sK1),
% 1.99/0.63    inference(subsumption_resolution,[],[f298,f89])).
% 1.99/0.63  fof(f89,plain,(
% 1.99/0.63    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.99/0.63    inference(equality_resolution,[],[f70])).
% 1.99/0.63  fof(f70,plain,(
% 1.99/0.63    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.99/0.63    inference(cnf_transformation,[],[f45])).
% 1.99/0.63  fof(f45,plain,(
% 1.99/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.99/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 1.99/0.63  fof(f44,plain,(
% 1.99/0.63    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.99/0.63    introduced(choice_axiom,[])).
% 1.99/0.63  fof(f43,plain,(
% 1.99/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.99/0.63    inference(rectify,[],[f42])).
% 1.99/0.63  fof(f42,plain,(
% 1.99/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.99/0.63    inference(nnf_transformation,[],[f12])).
% 1.99/0.63  fof(f12,axiom,(
% 1.99/0.63    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.99/0.63  fof(f298,plain,(
% 1.99/0.63    sK0 = sK1 | r2_hidden(sK1,k1_tarski(sK0))),
% 1.99/0.63    inference(resolution,[],[f290,f66])).
% 1.99/0.63  fof(f66,plain,(
% 1.99/0.63    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.99/0.63    inference(cnf_transformation,[],[f32])).
% 1.99/0.63  fof(f32,plain,(
% 1.99/0.63    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.99/0.63    inference(ennf_transformation,[],[f20])).
% 1.99/0.63  fof(f20,axiom,(
% 1.99/0.63    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.99/0.63  fof(f290,plain,(
% 1.99/0.63    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | sK0 = sK1),
% 1.99/0.63    inference(trivial_inequality_removal,[],[f289])).
% 1.99/0.63  fof(f289,plain,(
% 1.99/0.63    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | sK0 = sK1),
% 1.99/0.63    inference(superposition,[],[f251,f65])).
% 1.99/0.63  fof(f65,plain,(
% 1.99/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.99/0.63    inference(cnf_transformation,[],[f31])).
% 1.99/0.63  fof(f31,plain,(
% 1.99/0.63    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.99/0.63    inference(ennf_transformation,[],[f23])).
% 1.99/0.63  fof(f23,axiom,(
% 1.99/0.63    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 1.99/0.63  fof(f251,plain,(
% 1.99/0.63    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 1.99/0.63    inference(superposition,[],[f100,f119])).
% 1.99/0.63  fof(f119,plain,(
% 1.99/0.63    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k5_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.99/0.63    inference(superposition,[],[f60,f68])).
% 1.99/0.63  fof(f100,plain,(
% 1.99/0.63    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.99/0.63    inference(superposition,[],[f51,f58])).
% 1.99/0.63  fof(f58,plain,(
% 1.99/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.99/0.63    inference(cnf_transformation,[],[f22])).
% 1.99/0.63  fof(f22,axiom,(
% 1.99/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.99/0.63  fof(f51,plain,(
% 1.99/0.63    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.99/0.63    inference(cnf_transformation,[],[f36])).
% 1.99/0.63  fof(f36,plain,(
% 1.99/0.63    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.99/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f35])).
% 1.99/0.63  fof(f35,plain,(
% 1.99/0.63    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.99/0.63    introduced(choice_axiom,[])).
% 1.99/0.63  fof(f28,plain,(
% 1.99/0.63    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.99/0.63    inference(ennf_transformation,[],[f25])).
% 1.99/0.63  fof(f25,negated_conjecture,(
% 1.99/0.63    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.99/0.63    inference(negated_conjecture,[],[f24])).
% 1.99/0.63  fof(f24,conjecture,(
% 1.99/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.99/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 1.99/0.63  % SZS output end Proof for theBenchmark
% 1.99/0.63  % (21497)------------------------------
% 1.99/0.63  % (21497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.63  % (21497)Termination reason: Refutation
% 1.99/0.63  
% 1.99/0.63  % (21497)Memory used [KB]: 2046
% 1.99/0.63  % (21497)Time elapsed: 0.146 s
% 1.99/0.63  % (21497)------------------------------
% 1.99/0.63  % (21497)------------------------------
% 1.99/0.63  % (21487)Success in time 0.263 s
%------------------------------------------------------------------------------
