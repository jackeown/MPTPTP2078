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
% DateTime   : Thu Dec  3 12:43:32 EST 2020

% Result     : Theorem 2.36s
% Output     : Refutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   56 (  99 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :   15
%              Number of atoms          :  113 ( 258 expanded)
%              Number of equality atoms :   41 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1158,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1157,f272])).

fof(f272,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f267,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f267,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f265,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f265,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f262,f70])).

fof(f70,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f61,f38])).

fof(f61,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f33,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f262,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f242,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f242,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f63,f38])).

fof(f63,plain,(
    k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f34,f43])).

fof(f34,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f1157,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1141,f66])).

fof(f66,plain,(
    ~ r1_xboole_0(k1_tarski(sK3),sK2) ),
    inference(superposition,[],[f59,f36])).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f59,plain,(
    ! [X0] : ~ r1_xboole_0(k2_tarski(sK3,X0),sK2) ),
    inference(resolution,[],[f32,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f32,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f1141,plain,
    ( r1_xboole_0(k1_tarski(sK3),sK2)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f150,f94])).

fof(f94,plain,
    ( k3_xboole_0(sK0,sK1) = k1_tarski(sK3)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f31,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f31,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f150,plain,(
    ! [X1] : r1_xboole_0(k3_xboole_0(X1,sK1),sK2) ),
    inference(superposition,[],[f141,f38])).

fof(f141,plain,(
    ! [X2] : r1_xboole_0(k3_xboole_0(sK1,X2),sK2) ),
    inference(resolution,[],[f93,f37])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f93,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | r1_xboole_0(X1,sK2) ) ),
    inference(superposition,[],[f51,f86])).

fof(f86,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f82,f35])).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f82,plain,(
    k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f41,f70])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (24125)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (24118)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (24121)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.56  % (24138)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.58  % (24120)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.58  % (24130)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.59  % (24116)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.60  % (24145)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.60  % (24119)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.60  % (24128)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.60  % (24126)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.60  % (24134)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.61  % (24134)Refutation not found, incomplete strategy% (24134)------------------------------
% 0.20/0.61  % (24134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.61  % (24134)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.61  
% 0.20/0.61  % (24134)Memory used [KB]: 10618
% 0.20/0.61  % (24134)Time elapsed: 0.177 s
% 0.20/0.61  % (24134)------------------------------
% 0.20/0.61  % (24134)------------------------------
% 0.20/0.61  % (24147)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.61  % (24139)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.62  % (24141)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.87/0.62  % (24131)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.87/0.63  % (24143)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.87/0.63  % (24136)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.87/0.63  % (24146)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.87/0.63  % (24140)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.87/0.64  % (24133)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.13/0.64  % (24124)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.13/0.64  % (24132)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 2.13/0.64  % (24122)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 2.13/0.64  % (24127)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.13/0.64  % (24115)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 2.13/0.66  % (24135)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.13/0.66  % (24123)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 2.36/0.66  % (24144)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.36/0.67  % (24137)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.36/0.69  % (24140)Refutation found. Thanks to Tanya!
% 2.36/0.69  % SZS status Theorem for theBenchmark
% 2.36/0.69  % SZS output start Proof for theBenchmark
% 2.36/0.69  fof(f1158,plain,(
% 2.36/0.69    $false),
% 2.36/0.69    inference(subsumption_resolution,[],[f1157,f272])).
% 2.36/0.69  fof(f272,plain,(
% 2.36/0.69    k1_xboole_0 != k3_xboole_0(sK0,sK1)),
% 2.36/0.69    inference(superposition,[],[f267,f38])).
% 2.36/0.69  fof(f38,plain,(
% 2.36/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.36/0.69    inference(cnf_transformation,[],[f1])).
% 2.36/0.69  fof(f1,axiom,(
% 2.36/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.36/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.36/0.69  fof(f267,plain,(
% 2.36/0.69    k1_xboole_0 != k3_xboole_0(sK1,sK0)),
% 2.36/0.69    inference(resolution,[],[f265,f43])).
% 2.36/0.69  fof(f43,plain,(
% 2.36/0.69    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.36/0.69    inference(cnf_transformation,[],[f28])).
% 2.36/0.69  fof(f28,plain,(
% 2.36/0.69    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.36/0.69    inference(nnf_transformation,[],[f2])).
% 2.36/0.69  fof(f2,axiom,(
% 2.36/0.69    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.36/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.36/0.69  fof(f265,plain,(
% 2.36/0.69    ~r1_xboole_0(sK1,sK0)),
% 2.36/0.69    inference(subsumption_resolution,[],[f262,f70])).
% 2.36/0.69  fof(f70,plain,(
% 2.36/0.69    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 2.36/0.69    inference(superposition,[],[f61,f38])).
% 2.36/0.69  fof(f61,plain,(
% 2.36/0.69    k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 2.36/0.69    inference(resolution,[],[f33,f42])).
% 2.36/0.69  fof(f42,plain,(
% 2.36/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.36/0.69    inference(cnf_transformation,[],[f28])).
% 2.36/0.69  fof(f33,plain,(
% 2.36/0.69    r1_xboole_0(sK2,sK1)),
% 2.36/0.69    inference(cnf_transformation,[],[f27])).
% 2.36/0.69  fof(f27,plain,(
% 2.36/0.69    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 2.36/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f26])).
% 2.36/0.69  fof(f26,plain,(
% 2.36/0.69    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 2.36/0.69    introduced(choice_axiom,[])).
% 2.36/0.69  fof(f22,plain,(
% 2.36/0.69    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 2.36/0.69    inference(flattening,[],[f21])).
% 2.36/0.69  fof(f21,plain,(
% 2.36/0.69    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 2.36/0.69    inference(ennf_transformation,[],[f20])).
% 2.36/0.69  fof(f20,negated_conjecture,(
% 2.36/0.69    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.36/0.69    inference(negated_conjecture,[],[f19])).
% 2.36/0.69  fof(f19,conjecture,(
% 2.36/0.69    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.36/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 2.36/0.69  fof(f262,plain,(
% 2.36/0.69    k1_xboole_0 != k3_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0)),
% 2.36/0.69    inference(superposition,[],[f242,f49])).
% 2.36/0.69  fof(f49,plain,(
% 2.36/0.69    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 2.36/0.69    inference(cnf_transformation,[],[f23])).
% 2.36/0.69  fof(f23,plain,(
% 2.36/0.69    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 2.36/0.69    inference(ennf_transformation,[],[f8])).
% 2.36/0.69  fof(f8,axiom,(
% 2.36/0.69    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 2.36/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 2.36/0.69  fof(f242,plain,(
% 2.36/0.69    k1_xboole_0 != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 2.36/0.69    inference(superposition,[],[f63,f38])).
% 2.36/0.69  fof(f63,plain,(
% 2.36/0.69    k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 2.36/0.69    inference(resolution,[],[f34,f43])).
% 2.36/0.69  fof(f34,plain,(
% 2.36/0.69    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 2.36/0.69    inference(cnf_transformation,[],[f27])).
% 2.36/0.69  fof(f1157,plain,(
% 2.36/0.69    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 2.36/0.69    inference(subsumption_resolution,[],[f1141,f66])).
% 2.36/0.69  fof(f66,plain,(
% 2.36/0.69    ~r1_xboole_0(k1_tarski(sK3),sK2)),
% 2.36/0.69    inference(superposition,[],[f59,f36])).
% 2.36/0.69  fof(f36,plain,(
% 2.36/0.69    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.36/0.69    inference(cnf_transformation,[],[f9])).
% 2.36/0.69  fof(f9,axiom,(
% 2.36/0.69    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.36/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.36/0.69  fof(f59,plain,(
% 2.36/0.69    ( ! [X0] : (~r1_xboole_0(k2_tarski(sK3,X0),sK2)) )),
% 2.36/0.69    inference(resolution,[],[f32,f52])).
% 2.36/0.69  fof(f52,plain,(
% 2.36/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 2.36/0.69    inference(cnf_transformation,[],[f25])).
% 2.36/0.69  fof(f25,plain,(
% 2.36/0.69    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.36/0.69    inference(ennf_transformation,[],[f18])).
% 2.36/0.69  fof(f18,axiom,(
% 2.36/0.69    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.36/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 2.36/0.69  fof(f32,plain,(
% 2.36/0.69    r2_hidden(sK3,sK2)),
% 2.36/0.69    inference(cnf_transformation,[],[f27])).
% 2.36/0.69  fof(f1141,plain,(
% 2.36/0.69    r1_xboole_0(k1_tarski(sK3),sK2) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 2.36/0.69    inference(superposition,[],[f150,f94])).
% 2.36/0.69  fof(f94,plain,(
% 2.36/0.69    k3_xboole_0(sK0,sK1) = k1_tarski(sK3) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 2.36/0.69    inference(resolution,[],[f31,f44])).
% 2.36/0.69  fof(f44,plain,(
% 2.36/0.69    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.36/0.69    inference(cnf_transformation,[],[f30])).
% 2.36/0.69  fof(f30,plain,(
% 2.36/0.69    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.36/0.69    inference(flattening,[],[f29])).
% 2.36/0.69  fof(f29,plain,(
% 2.36/0.69    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.36/0.69    inference(nnf_transformation,[],[f16])).
% 2.36/0.69  fof(f16,axiom,(
% 2.36/0.69    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.36/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.36/0.69  fof(f31,plain,(
% 2.36/0.69    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 2.36/0.69    inference(cnf_transformation,[],[f27])).
% 2.36/0.69  fof(f150,plain,(
% 2.36/0.69    ( ! [X1] : (r1_xboole_0(k3_xboole_0(X1,sK1),sK2)) )),
% 2.36/0.69    inference(superposition,[],[f141,f38])).
% 2.36/0.69  fof(f141,plain,(
% 2.36/0.69    ( ! [X2] : (r1_xboole_0(k3_xboole_0(sK1,X2),sK2)) )),
% 2.36/0.69    inference(resolution,[],[f93,f37])).
% 2.36/0.69  fof(f37,plain,(
% 2.36/0.69    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.36/0.69    inference(cnf_transformation,[],[f6])).
% 2.36/0.69  fof(f6,axiom,(
% 2.36/0.69    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.36/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.36/0.69  fof(f93,plain,(
% 2.36/0.69    ( ! [X1] : (~r1_tarski(X1,sK1) | r1_xboole_0(X1,sK2)) )),
% 2.36/0.69    inference(superposition,[],[f51,f86])).
% 2.36/0.69  fof(f86,plain,(
% 2.36/0.69    sK1 = k4_xboole_0(sK1,sK2)),
% 2.36/0.69    inference(forward_demodulation,[],[f82,f35])).
% 2.36/0.69  fof(f35,plain,(
% 2.36/0.69    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.36/0.69    inference(cnf_transformation,[],[f7])).
% 2.36/0.69  fof(f7,axiom,(
% 2.36/0.69    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.36/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.36/0.69  fof(f82,plain,(
% 2.36/0.69    k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0)),
% 2.36/0.69    inference(superposition,[],[f41,f70])).
% 2.36/0.69  fof(f41,plain,(
% 2.36/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.36/0.69    inference(cnf_transformation,[],[f3])).
% 2.36/0.69  fof(f3,axiom,(
% 2.36/0.69    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.36/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.36/0.69  fof(f51,plain,(
% 2.36/0.69    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 2.36/0.69    inference(cnf_transformation,[],[f24])).
% 2.36/0.69  fof(f24,plain,(
% 2.36/0.69    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.36/0.69    inference(ennf_transformation,[],[f4])).
% 2.36/0.69  fof(f4,axiom,(
% 2.36/0.69    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.36/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.36/0.69  % SZS output end Proof for theBenchmark
% 2.36/0.69  % (24140)------------------------------
% 2.36/0.69  % (24140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.69  % (24140)Termination reason: Refutation
% 2.36/0.69  
% 2.36/0.69  % (24140)Memory used [KB]: 2174
% 2.36/0.69  % (24140)Time elapsed: 0.244 s
% 2.36/0.69  % (24140)------------------------------
% 2.36/0.69  % (24140)------------------------------
% 2.36/0.69  % (24110)Success in time 0.331 s
%------------------------------------------------------------------------------
