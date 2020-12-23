%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:46 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 372 expanded)
%              Number of leaves         :   12 ( 116 expanded)
%              Depth                    :   17
%              Number of atoms          :   64 ( 477 expanded)
%              Number of equality atoms :   44 ( 359 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1059,plain,(
    $false ),
    inference(resolution,[],[f886,f18])).

fof(f18,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).

% (30972)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f16,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
   => ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).

fof(f886,plain,(
    ! [X2,X1] : r1_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f882,f428])).

fof(f428,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f401,f310])).

fof(f310,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k3_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f298,f70])).

fof(f70,plain,(
    ! [X0] : k2_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[],[f42,f62])).

fof(f62,plain,(
    ! [X1] : o_0_0_xboole_0 = k3_xboole_0(X1,o_0_0_xboole_0) ),
    inference(superposition,[],[f59,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f59,plain,(
    ! [X2] : o_0_0_xboole_0 = k3_xboole_0(o_0_0_xboole_0,X2) ),
    inference(superposition,[],[f42,f43])).

fof(f43,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f38,f34])).

fof(f34,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f24,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f19,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f21,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f26,f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[],[f25,f26])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f298,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(o_0_0_xboole_0,X6)) = k3_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f28,f276])).

fof(f276,plain,(
    ! [X1] : k4_xboole_0(X1,o_0_0_xboole_0) = X1 ),
    inference(superposition,[],[f71,f70])).

fof(f71,plain,(
    ! [X1] : k2_xboole_0(o_0_0_xboole_0,k4_xboole_0(X1,o_0_0_xboole_0)) = X1 ),
    inference(superposition,[],[f26,f62])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f401,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f186,f186])).

fof(f186,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f172,f70])).

fof(f172,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(o_0_0_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f29,f34])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f882,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(backward_demodulation,[],[f558,f880])).

fof(f880,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(backward_demodulation,[],[f177,f845])).

fof(f845,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(superposition,[],[f25,f444])).

fof(f444,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = X4 ),
    inference(forward_demodulation,[],[f414,f310])).

fof(f414,plain,(
    ! [X4,X5] : k2_xboole_0(k3_xboole_0(X4,k4_xboole_0(X4,X5)),k3_xboole_0(X4,X5)) = X4 ),
    inference(superposition,[],[f26,f186])).

fof(f177,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f29,f22])).

fof(f558,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f49,f54])).

fof(f54,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f25,f43])).

fof(f49,plain,(
    ! [X4,X5,X3] : r1_xboole_0(k4_xboole_0(X5,k4_xboole_0(X3,X4)),k4_xboole_0(X3,k2_xboole_0(X4,X5))) ),
    inference(superposition,[],[f24,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:49:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (30970)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (30963)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (30974)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (30963)Refutation not found, incomplete strategy% (30963)------------------------------
% 0.21/0.50  % (30963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30965)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (30978)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (30978)Refutation not found, incomplete strategy% (30978)------------------------------
% 0.21/0.51  % (30978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30978)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30978)Memory used [KB]: 6140
% 0.21/0.51  % (30978)Time elapsed: 0.002 s
% 0.21/0.51  % (30978)------------------------------
% 0.21/0.51  % (30978)------------------------------
% 0.21/0.51  % (30968)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (30985)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (30965)Refutation not found, incomplete strategy% (30965)------------------------------
% 0.21/0.52  % (30965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30965)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30965)Memory used [KB]: 10618
% 0.21/0.52  % (30965)Time elapsed: 0.107 s
% 0.21/0.52  % (30965)------------------------------
% 0.21/0.52  % (30965)------------------------------
% 0.21/0.52  % (30985)Refutation not found, incomplete strategy% (30985)------------------------------
% 0.21/0.52  % (30985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30985)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30985)Memory used [KB]: 10618
% 0.21/0.52  % (30985)Time elapsed: 0.076 s
% 0.21/0.52  % (30985)------------------------------
% 0.21/0.52  % (30985)------------------------------
% 0.21/0.52  % (30974)Refutation not found, incomplete strategy% (30974)------------------------------
% 0.21/0.52  % (30974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30974)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30974)Memory used [KB]: 10618
% 0.21/0.52  % (30974)Time elapsed: 0.103 s
% 0.21/0.52  % (30974)------------------------------
% 0.21/0.52  % (30974)------------------------------
% 0.21/0.52  % (30979)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (30967)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (30967)Refutation not found, incomplete strategy% (30967)------------------------------
% 0.21/0.52  % (30967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30967)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30967)Memory used [KB]: 6140
% 0.21/0.52  % (30967)Time elapsed: 0.110 s
% 0.21/0.52  % (30967)------------------------------
% 0.21/0.52  % (30967)------------------------------
% 1.27/0.52  % (30963)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (30963)Memory used [KB]: 1663
% 1.27/0.52  % (30963)Time elapsed: 0.087 s
% 1.27/0.52  % (30963)------------------------------
% 1.27/0.52  % (30963)------------------------------
% 1.27/0.52  % (30983)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.27/0.52  % (30983)Refutation not found, incomplete strategy% (30983)------------------------------
% 1.27/0.52  % (30983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (30983)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (30983)Memory used [KB]: 10618
% 1.27/0.52  % (30983)Time elapsed: 0.107 s
% 1.27/0.52  % (30983)------------------------------
% 1.27/0.52  % (30983)------------------------------
% 1.27/0.52  % (30986)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.52  % (30986)Refutation not found, incomplete strategy% (30986)------------------------------
% 1.27/0.52  % (30986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (30986)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (30986)Memory used [KB]: 1663
% 1.27/0.52  % (30986)Time elapsed: 0.101 s
% 1.27/0.52  % (30986)------------------------------
% 1.27/0.52  % (30986)------------------------------
% 1.27/0.52  % (30969)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.52  % (30975)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.53  % (30966)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.53  % (30977)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.53  % (30964)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.54  % (30992)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.27/0.54  % (30982)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.27/0.54  % (30971)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.54  % (30971)Refutation not found, incomplete strategy% (30971)------------------------------
% 1.27/0.54  % (30971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (30971)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (30971)Memory used [KB]: 10618
% 1.27/0.54  % (30971)Time elapsed: 0.126 s
% 1.27/0.54  % (30971)------------------------------
% 1.27/0.54  % (30971)------------------------------
% 1.42/0.54  % (30984)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.54  % (30984)Refutation not found, incomplete strategy% (30984)------------------------------
% 1.42/0.54  % (30984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (30984)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (30984)Memory used [KB]: 1663
% 1.42/0.54  % (30984)Time elapsed: 0.129 s
% 1.42/0.54  % (30984)------------------------------
% 1.42/0.54  % (30984)------------------------------
% 1.42/0.54  % (30989)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.54  % (30989)Refutation not found, incomplete strategy% (30989)------------------------------
% 1.42/0.54  % (30989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (30989)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (30989)Memory used [KB]: 10618
% 1.42/0.54  % (30989)Time elapsed: 0.131 s
% 1.42/0.54  % (30989)------------------------------
% 1.42/0.54  % (30989)------------------------------
% 1.42/0.54  % (30976)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.54  % (30976)Refutation not found, incomplete strategy% (30976)------------------------------
% 1.42/0.54  % (30976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (30976)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (30976)Memory used [KB]: 6140
% 1.42/0.54  % (30976)Time elapsed: 0.130 s
% 1.42/0.54  % (30976)------------------------------
% 1.42/0.54  % (30976)------------------------------
% 1.42/0.55  % (30990)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.55  % (30981)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.55  % (30987)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.42/0.55  % (30973)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.42/0.55  % (30973)Refutation not found, incomplete strategy% (30973)------------------------------
% 1.42/0.55  % (30973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (30973)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (30973)Memory used [KB]: 10618
% 1.42/0.55  % (30973)Time elapsed: 0.141 s
% 1.42/0.55  % (30973)------------------------------
% 1.42/0.55  % (30973)------------------------------
% 1.42/0.55  % (30975)Refutation found. Thanks to Tanya!
% 1.42/0.55  % SZS status Theorem for theBenchmark
% 1.42/0.55  % SZS output start Proof for theBenchmark
% 1.42/0.55  fof(f1059,plain,(
% 1.42/0.55    $false),
% 1.42/0.55    inference(resolution,[],[f886,f18])).
% 1.42/0.55  fof(f18,plain,(
% 1.42/0.55    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 1.42/0.55    inference(cnf_transformation,[],[f17])).
% 1.42/0.55  fof(f17,plain,(
% 1.42/0.55    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).
% 1.42/0.55  % (30972)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.55  fof(f16,plain,(
% 1.42/0.55    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) => ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f14,plain,(
% 1.42/0.55    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 1.42/0.55    inference(ennf_transformation,[],[f12])).
% 1.42/0.55  fof(f12,negated_conjecture,(
% 1.42/0.55    ~! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 1.42/0.55    inference(negated_conjecture,[],[f11])).
% 1.42/0.55  fof(f11,conjecture,(
% 1.42/0.55    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).
% 1.42/0.55  fof(f886,plain,(
% 1.42/0.55    ( ! [X2,X1] : (r1_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))) )),
% 1.42/0.55    inference(superposition,[],[f882,f428])).
% 1.42/0.55  fof(f428,plain,(
% 1.42/0.55    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 1.42/0.55    inference(forward_demodulation,[],[f401,f310])).
% 1.42/0.55  fof(f310,plain,(
% 1.42/0.55    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k3_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 1.42/0.55    inference(forward_demodulation,[],[f298,f70])).
% 1.42/0.55  fof(f70,plain,(
% 1.42/0.55    ( ! [X0] : (k2_xboole_0(o_0_0_xboole_0,X0) = X0) )),
% 1.42/0.55    inference(superposition,[],[f42,f62])).
% 1.42/0.55  fof(f62,plain,(
% 1.42/0.55    ( ! [X1] : (o_0_0_xboole_0 = k3_xboole_0(X1,o_0_0_xboole_0)) )),
% 1.42/0.55    inference(superposition,[],[f59,f23])).
% 1.42/0.55  fof(f23,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f1])).
% 1.42/0.55  fof(f1,axiom,(
% 1.42/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.42/0.55  fof(f59,plain,(
% 1.42/0.55    ( ! [X2] : (o_0_0_xboole_0 = k3_xboole_0(o_0_0_xboole_0,X2)) )),
% 1.42/0.55    inference(superposition,[],[f42,f43])).
% 1.42/0.55  fof(f43,plain,(
% 1.42/0.55    ( ! [X0] : (k2_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 1.42/0.55    inference(forward_demodulation,[],[f38,f34])).
% 1.42/0.55  fof(f34,plain,(
% 1.42/0.55    ( ! [X0] : (o_0_0_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.42/0.55    inference(resolution,[],[f24,f30])).
% 1.42/0.55  fof(f30,plain,(
% 1.42/0.55    ( ! [X0] : (~r1_xboole_0(X0,X0) | o_0_0_xboole_0 = X0) )),
% 1.42/0.55    inference(definition_unfolding,[],[f21,f19])).
% 1.42/0.55  fof(f19,plain,(
% 1.42/0.55    k1_xboole_0 = o_0_0_xboole_0),
% 1.42/0.55    inference(cnf_transformation,[],[f2])).
% 1.42/0.55  fof(f2,axiom,(
% 1.42/0.55    k1_xboole_0 = o_0_0_xboole_0),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 1.42/0.55  fof(f21,plain,(
% 1.42/0.55    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.42/0.55    inference(cnf_transformation,[],[f15])).
% 1.42/0.55  fof(f15,plain,(
% 1.42/0.55    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f8])).
% 1.42/0.55  fof(f8,axiom,(
% 1.42/0.55    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.42/0.55  fof(f24,plain,(
% 1.42/0.55    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f10])).
% 1.42/0.55  fof(f10,axiom,(
% 1.42/0.55    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).
% 1.42/0.55  fof(f38,plain,(
% 1.42/0.55    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.42/0.55    inference(superposition,[],[f26,f22])).
% 1.42/0.55  fof(f22,plain,(
% 1.42/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.42/0.55    inference(cnf_transformation,[],[f13])).
% 1.42/0.55  fof(f13,plain,(
% 1.42/0.55    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.42/0.55    inference(rectify,[],[f3])).
% 1.42/0.55  fof(f3,axiom,(
% 1.42/0.55    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.42/0.55  fof(f26,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.42/0.55    inference(cnf_transformation,[],[f5])).
% 1.42/0.55  fof(f5,axiom,(
% 1.42/0.55    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.42/0.55  fof(f42,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) )),
% 1.42/0.55    inference(superposition,[],[f25,f26])).
% 1.42/0.55  fof(f25,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f9])).
% 1.42/0.55  fof(f9,axiom,(
% 1.42/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
% 1.42/0.55  fof(f298,plain,(
% 1.42/0.55    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(o_0_0_xboole_0,X6)) = k3_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 1.42/0.55    inference(superposition,[],[f28,f276])).
% 1.42/0.55  fof(f276,plain,(
% 1.42/0.55    ( ! [X1] : (k4_xboole_0(X1,o_0_0_xboole_0) = X1) )),
% 1.42/0.55    inference(superposition,[],[f71,f70])).
% 1.42/0.55  fof(f71,plain,(
% 1.42/0.55    ( ! [X1] : (k2_xboole_0(o_0_0_xboole_0,k4_xboole_0(X1,o_0_0_xboole_0)) = X1) )),
% 1.42/0.55    inference(superposition,[],[f26,f62])).
% 1.42/0.55  fof(f28,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f7])).
% 1.42/0.55  fof(f7,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
% 1.42/0.55  fof(f401,plain,(
% 1.42/0.55    ( ! [X2,X3] : (k4_xboole_0(X2,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 1.42/0.55    inference(superposition,[],[f186,f186])).
% 1.42/0.55  fof(f186,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.42/0.55    inference(forward_demodulation,[],[f172,f70])).
% 1.42/0.55  fof(f172,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(o_0_0_xboole_0,k3_xboole_0(X0,X1))) )),
% 1.42/0.55    inference(superposition,[],[f29,f34])).
% 1.42/0.55  fof(f29,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f6])).
% 1.42/0.55  fof(f6,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.42/0.55  fof(f882,plain,(
% 1.42/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.42/0.55    inference(backward_demodulation,[],[f558,f880])).
% 1.42/0.55  fof(f880,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 1.42/0.55    inference(backward_demodulation,[],[f177,f845])).
% 1.42/0.55  fof(f845,plain,(
% 1.42/0.55    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 1.42/0.55    inference(superposition,[],[f25,f444])).
% 1.42/0.55  fof(f444,plain,(
% 1.42/0.55    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = X4) )),
% 1.42/0.55    inference(forward_demodulation,[],[f414,f310])).
% 1.42/0.55  fof(f414,plain,(
% 1.42/0.55    ( ! [X4,X5] : (k2_xboole_0(k3_xboole_0(X4,k4_xboole_0(X4,X5)),k3_xboole_0(X4,X5)) = X4) )),
% 1.42/0.55    inference(superposition,[],[f26,f186])).
% 1.42/0.55  fof(f177,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.42/0.55    inference(superposition,[],[f29,f22])).
% 1.42/0.55  fof(f558,plain,(
% 1.42/0.55    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) )),
% 1.42/0.55    inference(superposition,[],[f49,f54])).
% 1.42/0.55  fof(f54,plain,(
% 1.42/0.55    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.42/0.55    inference(superposition,[],[f25,f43])).
% 1.42/0.55  fof(f49,plain,(
% 1.42/0.55    ( ! [X4,X5,X3] : (r1_xboole_0(k4_xboole_0(X5,k4_xboole_0(X3,X4)),k4_xboole_0(X3,k2_xboole_0(X4,X5)))) )),
% 1.42/0.55    inference(superposition,[],[f24,f27])).
% 1.42/0.55  fof(f27,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f4])).
% 1.42/0.55  fof(f4,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.42/0.55  % SZS output end Proof for theBenchmark
% 1.42/0.55  % (30975)------------------------------
% 1.42/0.55  % (30975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (30975)Termination reason: Refutation
% 1.42/0.55  
% 1.42/0.55  % (30975)Memory used [KB]: 6908
% 1.42/0.55  % (30975)Time elapsed: 0.125 s
% 1.42/0.55  % (30975)------------------------------
% 1.42/0.55  % (30975)------------------------------
% 1.42/0.55  % (30972)Refutation not found, incomplete strategy% (30972)------------------------------
% 1.42/0.55  % (30972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (30972)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (30972)Memory used [KB]: 10618
% 1.42/0.55  % (30972)Time elapsed: 0.143 s
% 1.42/0.55  % (30972)------------------------------
% 1.42/0.55  % (30972)------------------------------
% 1.42/0.56  % (30991)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.56  % (30988)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.42/0.56  % (30988)Refutation not found, incomplete strategy% (30988)------------------------------
% 1.42/0.56  % (30988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (30988)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (30988)Memory used [KB]: 6140
% 1.42/0.56  % (30988)Time elapsed: 0.150 s
% 1.42/0.56  % (30988)------------------------------
% 1.42/0.56  % (30988)------------------------------
% 1.42/0.56  % (30980)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.56  % (30980)Refutation not found, incomplete strategy% (30980)------------------------------
% 1.42/0.56  % (30980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (30980)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (30980)Memory used [KB]: 10618
% 1.42/0.56  % (30980)Time elapsed: 0.151 s
% 1.42/0.56  % (30980)------------------------------
% 1.42/0.56  % (30980)------------------------------
% 1.42/0.58  % (30962)Success in time 0.202 s
%------------------------------------------------------------------------------
