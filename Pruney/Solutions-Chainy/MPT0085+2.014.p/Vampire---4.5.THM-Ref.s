%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:23 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 107 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  106 ( 268 expanded)
%              Number of equality atoms :   29 (  52 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1489,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1488])).

fof(f1488,plain,(
    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f354,f1356])).

fof(f1356,plain,(
    ! [X15] : k2_xboole_0(k1_xboole_0,X15) = X15 ),
    inference(superposition,[],[f96,f182])).

fof(f182,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k2_xboole_0(k1_xboole_0,k2_xboole_0(X4,X5))) = k2_xboole_0(k1_xboole_0,X4) ),
    inference(superposition,[],[f112,f124])).

fof(f124,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f113,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f113,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f34,f41])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f40,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f40,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f112,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f34,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f96,plain,(
    ! [X6,X4,X5] : k3_xboole_0(X4,k2_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(k4_xboole_0(X4,X5),X6)))) = X4 ),
    inference(resolution,[],[f81,f30])).

fof(f81,plain,(
    ! [X4,X2,X3] : r1_tarski(X2,k2_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(k4_xboole_0(X2,X3),X4)))) ),
    inference(resolution,[],[f79,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(resolution,[],[f35,f40])).

fof(f354,plain,(
    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2)) ),
    inference(superposition,[],[f25,f127])).

fof(f127,plain,(
    ! [X9] : k3_xboole_0(sK0,k2_xboole_0(sK1,X9)) = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X9)) ),
    inference(forward_demodulation,[],[f116,f112])).

fof(f116,plain,(
    ! [X9] : k3_xboole_0(sK0,k2_xboole_0(sK1,X9)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X9)) ),
    inference(superposition,[],[f34,f47])).

fof(f47,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f45,f26])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),X0) ),
    inference(resolution,[],[f44,f30])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,sK1),X0) ),
    inference(resolution,[],[f38,f24])).

fof(f24,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1) )
   => ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f32,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f25,plain,(
    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:05:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (11336)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (11329)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (11332)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (11326)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (11326)Refutation not found, incomplete strategy% (11326)------------------------------
% 0.21/0.53  % (11326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11326)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11326)Memory used [KB]: 10618
% 0.21/0.53  % (11326)Time elapsed: 0.115 s
% 0.21/0.53  % (11326)------------------------------
% 0.21/0.53  % (11326)------------------------------
% 0.21/0.53  % (11346)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (11338)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (11324)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (11342)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (11351)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (11346)Refutation not found, incomplete strategy% (11346)------------------------------
% 0.21/0.54  % (11346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11346)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11346)Memory used [KB]: 10618
% 0.21/0.54  % (11346)Time elapsed: 0.088 s
% 0.21/0.54  % (11346)------------------------------
% 0.21/0.54  % (11346)------------------------------
% 0.21/0.54  % (11325)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (11332)Refutation not found, incomplete strategy% (11332)------------------------------
% 0.21/0.54  % (11332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11332)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11332)Memory used [KB]: 10618
% 0.21/0.54  % (11332)Time elapsed: 0.093 s
% 0.21/0.54  % (11332)------------------------------
% 0.21/0.54  % (11332)------------------------------
% 0.21/0.54  % (11330)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (11327)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (11339)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (11340)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (11328)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (11345)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (11345)Refutation not found, incomplete strategy% (11345)------------------------------
% 0.21/0.55  % (11345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11345)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (11345)Memory used [KB]: 1663
% 0.21/0.55  % (11345)Time elapsed: 0.140 s
% 0.21/0.55  % (11345)------------------------------
% 0.21/0.55  % (11345)------------------------------
% 0.21/0.55  % (11334)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (11341)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (11334)Refutation not found, incomplete strategy% (11334)------------------------------
% 0.21/0.55  % (11334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11334)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (11334)Memory used [KB]: 10618
% 0.21/0.55  % (11334)Time elapsed: 0.139 s
% 0.21/0.55  % (11334)------------------------------
% 0.21/0.55  % (11334)------------------------------
% 0.21/0.55  % (11331)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (11341)Refutation not found, incomplete strategy% (11341)------------------------------
% 0.21/0.55  % (11341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11341)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (11341)Memory used [KB]: 10618
% 0.21/0.55  % (11341)Time elapsed: 0.137 s
% 0.21/0.55  % (11341)------------------------------
% 0.21/0.55  % (11341)------------------------------
% 0.21/0.55  % (11343)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (11353)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (11352)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (11333)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (11347)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (11337)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (11335)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (11349)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (11335)Refutation not found, incomplete strategy% (11335)------------------------------
% 0.21/0.56  % (11335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (11335)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (11335)Memory used [KB]: 10618
% 0.21/0.56  % (11335)Time elapsed: 0.151 s
% 0.21/0.56  % (11335)------------------------------
% 0.21/0.56  % (11335)------------------------------
% 0.21/0.56  % (11344)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (11350)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (11344)Refutation not found, incomplete strategy% (11344)------------------------------
% 0.21/0.56  % (11344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (11344)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (11344)Memory used [KB]: 10618
% 0.21/0.56  % (11344)Time elapsed: 0.150 s
% 0.21/0.56  % (11344)------------------------------
% 0.21/0.56  % (11344)------------------------------
% 0.21/0.57  % (11348)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.63/0.60  % (11331)Refutation found. Thanks to Tanya!
% 1.63/0.60  % SZS status Theorem for theBenchmark
% 1.63/0.60  % SZS output start Proof for theBenchmark
% 1.63/0.60  fof(f1489,plain,(
% 1.63/0.60    $false),
% 1.63/0.60    inference(trivial_inequality_removal,[],[f1488])).
% 1.63/0.60  fof(f1488,plain,(
% 1.63/0.60    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,sK2)),
% 1.63/0.60    inference(backward_demodulation,[],[f354,f1356])).
% 1.63/0.60  fof(f1356,plain,(
% 1.63/0.60    ( ! [X15] : (k2_xboole_0(k1_xboole_0,X15) = X15) )),
% 1.63/0.60    inference(superposition,[],[f96,f182])).
% 1.63/0.60  fof(f182,plain,(
% 1.63/0.60    ( ! [X4,X5] : (k3_xboole_0(X4,k2_xboole_0(k1_xboole_0,k2_xboole_0(X4,X5))) = k2_xboole_0(k1_xboole_0,X4)) )),
% 1.63/0.60    inference(superposition,[],[f112,f124])).
% 1.63/0.60  fof(f124,plain,(
% 1.63/0.60    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2) )),
% 1.63/0.60    inference(forward_demodulation,[],[f113,f27])).
% 1.63/0.60  fof(f27,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.63/0.60    inference(cnf_transformation,[],[f3])).
% 1.63/0.60  fof(f3,axiom,(
% 1.63/0.60    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.63/0.60  fof(f113,plain,(
% 1.63/0.60    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 1.63/0.60    inference(superposition,[],[f34,f41])).
% 1.63/0.60  fof(f41,plain,(
% 1.63/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.63/0.60    inference(resolution,[],[f40,f30])).
% 1.63/0.60  fof(f30,plain,(
% 1.63/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.63/0.60    inference(cnf_transformation,[],[f13])).
% 1.63/0.60  fof(f13,plain,(
% 1.63/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.63/0.60    inference(ennf_transformation,[],[f5])).
% 1.63/0.60  fof(f5,axiom,(
% 1.63/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.63/0.60  fof(f40,plain,(
% 1.63/0.60    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.63/0.60    inference(duplicate_literal_removal,[],[f39])).
% 1.63/0.60  fof(f39,plain,(
% 1.63/0.60    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.63/0.60    inference(resolution,[],[f33,f32])).
% 1.63/0.60  fof(f32,plain,(
% 1.63/0.60    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f23])).
% 1.63/0.60  fof(f23,plain,(
% 1.63/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.63/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 1.63/0.60  fof(f22,plain,(
% 1.63/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.63/0.60    introduced(choice_axiom,[])).
% 1.63/0.60  fof(f21,plain,(
% 1.63/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.63/0.60    inference(rectify,[],[f20])).
% 1.63/0.60  fof(f20,plain,(
% 1.63/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.63/0.60    inference(nnf_transformation,[],[f14])).
% 1.63/0.60  fof(f14,plain,(
% 1.63/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.63/0.60    inference(ennf_transformation,[],[f1])).
% 1.63/0.60  fof(f1,axiom,(
% 1.63/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.63/0.60  fof(f33,plain,(
% 1.63/0.60    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f23])).
% 1.63/0.60  fof(f34,plain,(
% 1.63/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f4])).
% 1.63/0.60  fof(f4,axiom,(
% 1.63/0.60    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 1.63/0.60  fof(f112,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))) )),
% 1.63/0.60    inference(superposition,[],[f34,f26])).
% 1.63/0.60  fof(f26,plain,(
% 1.63/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f6])).
% 1.63/0.60  fof(f6,axiom,(
% 1.63/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.63/0.60  fof(f96,plain,(
% 1.63/0.60    ( ! [X6,X4,X5] : (k3_xboole_0(X4,k2_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(k4_xboole_0(X4,X5),X6)))) = X4) )),
% 1.63/0.60    inference(resolution,[],[f81,f30])).
% 1.63/0.60  fof(f81,plain,(
% 1.63/0.60    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(k4_xboole_0(X2,X3),X4))))) )),
% 1.63/0.60    inference(resolution,[],[f79,f35])).
% 1.63/0.60  fof(f35,plain,(
% 1.63/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f15])).
% 1.63/0.60  fof(f15,plain,(
% 1.63/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.63/0.60    inference(ennf_transformation,[],[f7])).
% 1.63/0.60  fof(f7,axiom,(
% 1.63/0.60    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.63/0.60  fof(f79,plain,(
% 1.63/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 1.63/0.60    inference(resolution,[],[f35,f40])).
% 1.63/0.60  fof(f354,plain,(
% 1.63/0.60    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2))),
% 1.63/0.60    inference(superposition,[],[f25,f127])).
% 1.63/0.60  fof(f127,plain,(
% 1.63/0.60    ( ! [X9] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X9)) = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X9))) )),
% 1.63/0.60    inference(forward_demodulation,[],[f116,f112])).
% 1.63/0.60  fof(f116,plain,(
% 1.63/0.60    ( ! [X9] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X9)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X9))) )),
% 1.63/0.60    inference(superposition,[],[f34,f47])).
% 1.63/0.60  fof(f47,plain,(
% 1.63/0.60    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.63/0.60    inference(superposition,[],[f45,f26])).
% 1.63/0.60  fof(f45,plain,(
% 1.63/0.60    ( ! [X0] : (k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),X0)) )),
% 1.63/0.60    inference(resolution,[],[f44,f30])).
% 1.63/0.60  fof(f44,plain,(
% 1.63/0.60    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,sK1),X0)) )),
% 1.63/0.60    inference(resolution,[],[f38,f24])).
% 1.63/0.60  fof(f24,plain,(
% 1.63/0.60    r1_xboole_0(sK0,sK1)),
% 1.63/0.60    inference(cnf_transformation,[],[f17])).
% 1.63/0.60  fof(f17,plain,(
% 1.63/0.60    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1)),
% 1.63/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f16])).
% 1.63/0.60  fof(f16,plain,(
% 1.63/0.60    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1)) => (k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1))),
% 1.63/0.60    introduced(choice_axiom,[])).
% 1.63/0.60  fof(f11,plain,(
% 1.63/0.60    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1))),
% 1.63/0.60    inference(ennf_transformation,[],[f9])).
% 1.63/0.60  fof(f9,negated_conjecture,(
% 1.63/0.60    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 1.63/0.60    inference(negated_conjecture,[],[f8])).
% 1.63/0.60  fof(f8,conjecture,(
% 1.63/0.60    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 1.63/0.60  fof(f38,plain,(
% 1.63/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 1.63/0.60    inference(resolution,[],[f32,f29])).
% 1.63/0.60  fof(f29,plain,(
% 1.63/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f19])).
% 1.63/0.60  fof(f19,plain,(
% 1.63/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.63/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f18])).
% 1.63/0.60  fof(f18,plain,(
% 1.63/0.60    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.63/0.60    introduced(choice_axiom,[])).
% 1.63/0.60  fof(f12,plain,(
% 1.63/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.63/0.60    inference(ennf_transformation,[],[f10])).
% 1.63/0.60  fof(f10,plain,(
% 1.63/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.63/0.60    inference(rectify,[],[f2])).
% 1.63/0.60  fof(f2,axiom,(
% 1.63/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.63/0.60  fof(f25,plain,(
% 1.63/0.60    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)),
% 1.63/0.60    inference(cnf_transformation,[],[f17])).
% 1.63/0.60  % SZS output end Proof for theBenchmark
% 1.63/0.60  % (11331)------------------------------
% 1.63/0.60  % (11331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.60  % (11331)Termination reason: Refutation
% 1.63/0.60  
% 1.63/0.60  % (11331)Memory used [KB]: 7164
% 1.63/0.60  % (11331)Time elapsed: 0.191 s
% 1.63/0.60  % (11331)------------------------------
% 1.63/0.60  % (11331)------------------------------
% 1.63/0.60  % (11323)Success in time 0.233 s
%------------------------------------------------------------------------------
