%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:51 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 239 expanded)
%              Number of leaves         :   15 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          :  106 ( 291 expanded)
%              Number of equality atoms :   59 ( 241 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(subsumption_resolution,[],[f238,f230])).

fof(f230,plain,(
    ~ r1_tarski(k1_enumset1(sK1,sK1,sK1),sK0) ),
    inference(subsumption_resolution,[],[f229,f55])).

fof(f55,plain,(
    sK0 != k1_enumset1(sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f31,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f229,plain,
    ( ~ r1_tarski(k1_enumset1(sK1,sK1,sK1),sK0)
    | sK0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(superposition,[],[f80,f199])).

fof(f199,plain,(
    k1_enumset1(sK1,sK1,sK1) = k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f198,f39])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f198,plain,(
    k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f193,f148])).

fof(f148,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(forward_demodulation,[],[f144,f143])).

fof(f143,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(forward_demodulation,[],[f129,f39])).

fof(f129,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f90,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f90,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f41,f40])).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f144,plain,(
    ! [X2,X1] : k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) = X2 ),
    inference(backward_demodulation,[],[f121,f143])).

fof(f121,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f41,f104])).

fof(f104,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X2) ),
    inference(superposition,[],[f89,f40])).

fof(f89,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f41,f39])).

fof(f193,plain,(
    k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0))) ),
    inference(superposition,[],[f146,f40])).

fof(f146,plain,(
    ! [X10] : k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1))),X10)))) = X10 ),
    inference(backward_demodulation,[],[f101,f143])).

fof(f101,plain,(
    ! [X10] : k5_xboole_0(k1_xboole_0,X10) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1))),X10)))) ),
    inference(forward_demodulation,[],[f100,f41])).

fof(f100,plain,(
    ! [X10] : k5_xboole_0(k1_xboole_0,X10) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1)))),X10))) ),
    inference(forward_demodulation,[],[f93,f41])).

fof(f93,plain,(
    ! [X10] : k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1))))),X10)) = k5_xboole_0(k1_xboole_0,X10) ),
    inference(superposition,[],[f41,f65])).

fof(f65,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1)))))) ),
    inference(backward_demodulation,[],[f56,f41])).

fof(f56,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k1_enumset1(sK1,sK1,sK1)),k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1))))) ),
    inference(definition_unfolding,[],[f29,f53,f54])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f32,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f49])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X1)
      | k3_tarski(k1_enumset1(X1,X1,X2)) = X1 ) ),
    inference(resolution,[],[f47,f61])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f238,plain,(
    r1_tarski(k1_enumset1(sK1,sK1,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f231,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f54])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f231,plain,(
    r2_hidden(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f226,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f35,f54])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f226,plain,(
    ~ r1_xboole_0(k1_enumset1(sK1,sK1,sK1),sK0) ),
    inference(superposition,[],[f71,f199])).

fof(f71,plain,(
    ! [X0] : ~ r1_xboole_0(k3_tarski(k1_enumset1(sK0,sK0,X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f67,f61,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f67,plain,(
    ~ r1_xboole_0(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f30,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f30,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:09:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (31703)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (31714)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (31718)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.53  % (31703)Refutation not found, incomplete strategy% (31703)------------------------------
% 0.22/0.53  % (31703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31703)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31703)Memory used [KB]: 1791
% 0.22/0.53  % (31703)Time elapsed: 0.111 s
% 0.22/0.53  % (31703)------------------------------
% 0.22/0.53  % (31703)------------------------------
% 0.22/0.53  % (31729)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (31725)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (31702)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (31710)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (31718)Refutation not found, incomplete strategy% (31718)------------------------------
% 0.22/0.53  % (31718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31718)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31718)Memory used [KB]: 10618
% 0.22/0.53  % (31718)Time elapsed: 0.124 s
% 0.22/0.53  % (31718)------------------------------
% 0.22/0.53  % (31718)------------------------------
% 0.22/0.54  % (31713)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (31715)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (31706)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (31708)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (31720)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (31712)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (31714)Refutation not found, incomplete strategy% (31714)------------------------------
% 0.22/0.54  % (31714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31714)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (31714)Memory used [KB]: 10618
% 0.22/0.54  % (31714)Time elapsed: 0.133 s
% 0.22/0.54  % (31714)------------------------------
% 0.22/0.54  % (31714)------------------------------
% 0.22/0.54  % (31716)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.40/0.54  % (31717)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.40/0.54  % (31721)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.40/0.55  % (31705)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.40/0.55  % (31720)Refutation not found, incomplete strategy% (31720)------------------------------
% 1.40/0.55  % (31720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (31711)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.40/0.55  % (31722)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.40/0.55  % (31707)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.40/0.55  % (31724)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.40/0.55  % (31721)Refutation found. Thanks to Tanya!
% 1.40/0.55  % SZS status Theorem for theBenchmark
% 1.40/0.55  % SZS output start Proof for theBenchmark
% 1.40/0.55  fof(f239,plain,(
% 1.40/0.55    $false),
% 1.40/0.55    inference(subsumption_resolution,[],[f238,f230])).
% 1.40/0.55  fof(f230,plain,(
% 1.40/0.55    ~r1_tarski(k1_enumset1(sK1,sK1,sK1),sK0)),
% 1.40/0.55    inference(subsumption_resolution,[],[f229,f55])).
% 1.40/0.55  fof(f55,plain,(
% 1.40/0.55    sK0 != k1_enumset1(sK1,sK1,sK1)),
% 1.40/0.55    inference(definition_unfolding,[],[f31,f54])).
% 1.40/0.55  fof(f54,plain,(
% 1.40/0.55    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.40/0.55    inference(definition_unfolding,[],[f36,f49])).
% 1.40/0.55  fof(f49,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f13])).
% 1.40/0.55  fof(f13,axiom,(
% 1.40/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.40/0.55  fof(f36,plain,(
% 1.40/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f12])).
% 1.40/0.55  fof(f12,axiom,(
% 1.40/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.40/0.55  fof(f31,plain,(
% 1.40/0.55    sK0 != k1_tarski(sK1)),
% 1.40/0.55    inference(cnf_transformation,[],[f24])).
% 1.40/0.55  fof(f24,plain,(
% 1.40/0.55    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.40/0.55    inference(ennf_transformation,[],[f22])).
% 1.40/0.55  fof(f22,negated_conjecture,(
% 1.40/0.55    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.40/0.55    inference(negated_conjecture,[],[f21])).
% 1.40/0.55  fof(f21,conjecture,(
% 1.40/0.55    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 1.40/0.55  fof(f229,plain,(
% 1.40/0.55    ~r1_tarski(k1_enumset1(sK1,sK1,sK1),sK0) | sK0 = k1_enumset1(sK1,sK1,sK1)),
% 1.40/0.55    inference(superposition,[],[f80,f199])).
% 1.40/0.55  fof(f199,plain,(
% 1.40/0.55    k1_enumset1(sK1,sK1,sK1) = k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1)))),
% 1.40/0.55    inference(forward_demodulation,[],[f198,f39])).
% 1.40/0.55  fof(f39,plain,(
% 1.40/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.40/0.55    inference(cnf_transformation,[],[f5])).
% 1.40/0.55  fof(f5,axiom,(
% 1.40/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.40/0.55  fof(f198,plain,(
% 1.40/0.55    k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0)),
% 1.40/0.55    inference(forward_demodulation,[],[f193,f148])).
% 1.40/0.55  fof(f148,plain,(
% 1.40/0.55    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2) )),
% 1.40/0.55    inference(forward_demodulation,[],[f144,f143])).
% 1.40/0.55  fof(f143,plain,(
% 1.40/0.55    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.40/0.55    inference(forward_demodulation,[],[f129,f39])).
% 1.40/0.55  fof(f129,plain,(
% 1.40/0.55    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0)) )),
% 1.40/0.55    inference(superposition,[],[f90,f40])).
% 1.40/0.55  fof(f40,plain,(
% 1.40/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f10])).
% 1.40/0.55  fof(f10,axiom,(
% 1.40/0.55    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.40/0.55  fof(f90,plain,(
% 1.40/0.55    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 1.40/0.55    inference(superposition,[],[f41,f40])).
% 1.40/0.55  fof(f41,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f9])).
% 1.40/0.55  fof(f9,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.40/0.55  fof(f144,plain,(
% 1.40/0.55    ( ! [X2,X1] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) = X2) )),
% 1.40/0.55    inference(backward_demodulation,[],[f121,f143])).
% 1.40/0.55  fof(f121,plain,(
% 1.40/0.55    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2))) )),
% 1.40/0.55    inference(superposition,[],[f41,f104])).
% 1.40/0.55  fof(f104,plain,(
% 1.40/0.55    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X2)) )),
% 1.40/0.55    inference(superposition,[],[f89,f40])).
% 1.40/0.55  fof(f89,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 1.40/0.55    inference(superposition,[],[f41,f39])).
% 1.40/0.55  fof(f193,plain,(
% 1.40/0.55    k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_xboole_0)))),
% 1.40/0.55    inference(superposition,[],[f146,f40])).
% 1.40/0.55  fof(f146,plain,(
% 1.40/0.55    ( ! [X10] : (k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1))),X10)))) = X10) )),
% 1.40/0.55    inference(backward_demodulation,[],[f101,f143])).
% 1.40/0.55  fof(f101,plain,(
% 1.40/0.55    ( ! [X10] : (k5_xboole_0(k1_xboole_0,X10) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1))),X10))))) )),
% 1.40/0.55    inference(forward_demodulation,[],[f100,f41])).
% 1.40/0.55  fof(f100,plain,(
% 1.40/0.55    ( ! [X10] : (k5_xboole_0(k1_xboole_0,X10) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1)))),X10)))) )),
% 1.40/0.55    inference(forward_demodulation,[],[f93,f41])).
% 1.40/0.55  fof(f93,plain,(
% 1.40/0.55    ( ! [X10] : (k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1))))),X10)) = k5_xboole_0(k1_xboole_0,X10)) )),
% 1.40/0.55    inference(superposition,[],[f41,f65])).
% 1.40/0.55  fof(f65,plain,(
% 1.40/0.55    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1))))))),
% 1.40/0.55    inference(backward_demodulation,[],[f56,f41])).
% 1.40/0.55  fof(f56,plain,(
% 1.40/0.55    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k1_enumset1(sK1,sK1,sK1)),k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK1,sK1,sK1)))))),
% 1.40/0.55    inference(definition_unfolding,[],[f29,f53,f54])).
% 1.40/0.55  fof(f53,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X1))))) )),
% 1.40/0.55    inference(definition_unfolding,[],[f32,f52])).
% 1.40/0.55  fof(f52,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 1.40/0.55    inference(definition_unfolding,[],[f42,f51])).
% 1.40/0.55  fof(f51,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.40/0.55    inference(definition_unfolding,[],[f50,f49])).
% 1.40/0.55  fof(f50,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f20])).
% 1.40/0.55  fof(f20,axiom,(
% 1.40/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.40/0.55  fof(f42,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f11])).
% 1.40/0.55  fof(f11,axiom,(
% 1.40/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.40/0.55  fof(f32,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f4])).
% 1.40/0.55  fof(f4,axiom,(
% 1.40/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.40/0.55  fof(f29,plain,(
% 1.40/0.55    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.40/0.55    inference(cnf_transformation,[],[f24])).
% 1.40/0.55  fof(f80,plain,(
% 1.40/0.55    ( ! [X2,X1] : (~r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X1) | k3_tarski(k1_enumset1(X1,X1,X2)) = X1) )),
% 1.40/0.55    inference(resolution,[],[f47,f61])).
% 1.40/0.55  fof(f61,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 1.40/0.55    inference(definition_unfolding,[],[f48,f51])).
% 1.40/0.55  fof(f48,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f8])).
% 1.40/0.55  fof(f8,axiom,(
% 1.40/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.40/0.55  fof(f47,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.40/0.55    inference(cnf_transformation,[],[f3])).
% 1.40/0.55  fof(f3,axiom,(
% 1.40/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.40/0.55  fof(f238,plain,(
% 1.40/0.55    r1_tarski(k1_enumset1(sK1,sK1,sK1),sK0)),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f231,f58])).
% 1.40/0.55  fof(f58,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.40/0.55    inference(definition_unfolding,[],[f33,f54])).
% 1.40/0.55  fof(f33,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f18])).
% 1.40/0.55  fof(f18,axiom,(
% 1.40/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.40/0.55  fof(f231,plain,(
% 1.40/0.55    r2_hidden(sK1,sK0)),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f226,f59])).
% 1.40/0.55  fof(f59,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 1.40/0.55    inference(definition_unfolding,[],[f35,f54])).
% 1.40/0.55  fof(f35,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f25])).
% 1.40/0.55  fof(f25,plain,(
% 1.40/0.55    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.40/0.55    inference(ennf_transformation,[],[f19])).
% 1.40/0.55  fof(f19,axiom,(
% 1.40/0.55    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.40/0.55  fof(f226,plain,(
% 1.40/0.55    ~r1_xboole_0(k1_enumset1(sK1,sK1,sK1),sK0)),
% 1.40/0.55    inference(superposition,[],[f71,f199])).
% 1.40/0.55  fof(f71,plain,(
% 1.40/0.55    ( ! [X0] : (~r1_xboole_0(k3_tarski(k1_enumset1(sK0,sK0,X0)),sK0)) )),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f67,f61,f44])).
% 1.40/0.55  fof(f44,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1) | r1_xboole_0(X0,X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f28])).
% 1.40/0.55  fof(f28,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.40/0.55    inference(flattening,[],[f27])).
% 1.40/0.55  fof(f27,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.40/0.55    inference(ennf_transformation,[],[f6])).
% 1.40/0.55  fof(f6,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.40/0.55  fof(f67,plain,(
% 1.40/0.55    ~r1_xboole_0(sK0,sK0)),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f30,f37])).
% 1.40/0.55  fof(f37,plain,(
% 1.40/0.55    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.40/0.55    inference(cnf_transformation,[],[f26])).
% 1.40/0.55  fof(f26,plain,(
% 1.40/0.55    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.40/0.55    inference(ennf_transformation,[],[f7])).
% 1.40/0.55  fof(f7,axiom,(
% 1.40/0.55    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.40/0.55  fof(f30,plain,(
% 1.40/0.55    k1_xboole_0 != sK0),
% 1.40/0.55    inference(cnf_transformation,[],[f24])).
% 1.40/0.55  % SZS output end Proof for theBenchmark
% 1.40/0.55  % (31721)------------------------------
% 1.40/0.55  % (31721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (31721)Termination reason: Refutation
% 1.40/0.55  
% 1.40/0.55  % (31721)Memory used [KB]: 1791
% 1.40/0.55  % (31721)Time elapsed: 0.140 s
% 1.40/0.55  % (31721)------------------------------
% 1.40/0.55  % (31721)------------------------------
% 1.40/0.55  % (31716)Refutation not found, incomplete strategy% (31716)------------------------------
% 1.40/0.55  % (31716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (31716)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (31716)Memory used [KB]: 1663
% 1.40/0.55  % (31716)Time elapsed: 0.095 s
% 1.40/0.55  % (31716)------------------------------
% 1.40/0.55  % (31716)------------------------------
% 1.40/0.55  % (31728)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.40/0.55  % (31701)Success in time 0.185 s
%------------------------------------------------------------------------------
