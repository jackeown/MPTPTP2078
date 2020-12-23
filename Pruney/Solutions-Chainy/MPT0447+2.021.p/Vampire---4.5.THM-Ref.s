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
% DateTime   : Thu Dec  3 12:47:11 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 213 expanded)
%              Number of leaves         :   10 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  150 ( 554 expanded)
%              Number of equality atoms :   13 (  65 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f718,plain,(
    $false ),
    inference(global_subsumption,[],[f579,f715])).

% (22833)Refutation not found, incomplete strategy% (22833)------------------------------
% (22833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22833)Termination reason: Refutation not found, incomplete strategy

% (22833)Memory used [KB]: 10746
% (22833)Time elapsed: 0.110 s
% (22833)------------------------------
% (22833)------------------------------
fof(f715,plain,(
    r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f26,f655,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ sP4(X1,X0) ) ),
    inference(resolution,[],[f47,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)
      | ~ sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f655,plain,(
    sP4(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f574,f388])).

fof(f388,plain,(
    ! [X0] :
      ( ~ sP4(X0,sK0)
      | sP4(X0,sK1) ) ),
    inference(resolution,[],[f383,f55])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | sP4(X2,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f383,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_relat_1(sK1))
      | ~ sP4(X3,sK0) ) ),
    inference(resolution,[],[f89,f155])).

fof(f155,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f29,f27,f26,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f27,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X1)
      | r2_hidden(X0,X1)
      | ~ sP4(X0,X2) ) ),
    inference(resolution,[],[f36,f56])).

fof(f56,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_relat_1(X0))
      | ~ sP4(X2,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f574,plain,(
    sP4(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f558,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( sP4(sK2(k1_relat_1(X0),X1),X0)
      | r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(resolution,[],[f37,f55])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f558,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f29,f28,f300,f245])).

fof(f245,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),X1)
      | r1_tarski(k3_relat_1(X0),X1)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f54,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f30,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

% (22814)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (22815)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (22816)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (22820)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f300,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f171,f288])).

fof(f288,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k2_relat_1(sK1))
      | r1_tarski(X1,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f53,f242])).

fof(f242,plain,(
    k3_relat_1(sK1) = k3_tarski(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f26,f52])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f51])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f171,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f29,f27,f26,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f579,plain,(
    ~ r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f558,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n008.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 20:07:45 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.19/0.40  % (22811)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.42  % (22811)Refutation not found, incomplete strategy% (22811)------------------------------
% 0.19/0.42  % (22811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (22811)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.42  
% 0.19/0.42  % (22811)Memory used [KB]: 1663
% 0.19/0.42  % (22811)Time elapsed: 0.046 s
% 0.19/0.42  % (22811)------------------------------
% 0.19/0.42  % (22811)------------------------------
% 0.19/0.42  % (22828)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.42  % (22828)Refutation not found, incomplete strategy% (22828)------------------------------
% 0.19/0.42  % (22828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (22828)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.42  
% 0.19/0.42  % (22828)Memory used [KB]: 10618
% 0.19/0.42  % (22828)Time elapsed: 0.055 s
% 0.19/0.42  % (22828)------------------------------
% 0.19/0.42  % (22828)------------------------------
% 0.19/0.43  % (22819)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.43  % (22819)Refutation not found, incomplete strategy% (22819)------------------------------
% 0.19/0.43  % (22819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (22819)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.43  
% 0.19/0.43  % (22819)Memory used [KB]: 10746
% 0.19/0.43  % (22819)Time elapsed: 0.056 s
% 0.19/0.43  % (22819)------------------------------
% 0.19/0.43  % (22819)------------------------------
% 0.19/0.43  % (22824)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.43  % (22812)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.44  % (22835)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.46  % (22827)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.46  % (22818)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.47  % (22835)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.48  % (22833)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f718,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(global_subsumption,[],[f579,f715])).
% 0.19/0.49  % (22833)Refutation not found, incomplete strategy% (22833)------------------------------
% 0.19/0.49  % (22833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (22833)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (22833)Memory used [KB]: 10746
% 0.19/0.49  % (22833)Time elapsed: 0.110 s
% 0.19/0.49  % (22833)------------------------------
% 0.19/0.49  % (22833)------------------------------
% 0.19/0.49  fof(f715,plain,(
% 0.19/0.49    r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f26,f655,f113])).
% 0.19/0.49  fof(f113,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r2_hidden(X1,k3_relat_1(X0)) | ~v1_relat_1(X0) | ~sP4(X1,X0)) )),
% 0.19/0.49    inference(resolution,[],[f47,f39])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0) | ~sP4(X2,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,axiom,(
% 0.19/0.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.19/0.49  fof(f47,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X0,k3_relat_1(X2))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(flattening,[],[f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(ennf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 0.19/0.49  fof(f655,plain,(
% 0.19/0.49    sP4(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),sK1)),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f574,f388])).
% 0.19/0.49  fof(f388,plain,(
% 0.19/0.49    ( ! [X0] : (~sP4(X0,sK0) | sP4(X0,sK1)) )),
% 0.19/0.49    inference(resolution,[],[f383,f55])).
% 0.19/0.49  fof(f55,plain,(
% 0.19/0.49    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | sP4(X2,X0)) )),
% 0.19/0.49    inference(equality_resolution,[],[f42])).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (sP4(X2,X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.19/0.49    inference(cnf_transformation,[],[f8])).
% 0.19/0.49  fof(f383,plain,(
% 0.19/0.49    ( ! [X3] : (r2_hidden(X3,k1_relat_1(sK1)) | ~sP4(X3,sK0)) )),
% 0.19/0.49    inference(resolution,[],[f89,f155])).
% 0.19/0.49  fof(f155,plain,(
% 0.19/0.49    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f29,f27,f26,f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(flattening,[],[f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    r1_tarski(sK0,sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.19/0.49    inference(flattening,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f13])).
% 0.19/0.49  fof(f13,negated_conjecture,(
% 0.19/0.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.19/0.49    inference(negated_conjecture,[],[f12])).
% 0.19/0.49  fof(f12,conjecture,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    v1_relat_1(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f15])).
% 0.19/0.49  fof(f89,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X1) | r2_hidden(X0,X1) | ~sP4(X0,X2)) )),
% 0.19/0.49    inference(resolution,[],[f36,f56])).
% 0.19/0.49  fof(f56,plain,(
% 0.19/0.49    ( ! [X2,X0] : (r2_hidden(X2,k1_relat_1(X0)) | ~sP4(X2,X0)) )),
% 0.19/0.49    inference(equality_resolution,[],[f41])).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~sP4(X2,X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.19/0.49    inference(cnf_transformation,[],[f8])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.49  fof(f574,plain,(
% 0.19/0.49    sP4(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),sK0)),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f558,f71])).
% 0.19/0.49  fof(f71,plain,(
% 0.19/0.49    ( ! [X0,X1] : (sP4(sK2(k1_relat_1(X0),X1),X0) | r1_tarski(k1_relat_1(X0),X1)) )),
% 0.19/0.49    inference(resolution,[],[f37,f55])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f20])).
% 0.19/0.49  fof(f558,plain,(
% 0.19/0.49    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f29,f28,f300,f245])).
% 0.19/0.49  fof(f245,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),X1) | r1_tarski(k3_relat_1(X0),X1) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(superposition,[],[f54,f52])).
% 0.19/0.49  fof(f52,plain,(
% 0.19/0.49    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f30,f51])).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.19/0.49    inference(definition_unfolding,[],[f34,f35])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.19/0.49  fof(f54,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f50,f51])).
% 0.19/0.49  fof(f50,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.19/0.49    inference(flattening,[],[f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.19/0.49    inference(ennf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.19/0.49  % (22814)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.49  % (22815)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.49  % (22816)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.49  % (22820)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.49  fof(f300,plain,(
% 0.19/0.49    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f171,f288])).
% 0.19/0.49  fof(f288,plain,(
% 0.19/0.49    ( ! [X1] : (~r1_tarski(X1,k2_relat_1(sK1)) | r1_tarski(X1,k3_relat_1(sK1))) )),
% 0.19/0.49    inference(superposition,[],[f53,f242])).
% 0.19/0.49  fof(f242,plain,(
% 0.19/0.49    k3_relat_1(sK1) = k3_tarski(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1)))),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f26,f52])).
% 0.19/0.49  fof(f53,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f49,f51])).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.19/0.49  fof(f171,plain,(
% 0.19/0.49    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f29,f27,f26,f32])).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f18])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 0.19/0.49    inference(cnf_transformation,[],[f15])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    v1_relat_1(sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f15])).
% 0.19/0.49  fof(f579,plain,(
% 0.19/0.49    ~r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f558,f38])).
% 0.19/0.49  fof(f38,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f20])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (22835)------------------------------
% 0.19/0.49  % (22835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (22835)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (22835)Memory used [KB]: 7036
% 0.19/0.49  % (22835)Time elapsed: 0.103 s
% 0.19/0.49  % (22835)------------------------------
% 0.19/0.49  % (22835)------------------------------
% 0.19/0.49  % (22836)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.50  % (22810)Success in time 0.155 s
%------------------------------------------------------------------------------
