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
% DateTime   : Thu Dec  3 12:52:03 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 944 expanded)
%              Number of leaves         :   13 ( 269 expanded)
%              Depth                    :   18
%              Number of atoms          :  144 (2409 expanded)
%              Number of equality atoms :   51 ( 956 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f237,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f81,f222,f222,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f222,plain,(
    r2_hidden(sK4(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f66,f151])).

fof(f151,plain,(
    ! [X5] :
      ( r2_hidden(sK4(sK0,X5),X5)
      | sK0 = X5 ) ),
    inference(forward_demodulation,[],[f146,f142])).

fof(f142,plain,(
    sK0 = k1_relat_1(sK0) ),
    inference(unit_resulting_resolution,[],[f127,f132,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sP5(sK4(X0,X1),X0)
      | r2_hidden(sK4(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f132,plain,(
    ! [X0] : ~ sP5(X0,sK0) ),
    inference(unit_resulting_resolution,[],[f127,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
      | ~ sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f127,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(unit_resulting_resolution,[],[f126,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f31])).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f126,plain,(
    ! [X0] : ~ r1_tarski(k2_tarski(X0,X0),sK0) ),
    inference(global_subsumption,[],[f65,f123])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_tarski(X0,X0),sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f100,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_relat_1(sK2(X0,X1)) = k2_tarski(X1,X1)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f37,f31])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f100,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f69,f67,f90,f24])).

fof(f24,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),sK0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f90,plain,(
    ! [X0] : sK1 = k1_relat_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f65,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X0] : v1_relat_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f65,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    ! [X0] : v1_funct_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f65,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    k1_xboole_0 != sK1 ),
    inference(unit_resulting_resolution,[],[f29,f64])).

fof(f64,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(global_subsumption,[],[f58,f60,f63])).

fof(f63,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | k1_xboole_0 != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f62,f28])).

fof(f28,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f62,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),sK0) ),
    inference(superposition,[],[f24,f27])).

fof(f27,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f26,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

% (3339)Refutation not found, incomplete strategy% (3339)------------------------------
% (3339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

% (3339)Termination reason: Refutation not found, incomplete strategy

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

% (3339)Memory used [KB]: 10746
% (3339)Time elapsed: 0.116 s
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

% (3339)------------------------------
% (3339)------------------------------
fof(f58,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f26,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f146,plain,(
    ! [X5] :
      ( r2_hidden(sK4(sK0,X5),X5)
      | k1_relat_1(sK0) = X5 ) ),
    inference(resolution,[],[f47,f132])).

fof(f66,plain,(
    k1_xboole_0 != sK0 ),
    inference(unit_resulting_resolution,[],[f65,f25])).

fof(f25,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:46:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (3330)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (3330)Refutation not found, incomplete strategy% (3330)------------------------------
% 0.21/0.54  % (3330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3332)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (3347)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (3322)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (3325)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (3347)Refutation not found, incomplete strategy% (3347)------------------------------
% 0.21/0.55  % (3347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3347)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3347)Memory used [KB]: 10618
% 0.21/0.55  % (3347)Time elapsed: 0.127 s
% 0.21/0.55  % (3347)------------------------------
% 0.21/0.55  % (3347)------------------------------
% 0.21/0.55  % (3322)Refutation not found, incomplete strategy% (3322)------------------------------
% 0.21/0.55  % (3322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3322)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3322)Memory used [KB]: 1663
% 0.21/0.55  % (3322)Time elapsed: 0.122 s
% 0.21/0.55  % (3322)------------------------------
% 0.21/0.55  % (3322)------------------------------
% 0.21/0.55  % (3325)Refutation not found, incomplete strategy% (3325)------------------------------
% 0.21/0.55  % (3325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3325)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3325)Memory used [KB]: 10746
% 0.21/0.55  % (3325)Time elapsed: 0.122 s
% 0.21/0.55  % (3325)------------------------------
% 0.21/0.55  % (3325)------------------------------
% 0.21/0.55  % (3340)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (3344)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (3340)Refutation not found, incomplete strategy% (3340)------------------------------
% 0.21/0.55  % (3340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3340)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3340)Memory used [KB]: 10746
% 0.21/0.55  % (3340)Time elapsed: 0.139 s
% 0.21/0.55  % (3340)------------------------------
% 0.21/0.55  % (3340)------------------------------
% 0.21/0.55  % (3353)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (3330)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3330)Memory used [KB]: 6268
% 0.21/0.55  % (3330)Time elapsed: 0.127 s
% 0.21/0.55  % (3330)------------------------------
% 0.21/0.55  % (3330)------------------------------
% 0.21/0.55  % (3328)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (3351)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (3346)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (3355)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.56  % (3323)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.56  % (3354)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.56  % (3337)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.56  % (3350)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.56  % (3342)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.56  % (3339)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.56  % (3345)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.57  % (3350)Refutation not found, incomplete strategy% (3350)------------------------------
% 1.41/0.57  % (3350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (3350)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (3350)Memory used [KB]: 10746
% 1.41/0.57  % (3350)Time elapsed: 0.108 s
% 1.41/0.57  % (3350)------------------------------
% 1.41/0.57  % (3350)------------------------------
% 1.41/0.57  % (3332)Refutation not found, incomplete strategy% (3332)------------------------------
% 1.41/0.57  % (3332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (3332)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (3332)Memory used [KB]: 6268
% 1.41/0.57  % (3332)Time elapsed: 0.132 s
% 1.41/0.57  % (3332)------------------------------
% 1.41/0.57  % (3332)------------------------------
% 1.41/0.57  % (3345)Refutation not found, incomplete strategy% (3345)------------------------------
% 1.41/0.57  % (3345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (3345)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (3345)Memory used [KB]: 6140
% 1.41/0.57  % (3345)Time elapsed: 0.002 s
% 1.41/0.57  % (3345)------------------------------
% 1.41/0.57  % (3345)------------------------------
% 1.41/0.57  % (3359)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.57  % (3338)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.57  % (3341)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.57  % (3343)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.57  % (3349)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.57  % (3341)Refutation not found, incomplete strategy% (3341)------------------------------
% 1.41/0.57  % (3341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (3341)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (3341)Memory used [KB]: 10746
% 1.41/0.57  % (3341)Time elapsed: 0.148 s
% 1.41/0.57  % (3341)------------------------------
% 1.41/0.57  % (3341)------------------------------
% 1.41/0.57  % (3338)Refutation not found, incomplete strategy% (3338)------------------------------
% 1.41/0.57  % (3338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (3338)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (3338)Memory used [KB]: 10746
% 1.41/0.57  % (3338)Time elapsed: 0.105 s
% 1.41/0.57  % (3338)------------------------------
% 1.41/0.57  % (3338)------------------------------
% 1.41/0.57  % (3358)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.57  % (3357)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.57  % (3348)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.58  % (3335)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.58  % (3352)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.41/0.58  % (3351)Refutation not found, incomplete strategy% (3351)------------------------------
% 1.41/0.58  % (3351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.58  % (3351)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.58  
% 1.41/0.58  % (3351)Memory used [KB]: 1791
% 1.41/0.58  % (3351)Time elapsed: 0.157 s
% 1.41/0.58  % (3351)------------------------------
% 1.41/0.58  % (3351)------------------------------
% 1.41/0.58  % (3354)Refutation found. Thanks to Tanya!
% 1.41/0.58  % SZS status Theorem for theBenchmark
% 1.41/0.58  % SZS output start Proof for theBenchmark
% 1.41/0.58  fof(f237,plain,(
% 1.41/0.58    $false),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f81,f222,f222,f38])).
% 1.41/0.58  fof(f38,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f22])).
% 1.41/0.58  fof(f22,plain,(
% 1.41/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.41/0.58    inference(ennf_transformation,[],[f16])).
% 1.41/0.58  fof(f16,plain,(
% 1.41/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.41/0.58    inference(rectify,[],[f2])).
% 1.41/0.58  fof(f2,axiom,(
% 1.41/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.41/0.58  fof(f222,plain,(
% 1.41/0.58    r2_hidden(sK4(sK0,k1_xboole_0),k1_xboole_0)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f66,f151])).
% 1.41/0.58  fof(f151,plain,(
% 1.41/0.58    ( ! [X5] : (r2_hidden(sK4(sK0,X5),X5) | sK0 = X5) )),
% 1.41/0.58    inference(forward_demodulation,[],[f146,f142])).
% 1.41/0.58  fof(f142,plain,(
% 1.41/0.58    sK0 = k1_relat_1(sK0)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f127,f132,f47])).
% 1.41/0.58  fof(f47,plain,(
% 1.41/0.58    ( ! [X0,X1] : (sP5(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 1.41/0.58    inference(cnf_transformation,[],[f10])).
% 1.41/0.58  fof(f10,axiom,(
% 1.41/0.58    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.41/0.58  fof(f132,plain,(
% 1.41/0.58    ( ! [X0] : (~sP5(X0,sK0)) )),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f127,f43])).
% 1.41/0.58  fof(f43,plain,(
% 1.41/0.58    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~sP5(X2,X0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f10])).
% 1.41/0.58  fof(f127,plain,(
% 1.41/0.58    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f126,f55])).
% 1.41/0.58  fof(f55,plain,(
% 1.41/0.58    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.41/0.58    inference(definition_unfolding,[],[f49,f31])).
% 1.41/0.58  fof(f31,plain,(
% 1.41/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f6])).
% 1.41/0.58  fof(f6,axiom,(
% 1.41/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.41/0.58  fof(f49,plain,(
% 1.41/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f7])).
% 1.41/0.58  fof(f7,axiom,(
% 1.41/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.41/0.58  fof(f126,plain,(
% 1.41/0.58    ( ! [X0] : (~r1_tarski(k2_tarski(X0,X0),sK0)) )),
% 1.41/0.58    inference(global_subsumption,[],[f65,f123])).
% 1.41/0.58  fof(f123,plain,(
% 1.41/0.58    ( ! [X0] : (~r1_tarski(k2_tarski(X0,X0),sK0) | k1_xboole_0 = sK1) )),
% 1.41/0.58    inference(superposition,[],[f100,f53])).
% 1.41/0.58  fof(f53,plain,(
% 1.41/0.58    ( ! [X0,X1] : (k2_relat_1(sK2(X0,X1)) = k2_tarski(X1,X1) | k1_xboole_0 = X0) )),
% 1.41/0.58    inference(definition_unfolding,[],[f37,f31])).
% 1.41/0.58  fof(f37,plain,(
% 1.41/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = k2_relat_1(sK2(X0,X1))) )),
% 1.41/0.58    inference(cnf_transformation,[],[f21])).
% 1.41/0.58  fof(f21,plain,(
% 1.41/0.58    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.41/0.58    inference(ennf_transformation,[],[f13])).
% 1.41/0.58  fof(f13,axiom,(
% 1.41/0.58    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.41/0.58  fof(f100,plain,(
% 1.41/0.58    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)) )),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f69,f67,f90,f24])).
% 1.41/0.58  fof(f24,plain,(
% 1.41/0.58    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),sK0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f18])).
% 1.41/0.58  fof(f18,plain,(
% 1.41/0.58    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.41/0.58    inference(flattening,[],[f17])).
% 1.41/0.58  fof(f17,plain,(
% 1.41/0.58    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.41/0.58    inference(ennf_transformation,[],[f15])).
% 1.41/0.58  fof(f15,negated_conjecture,(
% 1.41/0.58    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.41/0.58    inference(negated_conjecture,[],[f14])).
% 1.41/0.58  fof(f14,conjecture,(
% 1.41/0.58    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 1.41/0.58  fof(f90,plain,(
% 1.41/0.58    ( ! [X0] : (sK1 = k1_relat_1(sK2(sK1,X0))) )),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f65,f36])).
% 1.41/0.58  fof(f36,plain,(
% 1.41/0.58    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.41/0.58    inference(cnf_transformation,[],[f21])).
% 1.41/0.58  fof(f67,plain,(
% 1.41/0.58    ( ! [X0] : (v1_relat_1(sK2(sK1,X0))) )),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f65,f34])).
% 1.41/0.58  fof(f34,plain,(
% 1.41/0.58    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.41/0.58    inference(cnf_transformation,[],[f21])).
% 1.41/0.58  fof(f69,plain,(
% 1.41/0.58    ( ! [X0] : (v1_funct_1(sK2(sK1,X0))) )),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f65,f35])).
% 1.41/0.58  fof(f35,plain,(
% 1.41/0.58    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.41/0.58    inference(cnf_transformation,[],[f21])).
% 1.41/0.58  fof(f65,plain,(
% 1.41/0.58    k1_xboole_0 != sK1),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f29,f64])).
% 1.41/0.58  fof(f64,plain,(
% 1.41/0.58    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,sK0)),
% 1.41/0.58    inference(global_subsumption,[],[f58,f60,f63])).
% 1.41/0.58  fof(f63,plain,(
% 1.41/0.58    ~r1_tarski(k1_xboole_0,sK0) | k1_xboole_0 != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.41/0.58    inference(forward_demodulation,[],[f62,f28])).
% 1.41/0.58  fof(f28,plain,(
% 1.41/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.41/0.58    inference(cnf_transformation,[],[f11])).
% 1.41/0.58  fof(f11,axiom,(
% 1.41/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.41/0.58  fof(f62,plain,(
% 1.41/0.58    k1_xboole_0 != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),sK0)),
% 1.41/0.58    inference(superposition,[],[f24,f27])).
% 1.41/0.58  fof(f27,plain,(
% 1.41/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.41/0.58    inference(cnf_transformation,[],[f11])).
% 1.41/0.58  fof(f60,plain,(
% 1.41/0.58    v1_relat_1(k1_xboole_0)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f26,f33])).
% 1.41/0.58  fof(f33,plain,(
% 1.41/0.58    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f20])).
% 1.41/0.58  % (3339)Refutation not found, incomplete strategy% (3339)------------------------------
% 1.41/0.58  % (3339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.58  fof(f20,plain,(
% 1.41/0.58    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.41/0.58    inference(ennf_transformation,[],[f9])).
% 1.41/0.58  % (3339)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.58  
% 1.41/0.58  fof(f9,axiom,(
% 1.41/0.58    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.41/0.58  fof(f26,plain,(
% 1.41/0.58    v1_xboole_0(k1_xboole_0)),
% 1.41/0.58    inference(cnf_transformation,[],[f1])).
% 1.41/0.58  % (3339)Memory used [KB]: 10746
% 1.41/0.58  % (3339)Time elapsed: 0.116 s
% 1.41/0.58  fof(f1,axiom,(
% 1.41/0.58    v1_xboole_0(k1_xboole_0)),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.41/0.58  % (3339)------------------------------
% 1.41/0.58  % (3339)------------------------------
% 1.41/0.58  fof(f58,plain,(
% 1.41/0.58    v1_funct_1(k1_xboole_0)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f26,f32])).
% 1.41/0.58  fof(f32,plain,(
% 1.41/0.58    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f19])).
% 1.41/0.58  fof(f19,plain,(
% 1.41/0.58    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 1.41/0.58    inference(ennf_transformation,[],[f12])).
% 1.41/0.58  fof(f12,axiom,(
% 1.41/0.58    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 1.41/0.58  fof(f29,plain,(
% 1.41/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f3])).
% 1.41/0.58  fof(f3,axiom,(
% 1.41/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.41/0.58  fof(f146,plain,(
% 1.41/0.58    ( ! [X5] : (r2_hidden(sK4(sK0,X5),X5) | k1_relat_1(sK0) = X5) )),
% 1.41/0.58    inference(resolution,[],[f47,f132])).
% 1.41/0.58  fof(f66,plain,(
% 1.41/0.58    k1_xboole_0 != sK0),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f65,f25])).
% 1.41/0.58  fof(f25,plain,(
% 1.41/0.58    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.41/0.58    inference(cnf_transformation,[],[f18])).
% 1.41/0.58  fof(f81,plain,(
% 1.41/0.58    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f30,f41])).
% 1.41/0.58  fof(f41,plain,(
% 1.41/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f5])).
% 1.41/0.58  fof(f5,axiom,(
% 1.41/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.41/0.58  fof(f30,plain,(
% 1.41/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f4])).
% 1.41/0.58  fof(f4,axiom,(
% 1.41/0.58    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.41/0.58  % SZS output end Proof for theBenchmark
% 1.41/0.58  % (3354)------------------------------
% 1.41/0.58  % (3354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.58  % (3354)Termination reason: Refutation
% 1.41/0.58  
% 1.41/0.58  % (3354)Memory used [KB]: 6396
% 1.41/0.58  % (3354)Time elapsed: 0.149 s
% 1.41/0.58  % (3354)------------------------------
% 1.41/0.58  % (3354)------------------------------
% 1.41/0.58  % (3320)Success in time 0.206 s
%------------------------------------------------------------------------------
