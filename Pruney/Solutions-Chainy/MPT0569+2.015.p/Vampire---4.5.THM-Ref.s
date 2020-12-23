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
% DateTime   : Thu Dec  3 12:50:28 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 270 expanded)
%              Number of leaves         :   10 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :  146 ( 616 expanded)
%              Number of equality atoms :   33 ( 167 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f540,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f404,f368,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK9(X0,X2),X2),X0)
      | ~ sP8(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f368,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(X0,sK6(k2_relat_1(sK1),sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f351,f354,f25])).

fof(f25,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f354,plain,(
    r2_hidden(sK6(k2_relat_1(sK1),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f349,f188])).

fof(f188,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(X2,X3),X3)
      | r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f169,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ sP12(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f169,plain,(
    ! [X0,X1] :
      ( sP12(sK6(X0,X1),X1,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f55,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))
      | sP12(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( sP12(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f51,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( sP12(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

% (15513)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f349,plain,(
    ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f348])).

fof(f348,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f342])).

fof(f342,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(superposition,[],[f21,f337])).

fof(f337,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(sK1,X0)
      | ~ r1_xboole_0(k2_relat_1(sK1),X0) ) ),
    inference(forward_demodulation,[],[f334,f201])).

fof(f201,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f192,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f192,plain,(
    ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f22,f80,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k10_relat_1(X0,X1))
      | sP3(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,(
    ! [X0,X1] : ~ sP3(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f75,f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X1)
      | ~ sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f72,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f24,f33])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f72,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f23,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f23,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f334,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,k1_xboole_0) = k10_relat_1(sK1,X0)
      | ~ r1_xboole_0(k2_relat_1(sK1),X0) ) ),
    inference(superposition,[],[f324,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f56,f32])).

fof(f324,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0))) ),
    inference(unit_resulting_resolution,[],[f22,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f36,f33])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f21,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f351,plain,(
    ! [X0] : ~ sP3(X0,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f349,f224])).

fof(f224,plain,(
    ! [X0] :
      ( ~ sP3(X0,sK0,sK1)
      | r1_xboole_0(k2_relat_1(sK1),sK0) ) ),
    inference(global_subsumption,[],[f22,f75,f221])).

% (15534)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f221,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ sP3(X0,sK0,sK1)
      | ~ v1_relat_1(sK1)
      | r1_xboole_0(k2_relat_1(sK1),sK0) ) ),
    inference(superposition,[],[f63,f20])).

fof(f20,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k10_relat_1(X0,X1))
      | ~ sP3(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f404,plain,(
    sP8(sK6(k2_relat_1(sK1),sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f353,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP8(X2,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( sP8(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f353,plain,(
    r2_hidden(sK6(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f349,f189])).

fof(f189,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK6(X4,X5),X4)
      | r1_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f169,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ sP12(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:47:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.53  % (15530)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.54  % (15523)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.54  % (15514)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.54  % (15515)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.54  % (15516)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.55  % (15522)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.55  % (15530)Refutation not found, incomplete strategy% (15530)------------------------------
% 0.19/0.55  % (15530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (15532)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.55  % (15524)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.56  % (15530)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (15530)Memory used [KB]: 10746
% 0.19/0.56  % (15530)Time elapsed: 0.131 s
% 0.19/0.56  % (15530)------------------------------
% 0.19/0.56  % (15530)------------------------------
% 0.19/0.56  % (15531)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.53/0.57  % (15510)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.81/0.59  % (15526)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.81/0.59  % (15517)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.81/0.59  % (15532)Refutation found. Thanks to Tanya!
% 1.81/0.59  % SZS status Theorem for theBenchmark
% 1.81/0.59  % (15518)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.81/0.60  % (15518)Refutation not found, incomplete strategy% (15518)------------------------------
% 1.81/0.60  % (15518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.60  % (15518)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.60  
% 1.81/0.60  % (15518)Memory used [KB]: 10618
% 1.81/0.60  % (15518)Time elapsed: 0.180 s
% 1.81/0.60  % (15518)------------------------------
% 1.81/0.60  % (15518)------------------------------
% 1.81/0.60  % SZS output start Proof for theBenchmark
% 1.81/0.60  fof(f540,plain,(
% 1.81/0.60    $false),
% 1.81/0.60    inference(unit_resulting_resolution,[],[f404,f368,f37])).
% 1.81/0.60  fof(f37,plain,(
% 1.81/0.60    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK9(X0,X2),X2),X0) | ~sP8(X2,X0)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f8])).
% 1.81/0.60  fof(f8,axiom,(
% 1.81/0.60    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.81/0.60  fof(f368,plain,(
% 1.81/0.60    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK6(k2_relat_1(sK1),sK0)),sK1)) )),
% 1.81/0.60    inference(unit_resulting_resolution,[],[f351,f354,f25])).
% 1.81/0.60  fof(f25,plain,(
% 1.81/0.60    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | sP3(X3,X1,X0)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f15])).
% 1.81/0.60  fof(f15,plain,(
% 1.81/0.60    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 1.81/0.60    inference(ennf_transformation,[],[f7])).
% 1.81/0.60  fof(f7,axiom,(
% 1.81/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 1.81/0.60  fof(f354,plain,(
% 1.81/0.60    r2_hidden(sK6(k2_relat_1(sK1),sK0),sK0)),
% 1.81/0.60    inference(unit_resulting_resolution,[],[f349,f188])).
% 1.81/0.60  fof(f188,plain,(
% 1.81/0.60    ( ! [X2,X3] : (r2_hidden(sK6(X2,X3),X3) | r1_xboole_0(X2,X3)) )),
% 1.81/0.60    inference(resolution,[],[f169,f49])).
% 1.81/0.60  fof(f49,plain,(
% 1.81/0.60    ( ! [X0,X3,X1] : (~sP12(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f1])).
% 1.81/0.60  fof(f1,axiom,(
% 1.81/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.81/0.60  fof(f169,plain,(
% 1.81/0.60    ( ! [X0,X1] : (sP12(sK6(X0,X1),X1,X0) | r1_xboole_0(X0,X1)) )),
% 1.81/0.60    inference(resolution,[],[f55,f66])).
% 1.81/0.60  fof(f66,plain,(
% 1.81/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) | sP12(X3,X1,X0)) )),
% 1.81/0.60    inference(equality_resolution,[],[f60])).
% 1.81/0.60  fof(f60,plain,(
% 1.81/0.60    ( ! [X2,X0,X3,X1] : (sP12(X3,X1,X0) | ~r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.81/0.60    inference(definition_unfolding,[],[f51,f33])).
% 1.81/0.60  fof(f33,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.81/0.60    inference(cnf_transformation,[],[f6])).
% 1.81/0.60  fof(f6,axiom,(
% 1.81/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.81/0.60  fof(f51,plain,(
% 1.81/0.60    ( ! [X2,X0,X3,X1] : (sP12(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.81/0.60    inference(cnf_transformation,[],[f1])).
% 1.81/0.60  fof(f55,plain,(
% 1.81/0.60    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 1.81/0.60    inference(definition_unfolding,[],[f35,f33])).
% 1.81/0.60  fof(f35,plain,(
% 1.81/0.60    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.81/0.60    inference(cnf_transformation,[],[f17])).
% 1.81/0.60  fof(f17,plain,(
% 1.81/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.81/0.60    inference(ennf_transformation,[],[f13])).
% 1.81/0.60  fof(f13,plain,(
% 1.81/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.81/0.60    inference(rectify,[],[f2])).
% 1.81/0.60  % (15513)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.81/0.60  fof(f2,axiom,(
% 1.81/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.81/0.60  fof(f349,plain,(
% 1.81/0.60    ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.81/0.60    inference(trivial_inequality_removal,[],[f348])).
% 1.81/0.60  fof(f348,plain,(
% 1.81/0.60    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.81/0.60    inference(duplicate_literal_removal,[],[f342])).
% 1.81/0.60  fof(f342,plain,(
% 1.81/0.60    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),sK0) | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.81/0.60    inference(superposition,[],[f21,f337])).
% 1.81/0.60  fof(f337,plain,(
% 1.81/0.60    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK1,X0) | ~r1_xboole_0(k2_relat_1(sK1),X0)) )),
% 1.81/0.60    inference(forward_demodulation,[],[f334,f201])).
% 1.81/0.60  fof(f201,plain,(
% 1.81/0.60    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.81/0.60    inference(unit_resulting_resolution,[],[f192,f32])).
% 1.81/0.60  fof(f32,plain,(
% 1.81/0.60    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 1.81/0.60    inference(cnf_transformation,[],[f16])).
% 1.81/0.60  fof(f16,plain,(
% 1.81/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.81/0.60    inference(ennf_transformation,[],[f3])).
% 1.81/0.60  fof(f3,axiom,(
% 1.81/0.60    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.81/0.60  fof(f192,plain,(
% 1.81/0.60    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,k1_xboole_0))) )),
% 1.81/0.60    inference(unit_resulting_resolution,[],[f22,f80,f62])).
% 1.81/0.60  fof(f62,plain,(
% 1.81/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,k10_relat_1(X0,X1)) | sP3(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 1.81/0.60    inference(equality_resolution,[],[f29])).
% 1.81/0.60  fof(f29,plain,(
% 1.81/0.60    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 1.81/0.60    inference(cnf_transformation,[],[f15])).
% 1.81/0.60  fof(f80,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~sP3(X0,k1_xboole_0,X1)) )),
% 1.81/0.60    inference(unit_resulting_resolution,[],[f75,f27])).
% 1.81/0.60  fof(f27,plain,(
% 1.81/0.60    ( ! [X0,X3,X1] : (r2_hidden(sK4(X0,X1,X3),X1) | ~sP3(X3,X1,X0)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f15])).
% 1.81/0.60  fof(f75,plain,(
% 1.81/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.81/0.60    inference(forward_demodulation,[],[f72,f54])).
% 1.81/0.60  fof(f54,plain,(
% 1.81/0.60    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.81/0.60    inference(definition_unfolding,[],[f24,f33])).
% 1.81/0.60  fof(f24,plain,(
% 1.81/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f4])).
% 1.81/0.60  fof(f4,axiom,(
% 1.81/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.81/0.60  fof(f72,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))) )),
% 1.81/0.60    inference(unit_resulting_resolution,[],[f23,f56])).
% 1.81/0.60  fof(f56,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.81/0.60    inference(definition_unfolding,[],[f34,f33])).
% 1.81/0.60  fof(f34,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f17])).
% 1.81/0.60  fof(f23,plain,(
% 1.81/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f5])).
% 1.81/0.60  fof(f5,axiom,(
% 1.81/0.60    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.81/0.60  fof(f22,plain,(
% 1.81/0.60    v1_relat_1(sK1)),
% 1.81/0.60    inference(cnf_transformation,[],[f14])).
% 1.81/0.60  fof(f14,plain,(
% 1.81/0.60    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.81/0.60    inference(ennf_transformation,[],[f12])).
% 1.81/0.60  fof(f12,negated_conjecture,(
% 1.81/0.60    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.81/0.60    inference(negated_conjecture,[],[f11])).
% 1.81/0.60  fof(f11,conjecture,(
% 1.81/0.60    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 1.81/0.60  fof(f334,plain,(
% 1.81/0.60    ( ! [X0] : (k10_relat_1(sK1,k1_xboole_0) = k10_relat_1(sK1,X0) | ~r1_xboole_0(k2_relat_1(sK1),X0)) )),
% 1.81/0.60    inference(superposition,[],[f324,f73])).
% 1.81/0.60  fof(f73,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.81/0.60    inference(resolution,[],[f56,f32])).
% 1.81/0.60  fof(f324,plain,(
% 1.81/0.60    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0)))) )),
% 1.81/0.60    inference(unit_resulting_resolution,[],[f22,f57])).
% 1.81/0.60  fof(f57,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.81/0.60    inference(definition_unfolding,[],[f36,f33])).
% 1.81/0.60  fof(f36,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 1.81/0.60    inference(cnf_transformation,[],[f18])).
% 1.81/0.60  fof(f18,plain,(
% 1.81/0.60    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.81/0.60    inference(ennf_transformation,[],[f10])).
% 1.81/0.60  fof(f10,axiom,(
% 1.81/0.60    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.81/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 1.81/0.60  fof(f21,plain,(
% 1.81/0.60    k1_xboole_0 != k10_relat_1(sK1,sK0) | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.81/0.60    inference(cnf_transformation,[],[f14])).
% 1.81/0.60  fof(f351,plain,(
% 1.81/0.60    ( ! [X0] : (~sP3(X0,sK0,sK1)) )),
% 1.81/0.60    inference(unit_resulting_resolution,[],[f349,f224])).
% 1.81/0.60  fof(f224,plain,(
% 1.81/0.60    ( ! [X0] : (~sP3(X0,sK0,sK1) | r1_xboole_0(k2_relat_1(sK1),sK0)) )),
% 1.81/0.60    inference(global_subsumption,[],[f22,f75,f221])).
% 1.81/0.60  % (15534)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.81/0.60  fof(f221,plain,(
% 1.81/0.60    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~sP3(X0,sK0,sK1) | ~v1_relat_1(sK1) | r1_xboole_0(k2_relat_1(sK1),sK0)) )),
% 1.81/0.60    inference(superposition,[],[f63,f20])).
% 1.81/0.60  fof(f20,plain,(
% 1.81/0.60    k1_xboole_0 = k10_relat_1(sK1,sK0) | r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.81/0.60    inference(cnf_transformation,[],[f14])).
% 1.81/0.60  fof(f63,plain,(
% 1.81/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,k10_relat_1(X0,X1)) | ~sP3(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 1.81/0.60    inference(equality_resolution,[],[f28])).
% 1.81/0.60  fof(f28,plain,(
% 1.81/0.60    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 1.81/0.60    inference(cnf_transformation,[],[f15])).
% 1.81/0.60  fof(f404,plain,(
% 1.81/0.60    sP8(sK6(k2_relat_1(sK1),sK0),sK1)),
% 1.81/0.60    inference(unit_resulting_resolution,[],[f353,f64])).
% 1.81/0.60  fof(f64,plain,(
% 1.81/0.60    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | sP8(X2,X0)) )),
% 1.81/0.60    inference(equality_resolution,[],[f40])).
% 1.81/0.60  fof(f40,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (sP8(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.81/0.60    inference(cnf_transformation,[],[f8])).
% 1.81/0.60  fof(f353,plain,(
% 1.81/0.60    r2_hidden(sK6(k2_relat_1(sK1),sK0),k2_relat_1(sK1))),
% 1.81/0.60    inference(unit_resulting_resolution,[],[f349,f189])).
% 1.81/0.60  fof(f189,plain,(
% 1.81/0.60    ( ! [X4,X5] : (r2_hidden(sK6(X4,X5),X4) | r1_xboole_0(X4,X5)) )),
% 1.81/0.60    inference(resolution,[],[f169,f48])).
% 1.81/0.60  fof(f48,plain,(
% 1.81/0.60    ( ! [X0,X3,X1] : (~sP12(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f1])).
% 1.81/0.60  % SZS output end Proof for theBenchmark
% 1.81/0.60  % (15532)------------------------------
% 1.81/0.60  % (15532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.60  % (15532)Termination reason: Refutation
% 1.81/0.60  
% 1.81/0.60  % (15532)Memory used [KB]: 6652
% 1.81/0.60  % (15532)Time elapsed: 0.182 s
% 1.81/0.60  % (15532)------------------------------
% 1.81/0.60  % (15532)------------------------------
% 1.81/0.60  % (15507)Success in time 0.255 s
%------------------------------------------------------------------------------
