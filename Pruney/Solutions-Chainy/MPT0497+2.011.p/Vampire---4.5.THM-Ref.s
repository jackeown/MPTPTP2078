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
% DateTime   : Thu Dec  3 12:48:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 161 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  145 ( 314 expanded)
%              Number of equality atoms :   44 ( 124 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f271,plain,(
    $false ),
    inference(subsumption_resolution,[],[f270,f126])).

fof(f126,plain,(
    ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f125])).

fof(f125,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f29,f124])).

fof(f124,plain,(
    k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(resolution,[],[f115,f57])).

fof(f57,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(resolution,[],[f28,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f28,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f115,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k1_relat_1(sK1))
      | k1_xboole_0 = k7_relat_1(sK1,X0) ) ),
    inference(forward_demodulation,[],[f114,f67])).

fof(f67,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    inference(resolution,[],[f42,f30])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

% (13800)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f114,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k1_relat_1(sK1))
      | k1_xboole_0 = k5_relat_1(k6_relat_1(X0),sK1) ) ),
    inference(subsumption_resolution,[],[f113,f32])).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f113,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_xboole_0 = k5_relat_1(k6_relat_1(X0),sK1) ) ),
    inference(superposition,[],[f96,f34])).

fof(f34,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f96,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(sK1))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(X0,sK1) ) ),
    inference(resolution,[],[f35,f30])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
      | k1_xboole_0 = k5_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k5_relat_1(X0,X1)
          | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k5_relat_1(X0,X1)
          | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
           => k1_xboole_0 = k5_relat_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_relat_1)).

fof(f29,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f270,plain,(
    r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f261,f74])).

fof(f74,plain,(
    ! [X0] : r1_xboole_0(k1_relat_1(k1_xboole_0),X0) ),
    inference(resolution,[],[f73,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f73,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f72,f31])).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f72,plain,(
    ! [X6,X5] :
      ( ~ v1_xboole_0(X6)
      | ~ r2_hidden(X5,k1_relat_1(X6)) ) ),
    inference(resolution,[],[f55,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f55,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f261,plain,
    ( ~ r1_xboole_0(k1_relat_1(k1_xboole_0),sK0)
    | r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f250,f124])).

fof(f250,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0)
      | r1_xboole_0(k1_relat_1(sK1),X0) ) ),
    inference(superposition,[],[f202,f242])).

fof(f242,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)) ),
    inference(superposition,[],[f200,f198])).

fof(f198,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f53,f30])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f200,plain,(
    ! [X2,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ),
    inference(forward_demodulation,[],[f199,f33])).

fof(f33,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f199,plain,(
    ! [X2,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),X2)) ),
    inference(resolution,[],[f53,f32])).

fof(f202,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(backward_demodulation,[],[f54,f200])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:50:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (13813)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (13805)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (13802)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (13818)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.56  % (13806)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.57  % (13810)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.57  % (13810)Refutation not found, incomplete strategy% (13810)------------------------------
% 0.20/0.57  % (13810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (13810)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (13810)Memory used [KB]: 10618
% 0.20/0.57  % (13810)Time elapsed: 0.137 s
% 0.20/0.57  % (13810)------------------------------
% 0.20/0.57  % (13810)------------------------------
% 0.20/0.58  % (13823)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.58  % (13802)Refutation not found, incomplete strategy% (13802)------------------------------
% 0.20/0.58  % (13802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (13802)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (13802)Memory used [KB]: 10874
% 0.20/0.58  % (13802)Time elapsed: 0.145 s
% 0.20/0.58  % (13802)------------------------------
% 0.20/0.58  % (13802)------------------------------
% 0.20/0.59  % (13815)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.59  % (13803)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.59  % (13815)Refutation not found, incomplete strategy% (13815)------------------------------
% 0.20/0.59  % (13815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (13815)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (13815)Memory used [KB]: 6140
% 0.20/0.59  % (13815)Time elapsed: 0.001 s
% 0.20/0.59  % (13815)------------------------------
% 0.20/0.59  % (13815)------------------------------
% 0.20/0.59  % (13806)Refutation found. Thanks to Tanya!
% 0.20/0.59  % SZS status Theorem for theBenchmark
% 0.20/0.59  % SZS output start Proof for theBenchmark
% 0.20/0.59  fof(f271,plain,(
% 0.20/0.59    $false),
% 0.20/0.59    inference(subsumption_resolution,[],[f270,f126])).
% 0.20/0.59  fof(f126,plain,(
% 0.20/0.59    ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.59    inference(trivial_inequality_removal,[],[f125])).
% 0.20/0.59  fof(f125,plain,(
% 0.20/0.59    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.59    inference(backward_demodulation,[],[f29,f124])).
% 0.20/0.59  fof(f124,plain,(
% 0.20/0.59    k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f123])).
% 0.20/0.59  fof(f123,plain,(
% 0.20/0.59    k1_xboole_0 = k7_relat_1(sK1,sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.59    inference(resolution,[],[f115,f57])).
% 0.20/0.59  fof(f57,plain,(
% 0.20/0.59    r1_xboole_0(sK0,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.59    inference(resolution,[],[f28,f44])).
% 0.20/0.59  fof(f44,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f26])).
% 0.20/0.59  fof(f26,plain,(
% 0.20/0.59    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.59    inference(ennf_transformation,[],[f3])).
% 0.20/0.59  fof(f3,axiom,(
% 0.20/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.59  fof(f28,plain,(
% 0.20/0.59    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f19])).
% 0.20/0.59  fof(f19,plain,(
% 0.20/0.59    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.20/0.59    inference(ennf_transformation,[],[f16])).
% 0.20/0.59  fof(f16,negated_conjecture,(
% 0.20/0.59    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.59    inference(negated_conjecture,[],[f15])).
% 0.20/0.59  fof(f15,conjecture,(
% 0.20/0.59    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.59  fof(f115,plain,(
% 0.20/0.59    ( ! [X0] : (~r1_xboole_0(X0,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,X0)) )),
% 0.20/0.59    inference(forward_demodulation,[],[f114,f67])).
% 0.20/0.59  fof(f67,plain,(
% 0.20/0.59    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) )),
% 0.20/0.59    inference(resolution,[],[f42,f30])).
% 0.20/0.59  fof(f30,plain,(
% 0.20/0.59    v1_relat_1(sK1)),
% 0.20/0.59    inference(cnf_transformation,[],[f19])).
% 0.20/0.59  fof(f42,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f24])).
% 0.20/0.59  % (13800)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.59  fof(f24,plain,(
% 0.20/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.59    inference(ennf_transformation,[],[f14])).
% 0.20/0.59  fof(f14,axiom,(
% 0.20/0.59    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.59  fof(f114,plain,(
% 0.20/0.59    ( ! [X0] : (~r1_xboole_0(X0,k1_relat_1(sK1)) | k1_xboole_0 = k5_relat_1(k6_relat_1(X0),sK1)) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f113,f32])).
% 0.20/0.59  fof(f32,plain,(
% 0.20/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f10])).
% 0.20/0.59  fof(f10,axiom,(
% 0.20/0.59    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.59  fof(f113,plain,(
% 0.20/0.59    ( ! [X0] : (~r1_xboole_0(X0,k1_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(X0)) | k1_xboole_0 = k5_relat_1(k6_relat_1(X0),sK1)) )),
% 0.20/0.59    inference(superposition,[],[f96,f34])).
% 0.20/0.59  fof(f34,plain,(
% 0.20/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.59    inference(cnf_transformation,[],[f12])).
% 0.20/0.59  fof(f12,axiom,(
% 0.20/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.59  fof(f96,plain,(
% 0.20/0.59    ( ! [X0] : (~r1_xboole_0(k2_relat_1(X0),k1_relat_1(sK1)) | ~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X0,sK1)) )),
% 0.20/0.59    inference(resolution,[],[f35,f30])).
% 0.20/0.59  fof(f35,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) | k1_xboole_0 = k5_relat_1(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f21])).
% 0.20/0.59  fof(f21,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (k1_xboole_0 = k5_relat_1(X0,X1) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.59    inference(flattening,[],[f20])).
% 0.20/0.59  fof(f20,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : ((k1_xboole_0 = k5_relat_1(X0,X1) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f11])).
% 0.20/0.59  fof(f11,axiom,(
% 0.20/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) => k1_xboole_0 = k5_relat_1(X0,X1))))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_relat_1)).
% 0.20/0.59  fof(f29,plain,(
% 0.20/0.59    k1_xboole_0 != k7_relat_1(sK1,sK0) | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f19])).
% 0.20/0.59  fof(f270,plain,(
% 0.20/0.59    r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.59    inference(subsumption_resolution,[],[f261,f74])).
% 0.20/0.59  fof(f74,plain,(
% 0.20/0.59    ( ! [X0] : (r1_xboole_0(k1_relat_1(k1_xboole_0),X0)) )),
% 0.20/0.59    inference(resolution,[],[f73,f40])).
% 0.20/0.59  fof(f40,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f23])).
% 0.20/0.59  fof(f23,plain,(
% 0.20/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.59    inference(ennf_transformation,[],[f17])).
% 0.20/0.59  fof(f17,plain,(
% 0.20/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.59    inference(rectify,[],[f4])).
% 0.20/0.59  fof(f4,axiom,(
% 0.20/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.59  fof(f73,plain,(
% 0.20/0.59    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 0.20/0.59    inference(resolution,[],[f72,f31])).
% 0.20/0.59  fof(f31,plain,(
% 0.20/0.59    v1_xboole_0(k1_xboole_0)),
% 0.20/0.59    inference(cnf_transformation,[],[f2])).
% 0.20/0.59  fof(f2,axiom,(
% 0.20/0.59    v1_xboole_0(k1_xboole_0)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.59  fof(f72,plain,(
% 0.20/0.59    ( ! [X6,X5] : (~v1_xboole_0(X6) | ~r2_hidden(X5,k1_relat_1(X6))) )),
% 0.20/0.59    inference(resolution,[],[f55,f36])).
% 0.20/0.59  fof(f36,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f22])).
% 0.20/0.59  fof(f22,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f18])).
% 0.20/0.59  fof(f18,plain,(
% 0.20/0.59    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.59    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.59  fof(f1,axiom,(
% 0.20/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.59  fof(f55,plain,(
% 0.20/0.59    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.20/0.59    inference(equality_resolution,[],[f46])).
% 0.20/0.59  fof(f46,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.59    inference(cnf_transformation,[],[f9])).
% 0.20/0.59  fof(f9,axiom,(
% 0.20/0.59    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.59  fof(f261,plain,(
% 0.20/0.59    ~r1_xboole_0(k1_relat_1(k1_xboole_0),sK0) | r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.59    inference(superposition,[],[f250,f124])).
% 0.20/0.59  fof(f250,plain,(
% 0.20/0.59    ( ! [X0] : (~r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0) | r1_xboole_0(k1_relat_1(sK1),X0)) )),
% 0.20/0.59    inference(superposition,[],[f202,f242])).
% 0.20/0.59  fof(f242,plain,(
% 0.20/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(sK1)),X0))) )),
% 0.20/0.59    inference(superposition,[],[f200,f198])).
% 0.20/0.59  fof(f198,plain,(
% 0.20/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),X0))) )),
% 0.20/0.59    inference(resolution,[],[f53,f30])).
% 0.20/0.59  fof(f53,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f43,f52])).
% 0.20/0.59  fof(f52,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f37,f51])).
% 0.20/0.59  fof(f51,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f38,f50])).
% 0.20/0.59  fof(f50,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f7])).
% 0.20/0.59  fof(f7,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.59  fof(f38,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f6])).
% 0.20/0.59  fof(f6,axiom,(
% 0.20/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.59  fof(f37,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f8])).
% 0.20/0.59  fof(f8,axiom,(
% 0.20/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.59  fof(f43,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f25])).
% 0.20/0.59  fof(f25,plain,(
% 0.20/0.59    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.59    inference(ennf_transformation,[],[f13])).
% 0.20/0.59  fof(f13,axiom,(
% 0.20/0.59    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.59  fof(f200,plain,(
% 0.20/0.59    ( ! [X2,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) )),
% 0.20/0.59    inference(forward_demodulation,[],[f199,f33])).
% 0.20/0.59  fof(f33,plain,(
% 0.20/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.59    inference(cnf_transformation,[],[f12])).
% 0.20/0.59  fof(f199,plain,(
% 0.20/0.59    ( ! [X2,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),X2))) )),
% 0.20/0.59    inference(resolution,[],[f53,f32])).
% 0.20/0.59  fof(f202,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(backward_demodulation,[],[f54,f200])).
% 0.20/0.59  fof(f54,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r1_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f49,f52])).
% 0.20/0.59  fof(f49,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(k3_xboole_0(X0,X1),X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f27])).
% 0.20/0.59  fof(f27,plain,(
% 0.20/0.59    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.20/0.59    inference(ennf_transformation,[],[f5])).
% 0.20/0.59  fof(f5,axiom,(
% 0.20/0.59    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (13806)------------------------------
% 0.20/0.59  % (13806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (13806)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (13806)Memory used [KB]: 6396
% 0.20/0.59  % (13806)Time elapsed: 0.165 s
% 0.20/0.59  % (13806)------------------------------
% 0.20/0.59  % (13806)------------------------------
% 0.20/0.59  % (13799)Success in time 0.232 s
%------------------------------------------------------------------------------
