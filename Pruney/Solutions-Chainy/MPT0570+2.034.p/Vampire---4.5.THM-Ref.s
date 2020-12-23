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
% DateTime   : Thu Dec  3 12:50:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  90 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :   17
%              Number of atoms          :  160 ( 298 expanded)
%              Number of equality atoms :   26 (  66 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f381,plain,(
    $false ),
    inference(subsumption_resolution,[],[f367,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
            & r1_tarski(X0,k2_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(f367,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f358,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f358,plain,(
    ! [X0] : r1_xboole_0(sK0,X0) ),
    inference(resolution,[],[f357,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f357,plain,(
    ! [X8] : ~ r2_hidden(X8,sK0) ),
    inference(duplicate_literal_removal,[],[f355])).

fof(f355,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,sK0)
      | ~ r2_hidden(X8,sK0) ) ),
    inference(resolution,[],[f349,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k2_relat_1(sK1))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f64,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f35,f26])).

fof(f26,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f349,plain,(
    r1_xboole_0(sK0,k2_relat_1(sK1)) ),
    inference(superposition,[],[f347,f61])).

fof(f61,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(resolution,[],[f30,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f347,plain,(
    ! [X0] : r1_xboole_0(sK0,k9_relat_1(sK1,X0)) ),
    inference(duplicate_literal_removal,[],[f342])).

fof(f342,plain,(
    ! [X0] :
      ( r1_xboole_0(sK0,k9_relat_1(sK1,X0))
      | r1_xboole_0(sK0,k9_relat_1(sK1,X0)) ) ),
    inference(resolution,[],[f337,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f337,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(sK0,X0),k9_relat_1(sK1,X1))
      | r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f336,f33])).

fof(f336,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f332,f54])).

fof(f54,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f31,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f332,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,sK1),k1_xboole_0)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    inference(superposition,[],[f321,f27])).

fof(f27,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f321,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X2,sK1),k10_relat_1(sK1,X1))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X2)) ) ),
    inference(resolution,[],[f320,f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,sK1),X0),sK1)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f42,f24])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f320,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,k10_relat_1(sK1,X2)) ) ),
    inference(resolution,[],[f53,f24])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f48,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

% (23209)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:18:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (23200)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (23208)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (23216)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (23202)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (23201)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.57  % (23210)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (23200)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.58  % (23217)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.58  % (23218)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.58  % (23199)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f381,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(subsumption_resolution,[],[f367,f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    k1_xboole_0 != sK0),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,plain,(
% 0.21/0.58    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.21/0.58    inference(flattening,[],[f14])).
% 0.21/0.58  fof(f14,plain,(
% 0.21/0.58    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.58    inference(negated_conjecture,[],[f10])).
% 0.21/0.58  fof(f10,conjecture,(
% 0.21/0.58    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).
% 0.21/0.58  fof(f367,plain,(
% 0.21/0.58    k1_xboole_0 = sK0),
% 0.21/0.58    inference(resolution,[],[f358,f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f16])).
% 0.21/0.58  fof(f16,plain,(
% 0.21/0.58    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.58  fof(f358,plain,(
% 0.21/0.58    ( ! [X0] : (r1_xboole_0(sK0,X0)) )),
% 0.21/0.58    inference(resolution,[],[f357,f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.58    inference(ennf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,plain,(
% 0.21/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.58    inference(rectify,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.58  fof(f357,plain,(
% 0.21/0.58    ( ! [X8] : (~r2_hidden(X8,sK0)) )),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f355])).
% 0.21/0.58  fof(f355,plain,(
% 0.21/0.58    ( ! [X8] : (~r2_hidden(X8,sK0) | ~r2_hidden(X8,sK0)) )),
% 0.21/0.58    inference(resolution,[],[f349,f67])).
% 0.21/0.58  fof(f67,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_xboole_0(X1,k2_relat_1(sK1)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.58    inference(resolution,[],[f64,f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.58    inference(resolution,[],[f35,f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,plain,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.58    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.58  fof(f349,plain,(
% 0.21/0.58    r1_xboole_0(sK0,k2_relat_1(sK1))),
% 0.21/0.58    inference(superposition,[],[f347,f61])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 0.21/0.58    inference(resolution,[],[f30,f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    v1_relat_1(sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,plain,(
% 0.21/0.58    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.58  fof(f347,plain,(
% 0.21/0.58    ( ! [X0] : (r1_xboole_0(sK0,k9_relat_1(sK1,X0))) )),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f342])).
% 0.21/0.58  fof(f342,plain,(
% 0.21/0.58    ( ! [X0] : (r1_xboole_0(sK0,k9_relat_1(sK1,X0)) | r1_xboole_0(sK0,k9_relat_1(sK1,X0))) )),
% 0.21/0.58    inference(resolution,[],[f337,f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  fof(f337,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(sK2(sK0,X0),k9_relat_1(sK1,X1)) | r1_xboole_0(sK0,X0)) )),
% 0.21/0.58    inference(resolution,[],[f336,f33])).
% 0.21/0.58  fof(f336,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f332,f54])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.58    inference(superposition,[],[f31,f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.58    inference(equality_resolution,[],[f38])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.58  fof(f332,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,sK1),k1_xboole_0) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) )),
% 0.21/0.58    inference(superposition,[],[f321,f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f321,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X2,sK1),k10_relat_1(sK1,X1)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k9_relat_1(sK1,X2))) )),
% 0.21/0.58    inference(resolution,[],[f320,f168])).
% 0.21/0.58  fof(f168,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,sK1),X0),sK1) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) )),
% 0.21/0.58    inference(resolution,[],[f42,f24])).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.58    inference(ennf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.58  fof(f320,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(X1,X2) | r2_hidden(X0,k10_relat_1(sK1,X2))) )),
% 0.21/0.58    inference(resolution,[],[f53,f24])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f48,f40])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k2_relat_1(X2))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.58    inference(flattening,[],[f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.58    inference(ennf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.58    inference(ennf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.58  % (23209)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (23200)------------------------------
% 0.21/0.58  % (23200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (23200)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (23200)Memory used [KB]: 6396
% 0.21/0.58  % (23200)Time elapsed: 0.117 s
% 0.21/0.58  % (23200)------------------------------
% 0.21/0.58  % (23200)------------------------------
% 0.21/0.58  % (23193)Success in time 0.212 s
%------------------------------------------------------------------------------
