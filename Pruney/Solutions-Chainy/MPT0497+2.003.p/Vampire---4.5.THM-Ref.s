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
% DateTime   : Thu Dec  3 12:48:24 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 395 expanded)
%              Number of leaves         :   11 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  180 ( 967 expanded)
%              Number of equality atoms :   63 ( 257 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1237,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1236,f1210])).

fof(f1210,plain,(
    ! [X0] : k1_xboole_0 = k1_relat_1(k7_relat_1(k1_xboole_0,X0)) ),
    inference(backward_demodulation,[],[f766,f1209])).

fof(f1209,plain,(
    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1208,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(resolution,[],[f63,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

% (25189)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f18,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] : r1_xboole_0(k1_setfam_1(k2_tarski(X0,k1_xboole_0)),X1) ),
    inference(resolution,[],[f60,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f60,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) ),
    inference(resolution,[],[f50,f29])).

fof(f29,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1208,plain,(
    k7_relat_1(sK1,k1_xboole_0) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,k1_xboole_0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1195,f56])).

fof(f56,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

% (25185)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f1195,plain,(
    k7_relat_1(sK1,k1_xboole_0) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,k1_xboole_0))))) ),
    inference(superposition,[],[f895,f301])).

fof(f301,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f296,f67])).

fof(f296,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f51,f26])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f41,f34])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f895,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(k7_relat_1(sK1,X0))))) ),
    inference(resolution,[],[f146,f26])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k1_setfam_1(k2_tarski(k7_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(X0,X1)),k2_relat_1(k7_relat_1(X0,X1))))) ) ),
    inference(resolution,[],[f47,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_setfam_1(k2_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f766,plain,(
    ! [X0] : k1_xboole_0 = k1_relat_1(k7_relat_1(k7_relat_1(sK1,k1_xboole_0),X0)) ),
    inference(forward_demodulation,[],[f738,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    inference(resolution,[],[f72,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f43,f34])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

% (25189)Refutation not found, incomplete strategy% (25189)------------------------------
% (25189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25189)Termination reason: Refutation not found, incomplete strategy

% (25189)Memory used [KB]: 10618
% (25189)Time elapsed: 0.172 s
% (25189)------------------------------
% (25189)------------------------------
fof(f72,plain,(
    ! [X1] : r1_xboole_0(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f63,f67])).

fof(f738,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_relat_1(k7_relat_1(k7_relat_1(sK1,k1_xboole_0),X0)) ),
    inference(superposition,[],[f706,f301])).

fof(f706,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1)) = k1_setfam_1(k2_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X1)) ),
    inference(resolution,[],[f297,f26])).

fof(f297,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k1_setfam_1(k2_tarski(k1_relat_1(k7_relat_1(X1,X2)),X3)) ) ),
    inference(resolution,[],[f51,f40])).

fof(f1236,plain,(
    k1_xboole_0 != k1_relat_1(k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))) ),
    inference(forward_demodulation,[],[f1231,f1214])).

fof(f1214,plain,(
    k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f1213])).

fof(f1213,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f1212,f67])).

fof(f1212,plain,
    ( k7_relat_1(sK1,sK0) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,sK0),k1_xboole_0))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f1196,f56])).

fof(f1196,plain,
    ( k7_relat_1(sK1,sK0) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,sK0)))))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(superposition,[],[f895,f298])).

fof(f298,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(superposition,[],[f296,f78])).

fof(f78,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(resolution,[],[f52,f24])).

% (25190)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f24,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f1231,plain,(
    k1_xboole_0 != k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(k7_relat_1(sK1,sK0)))) ),
    inference(resolution,[],[f1216,f716])).

fof(f716,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_relat_1(sK1),X0)
      | k1_xboole_0 != k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))) ) ),
    inference(backward_demodulation,[],[f502,f706])).

fof(f502,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_relat_1(sK1),X0)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)))) ) ),
    inference(resolution,[],[f491,f155])).

fof(f155,plain,(
    ! [X4,X3] :
      ( r1_xboole_0(X4,X3)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X3,X3)) ) ),
    inference(resolution,[],[f141,f131])).

fof(f131,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f58,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X2)
      | ~ r1_xboole_0(X2,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f37,f38])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f141,plain,(
    ! [X2,X1] :
      ( r1_xboole_0(X1,X2)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X1,X1)) ) ),
    inference(resolution,[],[f132,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f42,f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f58,f38])).

fof(f491,plain,(
    ! [X5] :
      ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X5)),k1_relat_1(k7_relat_1(sK1,X5)))
      | r1_xboole_0(k1_relat_1(sK1),X5) ) ),
    inference(forward_demodulation,[],[f486,f296])).

fof(f486,plain,(
    ! [X5] :
      ( r1_xboole_0(k1_relat_1(sK1),X5)
      | ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X5)),k1_setfam_1(k2_tarski(k1_relat_1(sK1),X5))) ) ),
    inference(duplicate_literal_removal,[],[f485])).

fof(f485,plain,(
    ! [X5] :
      ( r1_xboole_0(k1_relat_1(sK1),X5)
      | ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X5)),k1_setfam_1(k2_tarski(k1_relat_1(sK1),X5)))
      | r1_xboole_0(k1_relat_1(sK1),X5) ) ),
    inference(resolution,[],[f120,f306])).

fof(f306,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k1_relat_1(sK1),X1),k1_relat_1(k7_relat_1(sK1,X1)))
      | r1_xboole_0(k1_relat_1(sK1),X1) ) ),
    inference(superposition,[],[f49,f296])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X2)
      | r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(resolution,[],[f49,f37])).

fof(f1216,plain,(
    ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f1215])).

fof(f1215,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f25,f1214])).

fof(f25,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.38  ipcrm: permission denied for id (1218281474)
% 0.13/0.38  ipcrm: permission denied for id (1218314244)
% 0.13/0.40  ipcrm: permission denied for id (1218412558)
% 0.13/0.40  ipcrm: permission denied for id (1218445327)
% 0.21/0.41  ipcrm: permission denied for id (1218543641)
% 0.21/0.41  ipcrm: permission denied for id (1218576410)
% 0.21/0.42  ipcrm: permission denied for id (1218609181)
% 0.21/0.45  ipcrm: permission denied for id (1218773041)
% 0.21/0.45  ipcrm: permission denied for id (1218805813)
% 0.21/0.45  ipcrm: permission denied for id (1218838583)
% 0.21/0.45  ipcrm: permission denied for id (1218871352)
% 0.21/0.45  ipcrm: permission denied for id (1218904121)
% 0.21/0.46  ipcrm: permission denied for id (1218969660)
% 0.21/0.46  ipcrm: permission denied for id (1219002429)
% 0.21/0.46  ipcrm: permission denied for id (1219035198)
% 0.21/0.46  ipcrm: permission denied for id (1219133510)
% 0.21/0.47  ipcrm: permission denied for id (1219231822)
% 0.21/0.49  ipcrm: permission denied for id (1219428449)
% 0.21/0.49  ipcrm: permission denied for id (1219526757)
% 0.21/0.50  ipcrm: permission denied for id (1219756146)
% 0.21/0.51  ipcrm: permission denied for id (1219821691)
% 1.08/0.66  % (25178)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.68  % (25194)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.33/0.68  % (25195)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.33/0.69  % (25187)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.69  % (25186)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.69  % (25194)Refutation not found, incomplete strategy% (25194)------------------------------
% 1.33/0.69  % (25194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.69  % (25179)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.33/0.71  % (25177)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.33/0.71  % (25181)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.33/0.71  % (25194)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.71  
% 1.33/0.71  % (25194)Memory used [KB]: 10618
% 1.33/0.71  % (25194)Time elapsed: 0.115 s
% 1.33/0.71  % (25194)------------------------------
% 1.33/0.71  % (25194)------------------------------
% 1.33/0.71  % (25182)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.33/0.72  % (25176)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.33/0.72  % (25175)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.77/0.73  % (25200)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.77/0.73  % (25173)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.77/0.73  % (25174)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.77/0.73  % (25172)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.77/0.73  % (25201)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.77/0.73  % (25191)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.77/0.74  % (25198)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.77/0.74  % (25183)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.77/0.74  % (25193)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.77/0.74  % (25197)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.77/0.74  % (25184)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.77/0.74  % (25199)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.77/0.74  % (25192)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.77/0.75  % (25178)Refutation found. Thanks to Tanya!
% 1.77/0.75  % SZS status Theorem for theBenchmark
% 1.77/0.75  % SZS output start Proof for theBenchmark
% 1.77/0.75  fof(f1237,plain,(
% 1.77/0.75    $false),
% 1.77/0.75    inference(subsumption_resolution,[],[f1236,f1210])).
% 1.77/0.75  fof(f1210,plain,(
% 1.77/0.75    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k7_relat_1(k1_xboole_0,X0))) )),
% 1.77/0.75    inference(backward_demodulation,[],[f766,f1209])).
% 1.77/0.75  fof(f1209,plain,(
% 1.77/0.75    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)),
% 1.77/0.75    inference(forward_demodulation,[],[f1208,f67])).
% 1.77/0.75  fof(f67,plain,(
% 1.77/0.75    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.77/0.75    inference(resolution,[],[f63,f30])).
% 1.77/0.75  fof(f30,plain,(
% 1.77/0.75    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.77/0.75    inference(cnf_transformation,[],[f18])).
% 1.77/0.75  % (25189)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.77/0.75  fof(f18,plain,(
% 1.77/0.75    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.77/0.75    inference(ennf_transformation,[],[f6])).
% 1.77/0.75  fof(f6,axiom,(
% 1.77/0.75    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.77/0.75  fof(f63,plain,(
% 1.77/0.75    ( ! [X0,X1] : (r1_xboole_0(k1_setfam_1(k2_tarski(X0,k1_xboole_0)),X1)) )),
% 1.77/0.75    inference(resolution,[],[f60,f38])).
% 1.77/0.75  fof(f38,plain,(
% 1.77/0.75    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.77/0.75    inference(cnf_transformation,[],[f21])).
% 1.77/0.75  fof(f21,plain,(
% 1.77/0.75    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.77/0.75    inference(ennf_transformation,[],[f16])).
% 1.77/0.75  fof(f16,plain,(
% 1.77/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.77/0.75    inference(rectify,[],[f3])).
% 1.77/0.75  fof(f3,axiom,(
% 1.77/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.77/0.75  fof(f60,plain,(
% 1.77/0.75    ( ! [X0,X1] : (~r2_hidden(X0,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))) )),
% 1.77/0.75    inference(resolution,[],[f50,f29])).
% 1.77/0.75  fof(f29,plain,(
% 1.77/0.75    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.77/0.75    inference(cnf_transformation,[],[f5])).
% 1.77/0.75  fof(f5,axiom,(
% 1.77/0.75    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.77/0.75  fof(f50,plain,(
% 1.77/0.75    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.77/0.75    inference(definition_unfolding,[],[f35,f34])).
% 1.77/0.75  fof(f34,plain,(
% 1.77/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.77/0.75    inference(cnf_transformation,[],[f8])).
% 1.77/0.75  fof(f8,axiom,(
% 1.77/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.77/0.75  fof(f35,plain,(
% 1.77/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.77/0.75    inference(cnf_transformation,[],[f20])).
% 1.77/0.75  fof(f20,plain,(
% 1.77/0.75    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.77/0.75    inference(ennf_transformation,[],[f15])).
% 1.77/0.75  fof(f15,plain,(
% 1.77/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.77/0.75    inference(rectify,[],[f4])).
% 1.77/0.75  fof(f4,axiom,(
% 1.77/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.77/0.75  fof(f1208,plain,(
% 1.77/0.75    k7_relat_1(sK1,k1_xboole_0) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,k1_xboole_0),k1_xboole_0))),
% 1.77/0.75    inference(forward_demodulation,[],[f1195,f56])).
% 1.77/0.75  fof(f56,plain,(
% 1.77/0.75    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.77/0.75    inference(equality_resolution,[],[f45])).
% 1.77/0.75  fof(f45,plain,(
% 1.77/0.75    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.77/0.75    inference(cnf_transformation,[],[f7])).
% 1.77/0.75  fof(f7,axiom,(
% 1.77/0.75    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.77/0.75  % (25185)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.77/0.75  fof(f1195,plain,(
% 1.77/0.75    k7_relat_1(sK1,k1_xboole_0) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,k1_xboole_0)))))),
% 1.77/0.75    inference(superposition,[],[f895,f301])).
% 1.77/0.75  fof(f301,plain,(
% 1.77/0.75    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0))),
% 1.77/0.75    inference(superposition,[],[f296,f67])).
% 1.77/0.75  fof(f296,plain,(
% 1.77/0.75    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) )),
% 1.77/0.75    inference(resolution,[],[f51,f26])).
% 1.77/0.75  fof(f26,plain,(
% 1.77/0.75    v1_relat_1(sK1)),
% 1.77/0.75    inference(cnf_transformation,[],[f17])).
% 1.77/0.75  fof(f17,plain,(
% 1.77/0.75    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.77/0.75    inference(ennf_transformation,[],[f14])).
% 1.77/0.75  fof(f14,negated_conjecture,(
% 1.77/0.75    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.77/0.75    inference(negated_conjecture,[],[f13])).
% 1.77/0.75  fof(f13,conjecture,(
% 1.77/0.75    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 1.77/0.75  fof(f51,plain,(
% 1.77/0.75    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 1.77/0.75    inference(definition_unfolding,[],[f41,f34])).
% 1.77/0.75  fof(f41,plain,(
% 1.77/0.75    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 1.77/0.75    inference(cnf_transformation,[],[f23])).
% 1.77/0.75  fof(f23,plain,(
% 1.77/0.75    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.77/0.75    inference(ennf_transformation,[],[f12])).
% 1.77/0.75  fof(f12,axiom,(
% 1.77/0.75    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.77/0.75  fof(f895,plain,(
% 1.77/0.75    ( ! [X0] : (k7_relat_1(sK1,X0) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(k7_relat_1(sK1,X0)))))) )),
% 1.77/0.75    inference(resolution,[],[f146,f26])).
% 1.77/0.75  fof(f146,plain,(
% 1.77/0.75    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k1_setfam_1(k2_tarski(k7_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(X0,X1)),k2_relat_1(k7_relat_1(X0,X1)))))) )),
% 1.77/0.75    inference(resolution,[],[f47,f40])).
% 1.77/0.75  fof(f40,plain,(
% 1.77/0.75    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.77/0.75    inference(cnf_transformation,[],[f22])).
% 1.77/0.75  fof(f22,plain,(
% 1.77/0.75    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.77/0.75    inference(ennf_transformation,[],[f9])).
% 1.77/0.75  fof(f9,axiom,(
% 1.77/0.75    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.77/0.75  fof(f47,plain,(
% 1.77/0.75    ( ! [X0] : (~v1_relat_1(X0) | k1_setfam_1(k2_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) )),
% 1.77/0.75    inference(definition_unfolding,[],[f32,f34])).
% 1.77/0.75  fof(f32,plain,(
% 1.77/0.75    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 1.77/0.75    inference(cnf_transformation,[],[f19])).
% 1.77/0.75  fof(f19,plain,(
% 1.77/0.75    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.77/0.75    inference(ennf_transformation,[],[f10])).
% 1.77/0.75  fof(f10,axiom,(
% 1.77/0.75    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 1.77/0.75  fof(f766,plain,(
% 1.77/0.75    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k7_relat_1(k7_relat_1(sK1,k1_xboole_0),X0))) )),
% 1.77/0.75    inference(forward_demodulation,[],[f738,f80])).
% 1.77/0.75  fof(f80,plain,(
% 1.77/0.75    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) )),
% 1.77/0.75    inference(resolution,[],[f72,f52])).
% 1.77/0.75  fof(f52,plain,(
% 1.77/0.75    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.77/0.75    inference(definition_unfolding,[],[f43,f34])).
% 1.77/0.75  fof(f43,plain,(
% 1.77/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.77/0.75    inference(cnf_transformation,[],[f2])).
% 1.77/0.75  fof(f2,axiom,(
% 1.77/0.75    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.77/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.77/0.75  % (25189)Refutation not found, incomplete strategy% (25189)------------------------------
% 1.77/0.75  % (25189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.75  % (25189)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.75  
% 1.77/0.75  % (25189)Memory used [KB]: 10618
% 1.77/0.75  % (25189)Time elapsed: 0.172 s
% 1.77/0.75  % (25189)------------------------------
% 1.77/0.75  % (25189)------------------------------
% 1.77/0.75  fof(f72,plain,(
% 1.77/0.75    ( ! [X1] : (r1_xboole_0(k1_xboole_0,X1)) )),
% 1.77/0.75    inference(backward_demodulation,[],[f63,f67])).
% 1.77/0.75  fof(f738,plain,(
% 1.77/0.75    ( ! [X0] : (k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_relat_1(k7_relat_1(k7_relat_1(sK1,k1_xboole_0),X0))) )),
% 1.77/0.75    inference(superposition,[],[f706,f301])).
% 1.77/0.75  fof(f706,plain,(
% 1.77/0.75    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1)) = k1_setfam_1(k2_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X1))) )),
% 1.77/0.75    inference(resolution,[],[f297,f26])).
% 1.77/0.75  fof(f297,plain,(
% 1.77/0.75    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k1_setfam_1(k2_tarski(k1_relat_1(k7_relat_1(X1,X2)),X3))) )),
% 1.77/0.75    inference(resolution,[],[f51,f40])).
% 1.77/0.75  fof(f1236,plain,(
% 1.77/0.75    k1_xboole_0 != k1_relat_1(k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))),
% 1.77/0.75    inference(forward_demodulation,[],[f1231,f1214])).
% 1.77/0.75  fof(f1214,plain,(
% 1.77/0.75    k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.77/0.75    inference(duplicate_literal_removal,[],[f1213])).
% 1.77/0.75  fof(f1213,plain,(
% 1.77/0.75    k1_xboole_0 = k7_relat_1(sK1,sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.77/0.75    inference(forward_demodulation,[],[f1212,f67])).
% 1.77/0.75  fof(f1212,plain,(
% 1.77/0.75    k7_relat_1(sK1,sK0) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,sK0),k1_xboole_0)) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.77/0.75    inference(forward_demodulation,[],[f1196,f56])).
% 1.77/0.75  fof(f1196,plain,(
% 1.77/0.75    k7_relat_1(sK1,sK0) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,sK0))))) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.77/0.75    inference(superposition,[],[f895,f298])).
% 1.77/0.75  fof(f298,plain,(
% 1.77/0.75    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.77/0.75    inference(superposition,[],[f296,f78])).
% 1.77/0.75  fof(f78,plain,(
% 1.77/0.75    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.77/0.75    inference(resolution,[],[f52,f24])).
% 1.77/0.75  % (25190)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.77/0.75  fof(f24,plain,(
% 1.77/0.75    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.77/0.75    inference(cnf_transformation,[],[f17])).
% 1.77/0.75  fof(f1231,plain,(
% 1.77/0.75    k1_xboole_0 != k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(k7_relat_1(sK1,sK0))))),
% 1.77/0.75    inference(resolution,[],[f1216,f716])).
% 1.77/0.75  fof(f716,plain,(
% 1.77/0.75    ( ! [X0] : (r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 != k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))))) )),
% 1.77/0.75    inference(backward_demodulation,[],[f502,f706])).
% 1.77/0.75  fof(f502,plain,(
% 1.77/0.75    ( ! [X0] : (r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 != k1_setfam_1(k2_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0))))) )),
% 1.77/0.75    inference(resolution,[],[f491,f155])).
% 1.77/0.75  fof(f155,plain,(
% 1.77/0.75    ( ! [X4,X3] : (r1_xboole_0(X4,X3) | k1_xboole_0 != k1_setfam_1(k2_tarski(X3,X3))) )),
% 1.77/0.75    inference(resolution,[],[f141,f131])).
% 1.77/0.75  fof(f131,plain,(
% 1.77/0.75    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 1.77/0.75    inference(duplicate_literal_removal,[],[f130])).
% 1.77/0.75  fof(f130,plain,(
% 1.77/0.75    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 1.77/0.75    inference(resolution,[],[f58,f39])).
% 1.77/0.75  fof(f39,plain,(
% 1.77/0.75    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.77/0.75    inference(cnf_transformation,[],[f21])).
% 1.77/0.75  fof(f58,plain,(
% 1.77/0.75    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1),X2) | ~r1_xboole_0(X2,X0) | r1_xboole_0(X0,X1)) )),
% 1.77/0.75    inference(resolution,[],[f37,f38])).
% 1.77/0.75  fof(f37,plain,(
% 1.77/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.77/0.75    inference(cnf_transformation,[],[f21])).
% 1.77/0.75  fof(f141,plain,(
% 1.77/0.75    ( ! [X2,X1] : (r1_xboole_0(X1,X2) | k1_xboole_0 != k1_setfam_1(k2_tarski(X1,X1))) )),
% 1.77/0.75    inference(resolution,[],[f132,f53])).
% 1.77/0.75  fof(f53,plain,(
% 1.77/0.75    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.77/0.75    inference(definition_unfolding,[],[f42,f34])).
% 1.77/0.75  fof(f42,plain,(
% 1.77/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.77/0.75    inference(cnf_transformation,[],[f2])).
% 1.77/0.75  fof(f132,plain,(
% 1.77/0.75    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)) )),
% 1.77/0.75    inference(duplicate_literal_removal,[],[f129])).
% 1.77/0.75  fof(f129,plain,(
% 1.77/0.75    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) )),
% 1.77/0.75    inference(resolution,[],[f58,f38])).
% 1.77/0.75  fof(f491,plain,(
% 1.77/0.75    ( ! [X5] : (~r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X5)),k1_relat_1(k7_relat_1(sK1,X5))) | r1_xboole_0(k1_relat_1(sK1),X5)) )),
% 1.77/0.75    inference(forward_demodulation,[],[f486,f296])).
% 1.77/0.75  fof(f486,plain,(
% 1.77/0.75    ( ! [X5] : (r1_xboole_0(k1_relat_1(sK1),X5) | ~r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X5)),k1_setfam_1(k2_tarski(k1_relat_1(sK1),X5)))) )),
% 1.77/0.75    inference(duplicate_literal_removal,[],[f485])).
% 1.77/0.75  fof(f485,plain,(
% 1.77/0.75    ( ! [X5] : (r1_xboole_0(k1_relat_1(sK1),X5) | ~r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X5)),k1_setfam_1(k2_tarski(k1_relat_1(sK1),X5))) | r1_xboole_0(k1_relat_1(sK1),X5)) )),
% 1.77/0.75    inference(resolution,[],[f120,f306])).
% 1.77/0.75  fof(f306,plain,(
% 1.77/0.75    ( ! [X1] : (r2_hidden(sK2(k1_relat_1(sK1),X1),k1_relat_1(k7_relat_1(sK1,X1))) | r1_xboole_0(k1_relat_1(sK1),X1)) )),
% 1.77/0.75    inference(superposition,[],[f49,f296])).
% 1.77/0.75  fof(f49,plain,(
% 1.77/0.75    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 1.77/0.75    inference(definition_unfolding,[],[f36,f34])).
% 1.77/0.75  fof(f36,plain,(
% 1.77/0.75    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.77/0.75    inference(cnf_transformation,[],[f20])).
% 1.77/0.75  fof(f120,plain,(
% 1.77/0.75    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1),X2) | r1_xboole_0(X0,X1) | ~r1_xboole_0(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.77/0.75    inference(resolution,[],[f49,f37])).
% 1.77/0.75  fof(f1216,plain,(
% 1.77/0.75    ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 1.77/0.75    inference(trivial_inequality_removal,[],[f1215])).
% 1.77/0.75  fof(f1215,plain,(
% 1.77/0.75    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 1.77/0.75    inference(backward_demodulation,[],[f25,f1214])).
% 1.77/0.75  fof(f25,plain,(
% 1.77/0.75    k1_xboole_0 != k7_relat_1(sK1,sK0) | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 1.77/0.75    inference(cnf_transformation,[],[f17])).
% 1.77/0.75  % SZS output end Proof for theBenchmark
% 1.77/0.75  % (25178)------------------------------
% 1.77/0.75  % (25178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.75  % (25178)Termination reason: Refutation
% 1.77/0.75  
% 1.77/0.75  % (25178)Memory used [KB]: 6652
% 1.77/0.75  % (25178)Time elapsed: 0.174 s
% 1.77/0.75  % (25178)------------------------------
% 1.77/0.75  % (25178)------------------------------
% 1.77/0.76  % (25037)Success in time 0.393 s
%------------------------------------------------------------------------------
