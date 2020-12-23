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
% DateTime   : Thu Dec  3 12:50:27 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   78 (3311 expanded)
%              Number of leaves         :   10 ( 903 expanded)
%              Depth                    :   26
%              Number of atoms          :  155 (7911 expanded)
%              Number of equality atoms :   45 (2113 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f552,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f509,f500,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK8(X0,X2),X2),X0)
      | ~ sP7(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f500,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(X0,sK5(k2_relat_1(sK1),sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f453,f494,f25])).

fof(f25,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f494,plain,(
    r2_hidden(sK5(k2_relat_1(sK1),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f473,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ sP11(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f473,plain,(
    sP11(sK5(k2_relat_1(sK1),sK0),sK0,k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f455,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))
      | sP11(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( sP11(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f56,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( sP11(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f455,plain,(
    r2_hidden(sK5(k2_relat_1(sK1),sK0),k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))) ),
    inference(unit_resulting_resolution,[],[f449,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f449,plain,(
    ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f448])).

fof(f448,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f444])).

fof(f444,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(superposition,[],[f21,f439])).

fof(f439,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(sK1,X0)
      | ~ r1_xboole_0(k2_relat_1(sK1),X0) ) ),
    inference(forward_demodulation,[],[f436,f370])).

fof(f370,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f354,f369])).

fof(f369,plain,(
    k1_xboole_0 = k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f368,f354])).

fof(f368,plain,(
    k1_xboole_0 = k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f319,f354])).

fof(f319,plain,(
    k1_xboole_0 = k2_relat_1(k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f77,f279,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sP7(sK6(X0,X1),X0)
      | r2_hidden(sK6(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f279,plain,(
    ! [X0] : ~ sP7(X0,k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f234,f39])).

fof(f234,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f223,f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP7(X2,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP7(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f223,plain,(
    ! [X0] : ~ sP7(X0,k2_relat_1(k10_relat_1(sK1,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f207,f39])).

fof(f207,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k10_relat_1(sK1,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f202,f70])).

fof(f202,plain,(
    ! [X0] : ~ sP7(X0,k10_relat_1(sK1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f196,f39])).

fof(f196,plain,(
    ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f22,f98,f68])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f98,plain,(
    ! [X0,X1] : ~ sP3(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f77,f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X1)
      | ~ sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f77,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f32,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f32,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f354,plain,(
    k10_relat_1(sK1,k1_xboole_0) = k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f331,f353])).

fof(f353,plain,(
    k10_relat_1(sK1,k1_xboole_0) = k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f320,f331])).

fof(f320,plain,(
    k10_relat_1(sK1,k1_xboole_0) = k2_relat_1(k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f196,f279,f43])).

fof(f331,plain,(
    k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) = k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f323,f322])).

fof(f322,plain,(
    k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) = k2_relat_1(k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f207,f279,f43])).

fof(f323,plain,(
    k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0))) = k2_relat_1(k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f234,f279,f43])).

fof(f436,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,k1_xboole_0) = k10_relat_1(sK1,X0)
      | ~ r1_xboole_0(k2_relat_1(sK1),X0) ) ),
    inference(superposition,[],[f288,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f33])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f288,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0))) ),
    inference(unit_resulting_resolution,[],[f22,f61])).

fof(f61,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f21,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f453,plain,(
    ! [X0] : ~ sP3(X0,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f449,f216])).

fof(f216,plain,(
    ! [X0] :
      ( ~ sP3(X0,sK0,sK1)
      | r1_xboole_0(k2_relat_1(sK1),sK0) ) ),
    inference(global_subsumption,[],[f22,f77,f214])).

fof(f214,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ sP3(X0,sK0,sK1)
      | ~ v1_relat_1(sK1)
      | r1_xboole_0(k2_relat_1(sK1),sK0) ) ),
    inference(superposition,[],[f69,f20])).

fof(f20,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f509,plain,(
    sP7(sK5(k2_relat_1(sK1),sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f495,f70])).

fof(f495,plain,(
    r2_hidden(sK5(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f473,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ sP11(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:33:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (28369)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (28386)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.42/0.55  % (28378)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.56  % (28370)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.42/0.57  % (28391)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.57  % (28377)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.64/0.58  % (28367)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.64/0.59  % (28368)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.64/0.59  % (28365)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.64/0.60  % (28363)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.64/0.60  % (28385)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.64/0.60  % (28366)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.64/0.60  % (28390)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.64/0.60  % (28374)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.64/0.61  % (28374)Refutation not found, incomplete strategy% (28374)------------------------------
% 1.64/0.61  % (28374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.61  % (28374)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.61  
% 1.64/0.61  % (28374)Memory used [KB]: 10618
% 1.64/0.61  % (28374)Time elapsed: 0.180 s
% 1.64/0.61  % (28374)------------------------------
% 1.64/0.61  % (28374)------------------------------
% 1.64/0.61  % (28364)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.64/0.61  % (28373)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.64/0.61  % (28383)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.64/0.61  % (28373)Refutation not found, incomplete strategy% (28373)------------------------------
% 1.64/0.61  % (28373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.61  % (28373)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.61  
% 1.64/0.61  % (28373)Memory used [KB]: 10618
% 1.64/0.61  % (28373)Time elapsed: 0.180 s
% 1.64/0.61  % (28373)------------------------------
% 1.64/0.61  % (28373)------------------------------
% 1.64/0.61  % (28389)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.64/0.61  % (28376)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.64/0.62  % (28387)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.64/0.62  % (28382)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.64/0.62  % (28375)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.64/0.62  % (28380)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.64/0.62  % (28381)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.64/0.62  % (28392)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.64/0.63  % (28385)Refutation not found, incomplete strategy% (28385)------------------------------
% 1.64/0.63  % (28385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.63  % (28385)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.63  
% 1.64/0.63  % (28385)Memory used [KB]: 10746
% 1.64/0.63  % (28385)Time elapsed: 0.202 s
% 1.64/0.63  % (28385)------------------------------
% 1.64/0.63  % (28385)------------------------------
% 1.64/0.63  % (28384)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.64/0.63  % (28379)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.64/0.63  % (28371)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.64/0.63  % (28372)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.64/0.64  % (28388)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.64/0.65  % (28387)Refutation found. Thanks to Tanya!
% 1.64/0.65  % SZS status Theorem for theBenchmark
% 2.19/0.66  % SZS output start Proof for theBenchmark
% 2.19/0.66  fof(f552,plain,(
% 2.19/0.66    $false),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f509,f500,f39])).
% 2.19/0.66  fof(f39,plain,(
% 2.19/0.66    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK8(X0,X2),X2),X0) | ~sP7(X2,X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f8])).
% 2.19/0.66  fof(f8,axiom,(
% 2.19/0.66    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 2.19/0.66  fof(f500,plain,(
% 2.19/0.66    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK5(k2_relat_1(sK1),sK0)),sK1)) )),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f453,f494,f25])).
% 2.19/0.66  fof(f25,plain,(
% 2.19/0.66    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | sP3(X3,X1,X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f16])).
% 2.19/0.66  fof(f16,plain,(
% 2.19/0.66    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 2.19/0.66    inference(ennf_transformation,[],[f7])).
% 2.19/0.66  fof(f7,axiom,(
% 2.19/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
% 2.19/0.66  fof(f494,plain,(
% 2.19/0.66    r2_hidden(sK5(k2_relat_1(sK1),sK0),sK0)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f473,f54])).
% 2.19/0.66  fof(f54,plain,(
% 2.19/0.66    ( ! [X0,X3,X1] : (~sP11(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f1])).
% 2.19/0.66  fof(f1,axiom,(
% 2.19/0.66    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.19/0.66  fof(f473,plain,(
% 2.19/0.66    sP11(sK5(k2_relat_1(sK1),sK0),sK0,k2_relat_1(sK1))),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f455,f74])).
% 2.19/0.66  fof(f74,plain,(
% 2.19/0.66    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) | sP11(X3,X1,X0)) )),
% 2.19/0.66    inference(equality_resolution,[],[f66])).
% 2.19/0.66  fof(f66,plain,(
% 2.19/0.66    ( ! [X2,X0,X3,X1] : (sP11(X3,X1,X0) | ~r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 2.19/0.66    inference(definition_unfolding,[],[f56,f33])).
% 2.19/0.66  fof(f33,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.19/0.66    inference(cnf_transformation,[],[f6])).
% 2.19/0.66  fof(f6,axiom,(
% 2.19/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.19/0.66  fof(f56,plain,(
% 2.19/0.66    ( ! [X2,X0,X3,X1] : (sP11(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.19/0.66    inference(cnf_transformation,[],[f1])).
% 2.19/0.66  fof(f455,plain,(
% 2.19/0.66    r2_hidden(sK5(k2_relat_1(sK1),sK0),k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)))),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f449,f59])).
% 2.19/0.66  fof(f59,plain,(
% 2.19/0.66    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 2.19/0.66    inference(definition_unfolding,[],[f35,f33])).
% 2.19/0.66  fof(f35,plain,(
% 2.19/0.66    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.19/0.66    inference(cnf_transformation,[],[f17])).
% 2.19/0.66  fof(f17,plain,(
% 2.19/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.19/0.66    inference(ennf_transformation,[],[f14])).
% 2.19/0.66  fof(f14,plain,(
% 2.19/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.19/0.66    inference(rectify,[],[f3])).
% 2.19/0.66  fof(f3,axiom,(
% 2.19/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.19/0.66  fof(f449,plain,(
% 2.19/0.66    ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 2.19/0.66    inference(trivial_inequality_removal,[],[f448])).
% 2.19/0.66  fof(f448,plain,(
% 2.19/0.66    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 2.19/0.66    inference(duplicate_literal_removal,[],[f444])).
% 2.19/0.66  fof(f444,plain,(
% 2.19/0.66    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),sK0) | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 2.19/0.66    inference(superposition,[],[f21,f439])).
% 2.19/0.66  fof(f439,plain,(
% 2.19/0.66    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK1,X0) | ~r1_xboole_0(k2_relat_1(sK1),X0)) )),
% 2.19/0.66    inference(forward_demodulation,[],[f436,f370])).
% 2.19/0.66  fof(f370,plain,(
% 2.19/0.66    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 2.19/0.66    inference(backward_demodulation,[],[f354,f369])).
% 2.19/0.66  fof(f369,plain,(
% 2.19/0.66    k1_xboole_0 = k2_relat_1(k10_relat_1(sK1,k1_xboole_0))),
% 2.19/0.66    inference(forward_demodulation,[],[f368,f354])).
% 2.19/0.66  fof(f368,plain,(
% 2.19/0.66    k1_xboole_0 = k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0)))),
% 2.19/0.66    inference(forward_demodulation,[],[f319,f354])).
% 2.19/0.66  fof(f319,plain,(
% 2.19/0.66    k1_xboole_0 = k2_relat_1(k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0))))),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f77,f279,f43])).
% 2.19/0.66  fof(f43,plain,(
% 2.19/0.66    ( ! [X0,X1] : (sP7(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 2.19/0.66    inference(cnf_transformation,[],[f8])).
% 2.19/0.66  fof(f279,plain,(
% 2.19/0.66    ( ! [X0] : (~sP7(X0,k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0))))) )),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f234,f39])).
% 2.19/0.66  fof(f234,plain,(
% 2.19/0.66    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0))))) )),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f223,f70])).
% 2.19/0.66  fof(f70,plain,(
% 2.19/0.66    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | sP7(X2,X0)) )),
% 2.19/0.66    inference(equality_resolution,[],[f42])).
% 2.19/0.66  fof(f42,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (sP7(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 2.19/0.66    inference(cnf_transformation,[],[f8])).
% 2.19/0.66  fof(f223,plain,(
% 2.19/0.66    ( ! [X0] : (~sP7(X0,k2_relat_1(k10_relat_1(sK1,k1_xboole_0)))) )),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f207,f39])).
% 2.19/0.66  fof(f207,plain,(
% 2.19/0.66    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k10_relat_1(sK1,k1_xboole_0)))) )),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f202,f70])).
% 2.19/0.66  fof(f202,plain,(
% 2.19/0.66    ( ! [X0] : (~sP7(X0,k10_relat_1(sK1,k1_xboole_0))) )),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f196,f39])).
% 2.19/0.66  fof(f196,plain,(
% 2.19/0.66    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,k1_xboole_0))) )),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f22,f98,f68])).
% 2.19/0.66  fof(f68,plain,(
% 2.19/0.66    ( ! [X0,X3,X1] : (~r2_hidden(X3,k10_relat_1(X0,X1)) | sP3(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 2.19/0.66    inference(equality_resolution,[],[f29])).
% 2.19/0.66  fof(f29,plain,(
% 2.19/0.66    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 2.19/0.66    inference(cnf_transformation,[],[f16])).
% 2.19/0.66  fof(f98,plain,(
% 2.19/0.66    ( ! [X0,X1] : (~sP3(X0,k1_xboole_0,X1)) )),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f77,f27])).
% 2.19/0.66  fof(f27,plain,(
% 2.19/0.66    ( ! [X0,X3,X1] : (r2_hidden(sK4(X0,X1,X3),X1) | ~sP3(X3,X1,X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f16])).
% 2.19/0.66  fof(f22,plain,(
% 2.19/0.66    v1_relat_1(sK1)),
% 2.19/0.66    inference(cnf_transformation,[],[f15])).
% 2.19/0.66  fof(f15,plain,(
% 2.19/0.66    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 2.19/0.66    inference(ennf_transformation,[],[f13])).
% 2.19/0.66  fof(f13,negated_conjecture,(
% 2.19/0.66    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 2.19/0.66    inference(negated_conjecture,[],[f12])).
% 2.19/0.66  fof(f12,conjecture,(
% 2.19/0.66    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 2.19/0.66  fof(f77,plain,(
% 2.19/0.66    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.19/0.66    inference(superposition,[],[f32,f72])).
% 2.19/0.66  fof(f72,plain,(
% 2.19/0.66    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.19/0.66    inference(equality_resolution,[],[f47])).
% 2.19/0.66  fof(f47,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f4])).
% 2.19/0.66  fof(f4,axiom,(
% 2.19/0.66    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.19/0.66  fof(f32,plain,(
% 2.19/0.66    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.19/0.66    inference(cnf_transformation,[],[f5])).
% 2.19/0.66  fof(f5,axiom,(
% 2.19/0.66    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 2.19/0.66  fof(f354,plain,(
% 2.19/0.66    k10_relat_1(sK1,k1_xboole_0) = k2_relat_1(k10_relat_1(sK1,k1_xboole_0))),
% 2.19/0.66    inference(backward_demodulation,[],[f331,f353])).
% 2.19/0.66  fof(f353,plain,(
% 2.19/0.66    k10_relat_1(sK1,k1_xboole_0) = k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0)))),
% 2.19/0.66    inference(forward_demodulation,[],[f320,f331])).
% 2.19/0.66  fof(f320,plain,(
% 2.19/0.66    k10_relat_1(sK1,k1_xboole_0) = k2_relat_1(k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0))))),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f196,f279,f43])).
% 2.19/0.66  fof(f331,plain,(
% 2.19/0.66    k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) = k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0)))),
% 2.19/0.66    inference(backward_demodulation,[],[f323,f322])).
% 2.19/0.66  fof(f322,plain,(
% 2.19/0.66    k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) = k2_relat_1(k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0))))),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f207,f279,f43])).
% 2.19/0.66  fof(f323,plain,(
% 2.19/0.66    k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0))) = k2_relat_1(k2_relat_1(k2_relat_1(k10_relat_1(sK1,k1_xboole_0))))),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f234,f279,f43])).
% 2.19/0.66  fof(f436,plain,(
% 2.19/0.66    ( ! [X0] : (k10_relat_1(sK1,k1_xboole_0) = k10_relat_1(sK1,X0) | ~r1_xboole_0(k2_relat_1(sK1),X0)) )),
% 2.19/0.66    inference(superposition,[],[f288,f62])).
% 2.19/0.66  fof(f62,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.19/0.66    inference(definition_unfolding,[],[f38,f33])).
% 2.19/0.66  fof(f38,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f2])).
% 2.19/0.66  fof(f2,axiom,(
% 2.19/0.66    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.19/0.66  fof(f288,plain,(
% 2.19/0.66    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0)))) )),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f22,f61])).
% 2.19/0.66  fof(f61,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 2.19/0.66    inference(definition_unfolding,[],[f36,f33])).
% 2.19/0.66  fof(f36,plain,(
% 2.19/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 2.19/0.66    inference(cnf_transformation,[],[f18])).
% 2.19/0.66  fof(f18,plain,(
% 2.19/0.66    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.19/0.66    inference(ennf_transformation,[],[f10])).
% 2.19/0.66  fof(f10,axiom,(
% 2.19/0.66    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 2.19/0.66  fof(f21,plain,(
% 2.19/0.66    k1_xboole_0 != k10_relat_1(sK1,sK0) | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 2.19/0.66    inference(cnf_transformation,[],[f15])).
% 2.19/0.66  fof(f453,plain,(
% 2.19/0.66    ( ! [X0] : (~sP3(X0,sK0,sK1)) )),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f449,f216])).
% 2.19/0.66  fof(f216,plain,(
% 2.19/0.66    ( ! [X0] : (~sP3(X0,sK0,sK1) | r1_xboole_0(k2_relat_1(sK1),sK0)) )),
% 2.19/0.66    inference(global_subsumption,[],[f22,f77,f214])).
% 2.19/0.66  fof(f214,plain,(
% 2.19/0.66    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~sP3(X0,sK0,sK1) | ~v1_relat_1(sK1) | r1_xboole_0(k2_relat_1(sK1),sK0)) )),
% 2.19/0.66    inference(superposition,[],[f69,f20])).
% 2.19/0.66  fof(f20,plain,(
% 2.19/0.66    k1_xboole_0 = k10_relat_1(sK1,sK0) | r1_xboole_0(k2_relat_1(sK1),sK0)),
% 2.19/0.66    inference(cnf_transformation,[],[f15])).
% 2.19/0.66  fof(f69,plain,(
% 2.19/0.66    ( ! [X0,X3,X1] : (r2_hidden(X3,k10_relat_1(X0,X1)) | ~sP3(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 2.19/0.66    inference(equality_resolution,[],[f28])).
% 2.19/0.67  fof(f28,plain,(
% 2.19/0.67    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 2.19/0.67    inference(cnf_transformation,[],[f16])).
% 2.19/0.67  fof(f509,plain,(
% 2.19/0.67    sP7(sK5(k2_relat_1(sK1),sK0),sK1)),
% 2.19/0.67    inference(unit_resulting_resolution,[],[f495,f70])).
% 2.19/0.67  fof(f495,plain,(
% 2.19/0.67    r2_hidden(sK5(k2_relat_1(sK1),sK0),k2_relat_1(sK1))),
% 2.19/0.67    inference(unit_resulting_resolution,[],[f473,f53])).
% 2.19/0.67  fof(f53,plain,(
% 2.19/0.67    ( ! [X0,X3,X1] : (~sP11(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f1])).
% 2.19/0.67  % SZS output end Proof for theBenchmark
% 2.19/0.67  % (28387)------------------------------
% 2.19/0.67  % (28387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.67  % (28387)Termination reason: Refutation
% 2.19/0.67  
% 2.19/0.67  % (28387)Memory used [KB]: 6652
% 2.19/0.67  % (28387)Time elapsed: 0.224 s
% 2.19/0.67  % (28387)------------------------------
% 2.19/0.67  % (28387)------------------------------
% 2.19/0.67  % (28362)Success in time 0.3 s
%------------------------------------------------------------------------------
