%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:07 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 408 expanded)
%              Number of leaves         :   16 ( 113 expanded)
%              Depth                    :   16
%              Number of atoms          :  164 (1189 expanded)
%              Number of equality atoms :   83 ( 587 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f711,plain,(
    $false ),
    inference(global_subsumption,[],[f118,f710])).

fof(f710,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f707,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f32,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f707,plain,(
    ! [X0] : sK0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f93,f688,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sP7(sK6(X0,X1,X2),X1,X0)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f61,f63])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sP7(sK6(X0,X1,X2),X1,X0)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f688,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(backward_demodulation,[],[f327,f677])).

fof(f677,plain,(
    ! [X0] : sK4(k1_tarski(X0),sK0) = X0 ),
    inference(unit_resulting_resolution,[],[f324,f101])).

fof(f101,plain,(
    ! [X2,X1] :
      ( sK4(k1_tarski(X1),X2) = X1
      | r1_tarski(k1_tarski(X1),X2) ) ),
    inference(resolution,[],[f47,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f324,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(X0),sK0) ),
    inference(forward_demodulation,[],[f320,f174])).

fof(f174,plain,(
    ! [X0] : k1_tarski(X0) = k2_relat_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f115,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f115,plain,(
    k1_xboole_0 != sK1 ),
    inference(unit_resulting_resolution,[],[f31,f113,f83])).

fof(f83,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(global_subsumption,[],[f76,f82])).

fof(f82,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | k1_xboole_0 != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f80,f29])).

fof(f29,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f80,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),sK0) ),
    inference(superposition,[],[f25,f28])).

fof(f28,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f30,f27])).

fof(f27,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f113,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f41,f106])).

fof(f106,plain,(
    k1_xboole_0 = sK3(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f40,f42,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f42,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f40,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f320,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f119,f120,f127,f25])).

fof(f127,plain,(
    ! [X0] : sK1 = k1_relat_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f115,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f120,plain,(
    ! [X0] : v1_relat_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f115,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f119,plain,(
    ! [X0] : v1_funct_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f115,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f327,plain,(
    ! [X0] : ~ r2_hidden(sK4(k1_tarski(X0),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f324,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f93,plain,(
    ! [X0,X1] : ~ sP7(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f77,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f77,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f43,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f118,plain,(
    k1_xboole_0 != sK0 ),
    inference(unit_resulting_resolution,[],[f115,f26])).

fof(f26,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:14:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.46  % (4416)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.46  % (4424)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.22/0.52  % (4402)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.22/0.52  % (4408)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.22/0.53  % (4403)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.53  % (4401)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.22/0.53  % (4404)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.22/0.53  % (4401)Refutation not found, incomplete strategy% (4401)------------------------------
% 1.22/0.53  % (4401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (4401)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (4401)Memory used [KB]: 1663
% 1.22/0.53  % (4401)Time elapsed: 0.122 s
% 1.22/0.53  % (4401)------------------------------
% 1.22/0.53  % (4401)------------------------------
% 1.38/0.53  % (4403)Refutation not found, incomplete strategy% (4403)------------------------------
% 1.38/0.53  % (4403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (4403)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (4403)Memory used [KB]: 10746
% 1.38/0.53  % (4403)Time elapsed: 0.125 s
% 1.38/0.53  % (4403)------------------------------
% 1.38/0.53  % (4403)------------------------------
% 1.38/0.53  % (4413)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.53  % (4411)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.53  % (4412)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.53  % (4426)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.53  % (4411)Refutation not found, incomplete strategy% (4411)------------------------------
% 1.38/0.53  % (4411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (4411)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (4411)Memory used [KB]: 10618
% 1.38/0.53  % (4411)Time elapsed: 0.132 s
% 1.38/0.53  % (4411)------------------------------
% 1.38/0.53  % (4411)------------------------------
% 1.38/0.53  % (4429)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.53  % (4423)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.53  % (4405)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.38/0.54  % (4418)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.54  % (4406)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.38/0.54  % (4427)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.54  % (4423)Refutation not found, incomplete strategy% (4423)------------------------------
% 1.38/0.54  % (4423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (4423)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (4423)Memory used [KB]: 10746
% 1.38/0.54  % (4423)Time elapsed: 0.095 s
% 1.38/0.54  % (4423)------------------------------
% 1.38/0.54  % (4423)------------------------------
% 1.38/0.54  % (4417)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.54  % (4418)Refutation not found, incomplete strategy% (4418)------------------------------
% 1.38/0.54  % (4418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (4418)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (4418)Memory used [KB]: 10618
% 1.38/0.54  % (4418)Time elapsed: 0.142 s
% 1.38/0.54  % (4418)------------------------------
% 1.38/0.54  % (4418)------------------------------
% 1.38/0.54  % (4409)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.54  % (4415)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.54  % (4410)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.54  % (4410)Refutation not found, incomplete strategy% (4410)------------------------------
% 1.38/0.54  % (4410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (4410)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (4410)Memory used [KB]: 10618
% 1.38/0.54  % (4410)Time elapsed: 0.151 s
% 1.38/0.54  % (4410)------------------------------
% 1.38/0.54  % (4410)------------------------------
% 1.38/0.54  % (4420)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.54  % (4419)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.54  % (4409)Refutation not found, incomplete strategy% (4409)------------------------------
% 1.38/0.54  % (4409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (4421)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.54  % (4409)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (4409)Memory used [KB]: 10746
% 1.38/0.54  % (4409)Time elapsed: 0.145 s
% 1.38/0.54  % (4409)------------------------------
% 1.38/0.54  % (4409)------------------------------
% 1.38/0.55  % (4428)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.55  % (4422)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.55  % (4407)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.55  % (4425)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.55  % (4430)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.56  % (4414)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.58  % (4425)Refutation found. Thanks to Tanya!
% 1.38/0.58  % SZS status Theorem for theBenchmark
% 1.38/0.58  % SZS output start Proof for theBenchmark
% 1.38/0.58  fof(f711,plain,(
% 1.38/0.58    $false),
% 1.38/0.58    inference(global_subsumption,[],[f118,f710])).
% 1.38/0.58  fof(f710,plain,(
% 1.38/0.58    k1_xboole_0 = sK0),
% 1.38/0.58    inference(forward_demodulation,[],[f707,f64])).
% 1.38/0.58  fof(f64,plain,(
% 1.38/0.58    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) )),
% 1.38/0.58    inference(definition_unfolding,[],[f32,f63])).
% 1.38/0.58  fof(f63,plain,(
% 1.38/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.38/0.58    inference(definition_unfolding,[],[f44,f45])).
% 1.38/0.58  fof(f45,plain,(
% 1.38/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f6])).
% 1.38/0.58  fof(f6,axiom,(
% 1.38/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.38/0.58  fof(f44,plain,(
% 1.38/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.38/0.58    inference(cnf_transformation,[],[f9])).
% 1.38/0.58  fof(f9,axiom,(
% 1.38/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.38/0.58  fof(f32,plain,(
% 1.38/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f3])).
% 1.38/0.58  fof(f3,axiom,(
% 1.38/0.58    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.38/0.58  fof(f707,plain,(
% 1.38/0.58    ( ! [X0] : (sK0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) )),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f93,f688,f66])).
% 1.38/0.58  fof(f66,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (sP7(sK6(X0,X1,X2),X1,X0) | r2_hidden(sK6(X0,X1,X2),X2) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2) )),
% 1.38/0.58    inference(definition_unfolding,[],[f61,f63])).
% 1.38/0.58  fof(f61,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (sP7(sK6(X0,X1,X2),X1,X0) | r2_hidden(sK6(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.38/0.58    inference(cnf_transformation,[],[f2])).
% 1.38/0.58  fof(f2,axiom,(
% 1.38/0.58    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.38/0.58  fof(f688,plain,(
% 1.38/0.58    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 1.38/0.58    inference(backward_demodulation,[],[f327,f677])).
% 1.38/0.58  fof(f677,plain,(
% 1.38/0.58    ( ! [X0] : (sK4(k1_tarski(X0),sK0) = X0) )),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f324,f101])).
% 1.38/0.58  fof(f101,plain,(
% 1.38/0.58    ( ! [X2,X1] : (sK4(k1_tarski(X1),X2) = X1 | r1_tarski(k1_tarski(X1),X2)) )),
% 1.38/0.58    inference(resolution,[],[f47,f69])).
% 1.38/0.58  fof(f69,plain,(
% 1.38/0.58    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.38/0.58    inference(equality_resolution,[],[f50])).
% 1.38/0.58  fof(f50,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.38/0.58    inference(cnf_transformation,[],[f5])).
% 1.38/0.58  fof(f5,axiom,(
% 1.38/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.38/0.58  fof(f47,plain,(
% 1.38/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f24])).
% 1.38/0.58  fof(f24,plain,(
% 1.38/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.38/0.58    inference(ennf_transformation,[],[f1])).
% 1.38/0.58  fof(f1,axiom,(
% 1.38/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.38/0.58  fof(f324,plain,(
% 1.38/0.58    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK0)) )),
% 1.38/0.58    inference(forward_demodulation,[],[f320,f174])).
% 1.38/0.58  fof(f174,plain,(
% 1.38/0.58    ( ! [X0] : (k1_tarski(X0) = k2_relat_1(sK2(sK1,X0))) )),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f115,f38])).
% 1.38/0.58  fof(f38,plain,(
% 1.38/0.58    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.38/0.58    inference(cnf_transformation,[],[f22])).
% 1.38/0.58  fof(f22,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.38/0.58    inference(ennf_transformation,[],[f15])).
% 1.38/0.58  fof(f15,axiom,(
% 1.38/0.58    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).
% 1.38/0.58  fof(f115,plain,(
% 1.38/0.58    k1_xboole_0 != sK1),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f31,f113,f83])).
% 1.38/0.58  fof(f83,plain,(
% 1.38/0.58    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0)),
% 1.38/0.58    inference(global_subsumption,[],[f76,f82])).
% 1.38/0.58  fof(f82,plain,(
% 1.38/0.58    ~r1_tarski(k1_xboole_0,sK0) | k1_xboole_0 != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.38/0.58    inference(forward_demodulation,[],[f80,f29])).
% 1.38/0.58  fof(f29,plain,(
% 1.38/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.38/0.58    inference(cnf_transformation,[],[f11])).
% 1.38/0.58  fof(f11,axiom,(
% 1.38/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.38/0.58  fof(f80,plain,(
% 1.38/0.58    k1_xboole_0 != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),sK0)),
% 1.38/0.58    inference(superposition,[],[f25,f28])).
% 1.38/0.58  fof(f28,plain,(
% 1.38/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.38/0.58    inference(cnf_transformation,[],[f11])).
% 1.38/0.58  fof(f25,plain,(
% 1.38/0.58    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),sK0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f19])).
% 1.38/0.58  fof(f19,plain,(
% 1.38/0.58    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.38/0.58    inference(flattening,[],[f18])).
% 1.38/0.58  fof(f18,plain,(
% 1.38/0.58    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.38/0.58    inference(ennf_transformation,[],[f17])).
% 1.38/0.58  fof(f17,negated_conjecture,(
% 1.38/0.58    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.38/0.58    inference(negated_conjecture,[],[f16])).
% 1.38/0.58  fof(f16,conjecture,(
% 1.38/0.58    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 1.38/0.58  fof(f76,plain,(
% 1.38/0.58    v1_relat_1(k1_xboole_0)),
% 1.38/0.58    inference(superposition,[],[f30,f27])).
% 1.38/0.58  fof(f27,plain,(
% 1.38/0.58    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.38/0.58    inference(cnf_transformation,[],[f13])).
% 1.38/0.58  fof(f13,axiom,(
% 1.38/0.58    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 1.38/0.58  fof(f30,plain,(
% 1.38/0.58    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.38/0.58    inference(cnf_transformation,[],[f10])).
% 1.38/0.58  fof(f10,axiom,(
% 1.38/0.58    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.38/0.58  fof(f113,plain,(
% 1.38/0.58    v1_funct_1(k1_xboole_0)),
% 1.38/0.58    inference(superposition,[],[f41,f106])).
% 1.38/0.58  fof(f106,plain,(
% 1.38/0.58    k1_xboole_0 = sK3(k1_xboole_0)),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f40,f42,f33])).
% 1.38/0.58  fof(f33,plain,(
% 1.38/0.58    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.38/0.58    inference(cnf_transformation,[],[f21])).
% 1.38/0.58  fof(f21,plain,(
% 1.38/0.58    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.38/0.58    inference(flattening,[],[f20])).
% 1.38/0.58  fof(f20,plain,(
% 1.38/0.58    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.38/0.58    inference(ennf_transformation,[],[f12])).
% 1.38/0.58  fof(f12,axiom,(
% 1.38/0.58    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.38/0.58  fof(f42,plain,(
% 1.38/0.58    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 1.38/0.58    inference(cnf_transformation,[],[f23])).
% 1.38/0.58  fof(f23,plain,(
% 1.38/0.58    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.38/0.58    inference(ennf_transformation,[],[f14])).
% 1.38/0.58  fof(f14,axiom,(
% 1.38/0.58    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.38/0.58  fof(f40,plain,(
% 1.38/0.58    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 1.38/0.58    inference(cnf_transformation,[],[f23])).
% 1.38/0.58  fof(f41,plain,(
% 1.38/0.58    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 1.38/0.58    inference(cnf_transformation,[],[f23])).
% 1.38/0.58  fof(f31,plain,(
% 1.38/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f4])).
% 1.38/0.58  fof(f4,axiom,(
% 1.38/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.38/0.58  fof(f320,plain,(
% 1.38/0.58    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)) )),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f119,f120,f127,f25])).
% 1.38/0.58  fof(f127,plain,(
% 1.38/0.58    ( ! [X0] : (sK1 = k1_relat_1(sK2(sK1,X0))) )),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f115,f37])).
% 1.38/0.58  fof(f37,plain,(
% 1.38/0.58    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.38/0.58    inference(cnf_transformation,[],[f22])).
% 1.38/0.58  fof(f120,plain,(
% 1.38/0.58    ( ! [X0] : (v1_relat_1(sK2(sK1,X0))) )),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f115,f35])).
% 1.38/0.58  fof(f35,plain,(
% 1.38/0.58    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.38/0.58    inference(cnf_transformation,[],[f22])).
% 1.38/0.58  fof(f119,plain,(
% 1.38/0.58    ( ! [X0] : (v1_funct_1(sK2(sK1,X0))) )),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f115,f36])).
% 1.38/0.58  fof(f36,plain,(
% 1.38/0.58    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.38/0.58    inference(cnf_transformation,[],[f22])).
% 1.38/0.58  fof(f327,plain,(
% 1.38/0.58    ( ! [X0] : (~r2_hidden(sK4(k1_tarski(X0),sK0),sK0)) )),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f324,f48])).
% 1.38/0.58  fof(f48,plain,(
% 1.38/0.58    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f24])).
% 1.38/0.58  fof(f93,plain,(
% 1.38/0.58    ( ! [X0,X1] : (~sP7(X0,k1_xboole_0,X1)) )),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f77,f58])).
% 1.38/0.58  fof(f58,plain,(
% 1.38/0.58    ( ! [X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f2])).
% 1.38/0.58  fof(f77,plain,(
% 1.38/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.38/0.58    inference(superposition,[],[f43,f72])).
% 1.38/0.58  fof(f72,plain,(
% 1.38/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.38/0.58    inference(equality_resolution,[],[f55])).
% 1.38/0.58  fof(f55,plain,(
% 1.38/0.58    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f7])).
% 1.38/0.58  fof(f7,axiom,(
% 1.38/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.38/0.58  fof(f43,plain,(
% 1.38/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.38/0.58    inference(cnf_transformation,[],[f8])).
% 1.38/0.58  fof(f8,axiom,(
% 1.38/0.58    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.38/0.58  fof(f118,plain,(
% 1.38/0.58    k1_xboole_0 != sK0),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f115,f26])).
% 1.38/0.58  fof(f26,plain,(
% 1.38/0.58    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.38/0.58    inference(cnf_transformation,[],[f19])).
% 1.38/0.58  % SZS output end Proof for theBenchmark
% 1.38/0.58  % (4425)------------------------------
% 1.38/0.58  % (4425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (4425)Termination reason: Refutation
% 1.38/0.58  
% 1.38/0.58  % (4425)Memory used [KB]: 7164
% 1.38/0.58  % (4425)Time elapsed: 0.177 s
% 1.38/0.58  % (4425)------------------------------
% 1.38/0.58  % (4425)------------------------------
% 1.38/0.58  % (4400)Success in time 0.23 s
%------------------------------------------------------------------------------
