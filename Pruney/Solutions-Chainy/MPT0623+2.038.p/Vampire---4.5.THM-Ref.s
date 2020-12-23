%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:08 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 417 expanded)
%              Number of leaves         :   10 ( 108 expanded)
%              Depth                    :   16
%              Number of atoms          :  180 (1307 expanded)
%              Number of equality atoms :   72 ( 539 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f336,plain,(
    $false ),
    inference(global_subsumption,[],[f184,f335])).

fof(f335,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f329,f24])).

fof(f24,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f329,plain,(
    k2_relat_1(k1_xboole_0) = sK0 ),
    inference(unit_resulting_resolution,[],[f141,f310,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sP8(sK7(X0,X1),X0)
      | r2_hidden(sK7(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f310,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(backward_demodulation,[],[f222,f295])).

fof(f295,plain,(
    ! [X0] : sK5(k1_tarski(X0),sK0) = X0 ),
    inference(unit_resulting_resolution,[],[f223,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f223,plain,(
    ! [X0] : r2_hidden(sK5(k1_tarski(X0),sK0),k1_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f196,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
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

fof(f196,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(X0),sK0) ),
    inference(backward_demodulation,[],[f183,f190])).

fof(f190,plain,(
    ! [X0] : k1_tarski(X0) = k2_relat_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f180,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f180,plain,(
    k1_xboole_0 != sK1 ),
    inference(unit_resulting_resolution,[],[f97,f96,f144,f60])).

fof(f60,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f58,f24])).

fof(f58,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),sK0) ),
    inference(superposition,[],[f21,f23])).

fof(f23,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f144,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f138,f40])).

fof(f138,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f90,f25,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f25,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f90,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_relat_1(k1_tarski(k4_tarski(X1,X0)))) ),
    inference(unit_resulting_resolution,[],[f87,f56])).

fof(f56,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ sP8(X2,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ sP8(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f87,plain,(
    ! [X0,X1] : sP8(X0,k1_tarski(k4_tarski(X1,X0))) ),
    inference(unit_resulting_resolution,[],[f54,f47])).

fof(f47,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | sP8(X2,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f96,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f34,f91])).

fof(f91,plain,(
    k1_xboole_0 = sK3(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f33,f35,f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f35,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f33,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f97,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f33,f91])).

fof(f183,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f180,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X2,X3] :
      ( sK1 != X2
      | ~ r1_tarski(k2_relat_1(sK2(X2,X3)),sK0)
      | k1_xboole_0 = X2 ) ),
    inference(global_subsumption,[],[f29,f28,f116])).

fof(f116,plain,(
    ! [X2,X3] :
      ( sK1 != X2
      | ~ v1_funct_1(sK2(X2,X3))
      | ~ v1_relat_1(sK2(X2,X3))
      | ~ r1_tarski(k2_relat_1(sK2(X2,X3)),sK0)
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f21,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f222,plain,(
    ! [X0] : ~ r2_hidden(sK5(k1_tarski(X0),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f196,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f141,plain,(
    ! [X0] : ~ sP8(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f138,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ sP8(X0,k1_xboole_0)
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f56,f24])).

fof(f184,plain,(
    k1_xboole_0 != sK0 ),
    inference(unit_resulting_resolution,[],[f180,f22])).

fof(f22,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:23:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (10739)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.20/0.52  % (10742)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.20/0.52  % (10743)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.20/0.52  % (10753)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.20/0.52  % (10739)Refutation not found, incomplete strategy% (10739)------------------------------
% 1.20/0.52  % (10739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (10733)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.20/0.52  % (10739)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (10739)Memory used [KB]: 10746
% 1.20/0.52  % (10739)Time elapsed: 0.097 s
% 1.20/0.52  % (10739)------------------------------
% 1.20/0.52  % (10739)------------------------------
% 1.20/0.52  % (10737)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.20/0.53  % (10759)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.20/0.53  % (10760)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.20/0.53  % (10746)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.20/0.53  % (10731)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.20/0.53  % (10731)Refutation not found, incomplete strategy% (10731)------------------------------
% 1.20/0.53  % (10731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (10731)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (10731)Memory used [KB]: 1663
% 1.20/0.53  % (10731)Time elapsed: 0.107 s
% 1.20/0.53  % (10731)------------------------------
% 1.20/0.53  % (10731)------------------------------
% 1.20/0.53  % (10754)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.20/0.53  % (10750)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.20/0.53  % (10755)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.20/0.53  % (10734)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.20/0.53  % (10751)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.20/0.54  % (10735)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.20/0.54  % (10756)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.54  % (10736)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.36/0.54  % (10761)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.54  % (10732)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.54  % (10747)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.54  % (10748)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.54  % (10733)Refutation not found, incomplete strategy% (10733)------------------------------
% 1.36/0.54  % (10733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (10733)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (10733)Memory used [KB]: 10746
% 1.36/0.54  % (10733)Time elapsed: 0.136 s
% 1.36/0.54  % (10733)------------------------------
% 1.36/0.54  % (10733)------------------------------
% 1.36/0.54  % (10758)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.54  % (10757)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.55  % (10762)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.55  % (10749)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.55  % (10749)Refutation not found, incomplete strategy% (10749)------------------------------
% 1.36/0.55  % (10749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (10749)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (10749)Memory used [KB]: 10618
% 1.36/0.55  % (10749)Time elapsed: 0.139 s
% 1.36/0.55  % (10749)------------------------------
% 1.36/0.55  % (10749)------------------------------
% 1.36/0.55  % (10741)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.55  % (10740)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.55  % (10741)Refutation not found, incomplete strategy% (10741)------------------------------
% 1.36/0.55  % (10741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (10741)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (10741)Memory used [KB]: 10618
% 1.36/0.55  % (10741)Time elapsed: 0.151 s
% 1.36/0.55  % (10741)------------------------------
% 1.36/0.55  % (10741)------------------------------
% 1.36/0.55  % (10740)Refutation not found, incomplete strategy% (10740)------------------------------
% 1.36/0.55  % (10740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (10740)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (10740)Memory used [KB]: 10618
% 1.36/0.55  % (10740)Time elapsed: 0.150 s
% 1.36/0.55  % (10740)------------------------------
% 1.36/0.55  % (10740)------------------------------
% 1.36/0.56  % (10744)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.56  % (10755)Refutation not found, incomplete strategy% (10755)------------------------------
% 1.36/0.56  % (10755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (10755)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (10755)Memory used [KB]: 10746
% 1.36/0.56  % (10755)Time elapsed: 0.114 s
% 1.36/0.56  % (10755)------------------------------
% 1.36/0.56  % (10755)------------------------------
% 1.36/0.56  % (10757)Refutation found. Thanks to Tanya!
% 1.36/0.56  % SZS status Theorem for theBenchmark
% 1.36/0.56  % SZS output start Proof for theBenchmark
% 1.36/0.56  fof(f336,plain,(
% 1.36/0.56    $false),
% 1.36/0.56    inference(global_subsumption,[],[f184,f335])).
% 1.36/0.56  fof(f335,plain,(
% 1.36/0.56    k1_xboole_0 = sK0),
% 1.36/0.56    inference(forward_demodulation,[],[f329,f24])).
% 1.36/0.56  fof(f24,plain,(
% 1.36/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.36/0.56    inference(cnf_transformation,[],[f6])).
% 1.36/0.56  fof(f6,axiom,(
% 1.36/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.36/0.56  fof(f329,plain,(
% 1.36/0.56    k2_relat_1(k1_xboole_0) = sK0),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f141,f310,f50])).
% 1.36/0.56  fof(f50,plain,(
% 1.36/0.56    ( ! [X0,X1] : (sP8(sK7(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.36/0.56    inference(cnf_transformation,[],[f5])).
% 1.36/0.56  fof(f5,axiom,(
% 1.36/0.56    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.36/0.56  fof(f310,plain,(
% 1.36/0.56    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 1.36/0.56    inference(backward_demodulation,[],[f222,f295])).
% 1.36/0.56  fof(f295,plain,(
% 1.36/0.56    ( ! [X0] : (sK5(k1_tarski(X0),sK0) = X0) )),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f223,f52])).
% 1.36/0.56  fof(f52,plain,(
% 1.36/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.36/0.56    inference(equality_resolution,[],[f43])).
% 1.36/0.56  fof(f43,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.36/0.56    inference(cnf_transformation,[],[f4])).
% 1.36/0.56  fof(f4,axiom,(
% 1.36/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.36/0.56  fof(f223,plain,(
% 1.36/0.56    ( ! [X0] : (r2_hidden(sK5(k1_tarski(X0),sK0),k1_tarski(X0))) )),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f196,f40])).
% 1.36/0.56  fof(f40,plain,(
% 1.36/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f20])).
% 1.36/0.56  fof(f20,plain,(
% 1.36/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.36/0.56    inference(ennf_transformation,[],[f1])).
% 1.36/0.56  fof(f1,axiom,(
% 1.36/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.36/0.56  fof(f196,plain,(
% 1.36/0.56    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK0)) )),
% 1.36/0.56    inference(backward_demodulation,[],[f183,f190])).
% 1.36/0.56  fof(f190,plain,(
% 1.36/0.56    ( ! [X0] : (k1_tarski(X0) = k2_relat_1(sK2(sK1,X0))) )),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f180,f31])).
% 1.36/0.56  fof(f31,plain,(
% 1.36/0.56    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.36/0.56    inference(cnf_transformation,[],[f17])).
% 1.36/0.56  fof(f17,plain,(
% 1.36/0.56    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.36/0.56    inference(ennf_transformation,[],[f9])).
% 1.36/0.56  fof(f9,axiom,(
% 1.36/0.56    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.36/0.56  fof(f180,plain,(
% 1.36/0.56    k1_xboole_0 != sK1),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f97,f96,f144,f60])).
% 1.36/0.56  fof(f60,plain,(
% 1.36/0.56    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.36/0.56    inference(forward_demodulation,[],[f58,f24])).
% 1.36/0.56  fof(f58,plain,(
% 1.36/0.56    k1_xboole_0 != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),sK0)),
% 1.36/0.56    inference(superposition,[],[f21,f23])).
% 1.36/0.56  fof(f23,plain,(
% 1.36/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.36/0.56    inference(cnf_transformation,[],[f6])).
% 1.36/0.56  fof(f21,plain,(
% 1.36/0.56    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),sK0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f14])).
% 1.36/0.56  fof(f14,plain,(
% 1.36/0.56    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.36/0.56    inference(flattening,[],[f13])).
% 1.36/0.56  fof(f13,plain,(
% 1.36/0.56    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.36/0.56    inference(ennf_transformation,[],[f11])).
% 1.36/0.56  fof(f11,negated_conjecture,(
% 1.36/0.56    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.36/0.56    inference(negated_conjecture,[],[f10])).
% 1.36/0.56  fof(f10,conjecture,(
% 1.36/0.56    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 1.36/0.56  fof(f144,plain,(
% 1.36/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f138,f40])).
% 1.36/0.56  fof(f138,plain,(
% 1.36/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f90,f25,f36])).
% 1.36/0.56  fof(f36,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f19])).
% 1.36/0.56  fof(f19,plain,(
% 1.36/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.36/0.56    inference(ennf_transformation,[],[f12])).
% 1.36/0.56  fof(f12,plain,(
% 1.36/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.36/0.56    inference(rectify,[],[f2])).
% 1.36/0.56  fof(f2,axiom,(
% 1.36/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.36/0.56  fof(f25,plain,(
% 1.36/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f3])).
% 1.36/0.56  fof(f3,axiom,(
% 1.36/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.36/0.56  fof(f90,plain,(
% 1.36/0.56    ( ! [X0,X1] : (r2_hidden(X0,k2_relat_1(k1_tarski(k4_tarski(X1,X0))))) )),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f87,f56])).
% 1.36/0.56  fof(f56,plain,(
% 1.36/0.56    ( ! [X2,X0] : (r2_hidden(X2,k2_relat_1(X0)) | ~sP8(X2,X0)) )),
% 1.36/0.56    inference(equality_resolution,[],[f48])).
% 1.36/0.56  fof(f48,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~sP8(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.36/0.56    inference(cnf_transformation,[],[f5])).
% 1.36/0.56  fof(f87,plain,(
% 1.36/0.56    ( ! [X0,X1] : (sP8(X0,k1_tarski(k4_tarski(X1,X0)))) )),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f54,f47])).
% 1.36/0.56  fof(f47,plain,(
% 1.36/0.56    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | sP8(X2,X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f5])).
% 1.36/0.56  fof(f54,plain,(
% 1.36/0.56    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 1.36/0.56    inference(equality_resolution,[],[f53])).
% 1.36/0.56  fof(f53,plain,(
% 1.36/0.56    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 1.36/0.56    inference(equality_resolution,[],[f42])).
% 1.36/0.56  fof(f42,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.36/0.56    inference(cnf_transformation,[],[f4])).
% 1.36/0.56  fof(f96,plain,(
% 1.36/0.56    v1_funct_1(k1_xboole_0)),
% 1.36/0.56    inference(superposition,[],[f34,f91])).
% 1.36/0.56  fof(f91,plain,(
% 1.36/0.56    k1_xboole_0 = sK3(k1_xboole_0)),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f33,f35,f26])).
% 1.36/0.56  fof(f26,plain,(
% 1.36/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.36/0.56    inference(cnf_transformation,[],[f16])).
% 1.36/0.56  fof(f16,plain,(
% 1.36/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.36/0.56    inference(flattening,[],[f15])).
% 1.36/0.56  fof(f15,plain,(
% 1.36/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.36/0.56    inference(ennf_transformation,[],[f7])).
% 1.36/0.56  fof(f7,axiom,(
% 1.36/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.36/0.56  fof(f35,plain,(
% 1.36/0.56    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 1.36/0.56    inference(cnf_transformation,[],[f18])).
% 1.36/0.56  fof(f18,plain,(
% 1.36/0.56    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.36/0.56    inference(ennf_transformation,[],[f8])).
% 1.36/0.56  fof(f8,axiom,(
% 1.36/0.56    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.36/0.56  fof(f33,plain,(
% 1.36/0.56    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f18])).
% 1.36/0.56  fof(f34,plain,(
% 1.36/0.56    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f18])).
% 1.36/0.56  fof(f97,plain,(
% 1.36/0.56    v1_relat_1(k1_xboole_0)),
% 1.36/0.56    inference(superposition,[],[f33,f91])).
% 1.36/0.56  fof(f183,plain,(
% 1.36/0.56    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)) )),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f180,f118])).
% 1.36/0.56  fof(f118,plain,(
% 1.36/0.56    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0) | k1_xboole_0 = sK1) )),
% 1.36/0.56    inference(equality_resolution,[],[f117])).
% 1.36/0.56  fof(f117,plain,(
% 1.36/0.56    ( ! [X2,X3] : (sK1 != X2 | ~r1_tarski(k2_relat_1(sK2(X2,X3)),sK0) | k1_xboole_0 = X2) )),
% 1.36/0.56    inference(global_subsumption,[],[f29,f28,f116])).
% 1.36/0.56  fof(f116,plain,(
% 1.36/0.56    ( ! [X2,X3] : (sK1 != X2 | ~v1_funct_1(sK2(X2,X3)) | ~v1_relat_1(sK2(X2,X3)) | ~r1_tarski(k2_relat_1(sK2(X2,X3)),sK0) | k1_xboole_0 = X2) )),
% 1.36/0.56    inference(superposition,[],[f21,f30])).
% 1.36/0.56  fof(f30,plain,(
% 1.36/0.56    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.36/0.56    inference(cnf_transformation,[],[f17])).
% 1.36/0.56  fof(f28,plain,(
% 1.36/0.56    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.36/0.56    inference(cnf_transformation,[],[f17])).
% 1.36/0.56  fof(f29,plain,(
% 1.36/0.56    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.36/0.56    inference(cnf_transformation,[],[f17])).
% 1.36/0.56  fof(f222,plain,(
% 1.36/0.56    ( ! [X0] : (~r2_hidden(sK5(k1_tarski(X0),sK0),sK0)) )),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f196,f41])).
% 1.36/0.56  fof(f41,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f20])).
% 1.36/0.56  fof(f141,plain,(
% 1.36/0.56    ( ! [X0] : (~sP8(X0,k1_xboole_0)) )),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f138,f69])).
% 1.36/0.56  fof(f69,plain,(
% 1.36/0.56    ( ! [X0] : (~sP8(X0,k1_xboole_0) | r2_hidden(X0,k1_xboole_0)) )),
% 1.36/0.56    inference(superposition,[],[f56,f24])).
% 1.36/0.56  fof(f184,plain,(
% 1.36/0.56    k1_xboole_0 != sK0),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f180,f22])).
% 1.36/0.56  fof(f22,plain,(
% 1.36/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.36/0.56    inference(cnf_transformation,[],[f14])).
% 1.36/0.56  % SZS output end Proof for theBenchmark
% 1.36/0.56  % (10757)------------------------------
% 1.36/0.56  % (10757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (10757)Termination reason: Refutation
% 1.36/0.56  
% 1.36/0.56  % (10757)Memory used [KB]: 6524
% 1.36/0.56  % (10757)Time elapsed: 0.150 s
% 1.36/0.56  % (10757)------------------------------
% 1.36/0.56  % (10757)------------------------------
% 1.36/0.56  % (10738)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.56  % (10725)Success in time 0.194 s
%------------------------------------------------------------------------------
