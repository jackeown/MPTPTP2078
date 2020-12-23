%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 318 expanded)
%              Number of leaves         :    9 (  74 expanded)
%              Depth                    :   23
%              Number of atoms          :  200 (1143 expanded)
%              Number of equality atoms :   91 ( 545 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(global_subsumption,[],[f21,f104,f192])).

% (9275)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f192,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f178,f162])).

fof(f162,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f161,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f38,f22])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f156,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f156,plain,(
    ! [X2] : r1_xboole_0(X2,k1_xboole_0) ),
    inference(resolution,[],[f153,f62])).

fof(f62,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,k1_xboole_0),X3)
      | r1_xboole_0(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f59,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f153,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(equality_resolution,[],[f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r2_hidden(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f151,f98])).

fof(f98,plain,(
    ! [X0] :
      ( sK1 != X0
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f97,f32])).

fof(f32,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f97,plain,(
    ! [X1] :
      ( sK1 != k1_relat_1(sK3(X1))
      | k1_xboole_0 != X1 ) ),
    inference(subsumption_resolution,[],[f96,f30])).

fof(f30,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f96,plain,(
    ! [X1] :
      ( sK1 != k1_relat_1(sK3(X1))
      | ~ v1_relat_1(sK3(X1))
      | k1_xboole_0 != X1 ) ),
    inference(subsumption_resolution,[],[f95,f31])).

fof(f31,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3(X1))
      | sK1 != k1_relat_1(sK3(X1))
      | ~ v1_relat_1(sK3(X1))
      | k1_xboole_0 != X1 ) ),
    inference(subsumption_resolution,[],[f92,f22])).

fof(f92,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | ~ v1_funct_1(sK3(X1))
      | sK1 != k1_relat_1(sK3(X1))
      | ~ v1_relat_1(sK3(X1))
      | k1_xboole_0 != X1 ) ),
    inference(superposition,[],[f20,f90])).

fof(f90,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(sK3(X0))
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f88,f32])).

fof(f88,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(sK3(X0))
      | k1_xboole_0 != k1_relat_1(sK3(X0)) ) ),
    inference(resolution,[],[f24,f30])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

% (9265)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f14,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f20,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f151,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f143,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f143,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X0))
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f141,f103])).

fof(f103,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X3),sK0)
      | sK1 != k1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f102,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f102,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X3),sK0)
      | sK1 != k1_relat_1(sK2(X2,X3))
      | ~ v1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f100,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f100,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X3),sK0)
      | ~ v1_funct_1(sK2(X2,X3))
      | sK1 != k1_relat_1(sK2(X2,X3))
      | ~ v1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f20,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

% (9280)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f141,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(X0),sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f40,f139])).

fof(f139,plain,(
    ! [X0] : sK6(k1_tarski(X0),sK0) = X0 ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK6(k1_tarski(X1),sK0) = X1 ) ),
    inference(subsumption_resolution,[],[f137,f98])).

fof(f137,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK6(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK6(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f111,f27])).

fof(f111,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X0))
      | sK6(k1_tarski(X0),sK0) = X0
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f52,f103])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | sK6(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f39,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f178,plain,(
    ! [X19] :
      ( r2_hidden(sK5(X19,sK0),X19)
      | sK0 = X19 ) ),
    inference(resolution,[],[f36,f153])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f104,plain,(
    k1_xboole_0 != sK1 ),
    inference(equality_resolution,[],[f98])).

fof(f21,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:15:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.52  % (9274)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (9266)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (9282)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (9271)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (9266)Refutation not found, incomplete strategy% (9266)------------------------------
% 0.21/0.52  % (9266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9258)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (9260)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (9258)Refutation not found, incomplete strategy% (9258)------------------------------
% 0.21/0.53  % (9258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9258)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (9258)Memory used [KB]: 1663
% 0.21/0.53  % (9258)Time elapsed: 0.114 s
% 0.21/0.53  % (9258)------------------------------
% 0.21/0.53  % (9258)------------------------------
% 0.21/0.53  % (9266)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (9266)Memory used [KB]: 10618
% 0.21/0.53  % (9266)Time elapsed: 0.106 s
% 0.21/0.53  % (9266)------------------------------
% 0.21/0.53  % (9266)------------------------------
% 0.21/0.53  % (9260)Refutation not found, incomplete strategy% (9260)------------------------------
% 0.21/0.53  % (9260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9260)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (9260)Memory used [KB]: 10746
% 0.21/0.53  % (9260)Time elapsed: 0.115 s
% 0.21/0.53  % (9260)------------------------------
% 0.21/0.53  % (9260)------------------------------
% 0.21/0.53  % (9259)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (9261)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (9264)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (9281)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (9262)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (9285)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (9283)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (9263)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (9264)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f201,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(global_subsumption,[],[f21,f104,f192])).
% 0.21/0.54  % (9275)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  fof(f192,plain,(
% 0.21/0.54    k1_xboole_0 = sK0),
% 0.21/0.54    inference(resolution,[],[f178,f162])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f161,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(resolution,[],[f38,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(resolution,[],[f156,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ( ! [X2] : (r1_xboole_0(X2,k1_xboole_0)) )),
% 0.21/0.54    inference(resolution,[],[f153,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X2,X3] : (r2_hidden(sK4(X2,k1_xboole_0),X3) | r1_xboole_0(X2,k1_xboole_0)) )),
% 0.21/0.54    inference(resolution,[],[f59,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f152])).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f151,f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X0] : (sK1 != X0 | k1_xboole_0 != X0) )),
% 0.21/0.54    inference(superposition,[],[f97,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ( ! [X1] : (sK1 != k1_relat_1(sK3(X1)) | k1_xboole_0 != X1) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f96,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ( ! [X1] : (sK1 != k1_relat_1(sK3(X1)) | ~v1_relat_1(sK3(X1)) | k1_xboole_0 != X1) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f95,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X1] : (~v1_funct_1(sK3(X1)) | sK1 != k1_relat_1(sK3(X1)) | ~v1_relat_1(sK3(X1)) | k1_xboole_0 != X1) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f92,f22])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X1] : (~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(sK3(X1)) | sK1 != k1_relat_1(sK3(X1)) | ~v1_relat_1(sK3(X1)) | k1_xboole_0 != X1) )),
% 0.21/0.54    inference(superposition,[],[f20,f90])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK3(X0)) | k1_xboole_0 != X0) )),
% 0.21/0.54    inference(forward_demodulation,[],[f88,f32])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK3(X0)) | k1_xboole_0 != k1_relat_1(sK3(X0))) )),
% 0.21/0.54    inference(resolution,[],[f24,f30])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  % (9265)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.54    inference(flattening,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.54    inference(negated_conjecture,[],[f9])).
% 0.21/0.54  fof(f9,conjecture,(
% 0.21/0.54    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f150])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(superposition,[],[f143,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,X0)) | ~r2_hidden(X0,sK0) | k1_xboole_0 = X1) )),
% 0.21/0.54    inference(resolution,[],[f141,f103])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X3),sK0) | sK1 != k1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f102,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X3),sK0) | sK1 != k1_relat_1(sK2(X2,X3)) | ~v1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f100,f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X3),sK0) | ~v1_funct_1(sK2(X2,X3)) | sK1 != k1_relat_1(sK2(X2,X3)) | ~v1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 0.21/0.54    inference(superposition,[],[f20,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  % (9280)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_tarski(X0),sK0) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.54    inference(superposition,[],[f40,f139])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    ( ! [X0] : (sK6(k1_tarski(X0),sK0) = X0) )),
% 0.21/0.54    inference(equality_resolution,[],[f138])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sK1 != X0 | sK6(k1_tarski(X1),sK0) = X1) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f137,f98])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sK1 != X0 | sK6(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f136])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sK1 != X0 | sK6(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(superposition,[],[f111,f27])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,X0)) | sK6(k1_tarski(X0),sK0) = X0 | k1_xboole_0 = X1) )),
% 0.21/0.54    inference(resolution,[],[f52,f103])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | sK6(k1_tarski(X0),X1) = X0) )),
% 0.21/0.54    inference(resolution,[],[f39,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 0.21/0.54    inference(equality_resolution,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    ( ! [X19] : (r2_hidden(sK5(X19,sK0),X19) | sK0 = X19) )),
% 0.21/0.54    inference(resolution,[],[f36,f153])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    k1_xboole_0 != sK1),
% 0.21/0.54    inference(equality_resolution,[],[f98])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (9264)------------------------------
% 0.21/0.54  % (9264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9275)Refutation not found, incomplete strategy% (9275)------------------------------
% 0.21/0.54  % (9275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9275)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (9275)Memory used [KB]: 10618
% 0.21/0.54  % (9275)Time elapsed: 0.130 s
% 0.21/0.54  % (9275)------------------------------
% 0.21/0.54  % (9275)------------------------------
% 0.21/0.54  % (9264)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (9264)Memory used [KB]: 6396
% 0.21/0.54  % (9264)Time elapsed: 0.135 s
% 0.21/0.54  % (9264)------------------------------
% 0.21/0.54  % (9264)------------------------------
% 0.21/0.55  % (9257)Success in time 0.18 s
%------------------------------------------------------------------------------
