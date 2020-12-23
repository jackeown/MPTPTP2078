%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:03 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 397 expanded)
%              Number of leaves         :   15 ( 116 expanded)
%              Depth                    :   14
%              Number of atoms          :  187 (1203 expanded)
%              Number of equality atoms :   55 ( 515 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f488,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f117,f248,f334,f338,f487])).

fof(f487,plain,(
    spl11_3 ),
    inference(avatar_contradiction_clause,[],[f480])).

fof(f480,plain,
    ( $false
    | spl11_3 ),
    inference(unit_resulting_resolution,[],[f108,f430,f434])).

fof(f434,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | sK7(X0) != sK7(k1_xboole_0) )
    | spl11_3 ),
    inference(backward_demodulation,[],[f39,f430])).

fof(f39,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK7(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f430,plain,
    ( ! [X0] : sK7(k1_xboole_0) = X0
    | spl11_3 ),
    inference(unit_resulting_resolution,[],[f419,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
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

fof(f419,plain,
    ( ! [X0] : r2_hidden(sK7(k1_xboole_0),X0)
    | spl11_3 ),
    inference(unit_resulting_resolution,[],[f25,f413,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f413,plain,
    ( r2_hidden(sK7(k1_xboole_0),k1_xboole_0)
    | spl11_3 ),
    inference(unit_resulting_resolution,[],[f108,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK7(X0),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f108,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl11_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f338,plain,(
    spl11_4 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | spl11_4 ),
    inference(unit_resulting_resolution,[],[f44,f112,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f112,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl11_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl11_4
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f334,plain,(
    spl11_5 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | spl11_5 ),
    inference(unit_resulting_resolution,[],[f25,f116])).

fof(f116,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl11_5
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f248,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl11_1
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f57,f200])).

fof(f200,plain,
    ( k1_xboole_0 = sK0
    | spl11_1 ),
    inference(backward_demodulation,[],[f167,f195])).

fof(f195,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f160,f158,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f158,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | spl11_1 ),
    inference(backward_demodulation,[],[f146,f152])).

fof(f152,plain,
    ( ! [X0] : sK2(k1_tarski(X0),sK0) = X0
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f142,f47])).

fof(f142,plain,
    ( ! [X0] : r2_hidden(sK2(k1_tarski(X0),sK0),k1_tarski(X0))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f141,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f141,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(X0),sK0)
    | spl11_1 ),
    inference(forward_demodulation,[],[f140,f121])).

fof(f121,plain,
    ( ! [X0] : k1_tarski(X0) = k2_relat_1(sK6(sK1,X0))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f52,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK6(X0,X1))
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f52,plain,
    ( k1_xboole_0 != sK1
    | spl11_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl11_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f140,plain,
    ( ! [X0] : ~ r1_tarski(k2_relat_1(sK6(sK1,X0)),sK0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f118,f119,f120,f20])).

fof(f20,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f120,plain,
    ( ! [X0] : sK1 = k1_relat_1(sK6(sK1,X0))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f52,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK6(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f119,plain,
    ( ! [X0] : v1_funct_1(sK6(sK1,X0))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f52,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK6(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f118,plain,
    ( ! [X0] : v1_relat_1(sK6(sK1,X0))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f52,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK6(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f146,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k1_tarski(X0),sK0),k1_xboole_0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f25,f143,f22])).

fof(f143,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k1_tarski(X0),sK0),sK0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f141,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f160,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl11_1 ),
    inference(backward_demodulation,[],[f143,f152])).

fof(f167,plain,
    ( sK0 = k2_relat_1(sK0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f160,f160,f28])).

fof(f57,plain,
    ( k1_xboole_0 != sK0
    | spl11_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl11_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f117,plain,
    ( ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f75,f51,f114,f110,f106])).

fof(f75,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f74,f34])).

fof(f34,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f74,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != sK1
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f20,f35])).

fof(f35,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f58,plain,
    ( spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f21,f55,f51])).

fof(f21,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:43:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (19495)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (19486)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (19485)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (19487)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (19503)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (19483)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (19503)Refutation not found, incomplete strategy% (19503)------------------------------
% 0.21/0.52  % (19503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19489)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.26/0.52  % (19490)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.26/0.52  % (19503)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.52  
% 1.26/0.52  % (19503)Memory used [KB]: 10746
% 1.26/0.52  % (19503)Time elapsed: 0.110 s
% 1.26/0.52  % (19503)------------------------------
% 1.26/0.52  % (19503)------------------------------
% 1.26/0.52  % (19489)Refutation not found, incomplete strategy% (19489)------------------------------
% 1.26/0.52  % (19489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (19489)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.52  
% 1.26/0.52  % (19489)Memory used [KB]: 10746
% 1.26/0.52  % (19489)Time elapsed: 0.108 s
% 1.26/0.52  % (19489)------------------------------
% 1.26/0.52  % (19489)------------------------------
% 1.26/0.52  % (19490)Refutation not found, incomplete strategy% (19490)------------------------------
% 1.26/0.52  % (19490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (19490)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.52  
% 1.26/0.52  % (19490)Memory used [KB]: 10618
% 1.26/0.52  % (19490)Time elapsed: 0.107 s
% 1.26/0.52  % (19490)------------------------------
% 1.26/0.52  % (19490)------------------------------
% 1.26/0.53  % (19506)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.26/0.53  % (19500)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.26/0.53  % (19501)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.26/0.53  % (19482)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.54  % (19499)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.26/0.54  % (19510)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.26/0.54  % (19498)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.26/0.54  % (19492)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.54  % (19484)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.54  % (19483)Refutation not found, incomplete strategy% (19483)------------------------------
% 1.35/0.54  % (19483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (19483)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (19483)Memory used [KB]: 10746
% 1.35/0.54  % (19483)Time elapsed: 0.128 s
% 1.35/0.54  % (19483)------------------------------
% 1.35/0.54  % (19483)------------------------------
% 1.35/0.54  % (19502)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.54  % (19497)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.54  % (19491)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.54  % (19509)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.55  % (19491)Refutation not found, incomplete strategy% (19491)------------------------------
% 1.35/0.55  % (19491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (19491)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (19491)Memory used [KB]: 10618
% 1.35/0.55  % (19491)Time elapsed: 0.133 s
% 1.35/0.55  % (19491)------------------------------
% 1.35/0.55  % (19491)------------------------------
% 1.35/0.55  % (19498)Refutation not found, incomplete strategy% (19498)------------------------------
% 1.35/0.55  % (19498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (19508)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.55  % (19498)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (19498)Memory used [KB]: 10618
% 1.35/0.55  % (19498)Time elapsed: 0.125 s
% 1.35/0.55  % (19498)------------------------------
% 1.35/0.55  % (19498)------------------------------
% 1.35/0.55  % (19505)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.55  % (19481)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.35/0.55  % (19494)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.55  % (19507)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.55  % (19481)Refutation not found, incomplete strategy% (19481)------------------------------
% 1.35/0.55  % (19481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (19481)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (19481)Memory used [KB]: 1663
% 1.35/0.55  % (19481)Time elapsed: 0.136 s
% 1.35/0.55  % (19481)------------------------------
% 1.35/0.55  % (19481)------------------------------
% 1.35/0.55  % (19493)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.56  % (19496)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.56  % (19485)Refutation found. Thanks to Tanya!
% 1.35/0.56  % SZS status Theorem for theBenchmark
% 1.35/0.56  % SZS output start Proof for theBenchmark
% 1.35/0.56  fof(f488,plain,(
% 1.35/0.56    $false),
% 1.35/0.56    inference(avatar_sat_refutation,[],[f58,f117,f248,f334,f338,f487])).
% 1.35/0.56  fof(f487,plain,(
% 1.35/0.56    spl11_3),
% 1.35/0.56    inference(avatar_contradiction_clause,[],[f480])).
% 1.35/0.56  fof(f480,plain,(
% 1.35/0.56    $false | spl11_3),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f108,f430,f434])).
% 1.35/0.56  fof(f434,plain,(
% 1.35/0.56    ( ! [X0] : (v1_relat_1(X0) | sK7(X0) != sK7(k1_xboole_0)) ) | spl11_3),
% 1.35/0.56    inference(backward_demodulation,[],[f39,f430])).
% 1.35/0.56  fof(f39,plain,(
% 1.35/0.56    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK7(X0) | v1_relat_1(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f19])).
% 1.35/0.56  fof(f19,plain,(
% 1.35/0.56    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f7])).
% 1.35/0.56  fof(f7,axiom,(
% 1.35/0.56    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.35/0.56  fof(f430,plain,(
% 1.35/0.56    ( ! [X0] : (sK7(k1_xboole_0) = X0) ) | spl11_3),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f419,f47])).
% 1.35/0.56  fof(f47,plain,(
% 1.35/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.35/0.56    inference(equality_resolution,[],[f41])).
% 1.35/0.56  fof(f41,plain,(
% 1.35/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.35/0.56    inference(cnf_transformation,[],[f4])).
% 1.35/0.56  fof(f4,axiom,(
% 1.35/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.35/0.56  fof(f419,plain,(
% 1.35/0.56    ( ! [X0] : (r2_hidden(sK7(k1_xboole_0),X0)) ) | spl11_3),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f25,f413,f22])).
% 1.35/0.56  fof(f22,plain,(
% 1.35/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f16])).
% 1.35/0.56  fof(f16,plain,(
% 1.35/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f1])).
% 1.35/0.56  fof(f1,axiom,(
% 1.35/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.35/0.56  fof(f413,plain,(
% 1.35/0.56    r2_hidden(sK7(k1_xboole_0),k1_xboole_0) | spl11_3),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f108,f38])).
% 1.35/0.56  fof(f38,plain,(
% 1.35/0.56    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK7(X0),X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f19])).
% 1.35/0.56  fof(f25,plain,(
% 1.35/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f3])).
% 1.35/0.56  fof(f3,axiom,(
% 1.35/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.35/0.56  fof(f108,plain,(
% 1.35/0.56    ~v1_relat_1(k1_xboole_0) | spl11_3),
% 1.35/0.56    inference(avatar_component_clause,[],[f106])).
% 1.35/0.56  fof(f106,plain,(
% 1.35/0.56    spl11_3 <=> v1_relat_1(k1_xboole_0)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.35/0.56  fof(f338,plain,(
% 1.35/0.56    spl11_4),
% 1.35/0.56    inference(avatar_contradiction_clause,[],[f336])).
% 1.35/0.56  fof(f336,plain,(
% 1.35/0.56    $false | spl11_4),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f44,f112,f36])).
% 1.35/0.56  fof(f36,plain,(
% 1.35/0.56    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f18])).
% 1.35/0.56  fof(f18,plain,(
% 1.35/0.56    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 1.35/0.56    inference(ennf_transformation,[],[f10])).
% 1.35/0.56  fof(f10,axiom,(
% 1.35/0.56    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 1.35/0.56  fof(f112,plain,(
% 1.35/0.56    ~v1_funct_1(k1_xboole_0) | spl11_4),
% 1.35/0.56    inference(avatar_component_clause,[],[f110])).
% 1.35/0.56  fof(f110,plain,(
% 1.35/0.56    spl11_4 <=> v1_funct_1(k1_xboole_0)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.35/0.56  fof(f44,plain,(
% 1.35/0.56    v1_xboole_0(k1_xboole_0)),
% 1.35/0.56    inference(cnf_transformation,[],[f2])).
% 1.35/0.56  fof(f2,axiom,(
% 1.35/0.56    v1_xboole_0(k1_xboole_0)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.35/0.56  fof(f334,plain,(
% 1.35/0.56    spl11_5),
% 1.35/0.56    inference(avatar_contradiction_clause,[],[f331])).
% 1.35/0.56  fof(f331,plain,(
% 1.35/0.56    $false | spl11_5),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f25,f116])).
% 1.35/0.56  fof(f116,plain,(
% 1.35/0.56    ~r1_tarski(k1_xboole_0,sK0) | spl11_5),
% 1.35/0.56    inference(avatar_component_clause,[],[f114])).
% 1.35/0.56  fof(f114,plain,(
% 1.35/0.56    spl11_5 <=> r1_tarski(k1_xboole_0,sK0)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.35/0.56  fof(f248,plain,(
% 1.35/0.56    spl11_1 | spl11_2),
% 1.35/0.56    inference(avatar_contradiction_clause,[],[f244])).
% 1.35/0.56  fof(f244,plain,(
% 1.35/0.56    $false | (spl11_1 | spl11_2)),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f57,f200])).
% 1.35/0.56  fof(f200,plain,(
% 1.35/0.56    k1_xboole_0 = sK0 | spl11_1),
% 1.35/0.56    inference(backward_demodulation,[],[f167,f195])).
% 1.35/0.56  fof(f195,plain,(
% 1.35/0.56    k1_xboole_0 = k2_relat_1(sK0) | spl11_1),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f160,f158,f28])).
% 1.35/0.56  fof(f28,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.35/0.56    inference(cnf_transformation,[],[f8])).
% 1.35/0.56  fof(f8,axiom,(
% 1.35/0.56    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.35/0.56  fof(f158,plain,(
% 1.35/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | spl11_1),
% 1.35/0.56    inference(backward_demodulation,[],[f146,f152])).
% 1.35/0.56  fof(f152,plain,(
% 1.35/0.56    ( ! [X0] : (sK2(k1_tarski(X0),sK0) = X0) ) | spl11_1),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f142,f47])).
% 1.35/0.56  fof(f142,plain,(
% 1.35/0.56    ( ! [X0] : (r2_hidden(sK2(k1_tarski(X0),sK0),k1_tarski(X0))) ) | spl11_1),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f141,f23])).
% 1.35/0.56  fof(f23,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f16])).
% 1.35/0.56  fof(f141,plain,(
% 1.35/0.56    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK0)) ) | spl11_1),
% 1.35/0.56    inference(forward_demodulation,[],[f140,f121])).
% 1.35/0.56  fof(f121,plain,(
% 1.35/0.56    ( ! [X0] : (k1_tarski(X0) = k2_relat_1(sK6(sK1,X0))) ) | spl11_1),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f52,f33])).
% 1.35/0.56  fof(f33,plain,(
% 1.35/0.56    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK6(X0,X1)) | k1_xboole_0 = X0) )),
% 1.35/0.56    inference(cnf_transformation,[],[f17])).
% 1.35/0.56  fof(f17,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.35/0.56    inference(ennf_transformation,[],[f11])).
% 1.35/0.56  fof(f11,axiom,(
% 1.35/0.56    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.35/0.56  fof(f52,plain,(
% 1.35/0.56    k1_xboole_0 != sK1 | spl11_1),
% 1.35/0.56    inference(avatar_component_clause,[],[f51])).
% 1.35/0.56  fof(f51,plain,(
% 1.35/0.56    spl11_1 <=> k1_xboole_0 = sK1),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.35/0.56  fof(f140,plain,(
% 1.35/0.56    ( ! [X0] : (~r1_tarski(k2_relat_1(sK6(sK1,X0)),sK0)) ) | spl11_1),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f118,f119,f120,f20])).
% 1.35/0.56  fof(f20,plain,(
% 1.35/0.56    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~v1_relat_1(X2)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f15])).
% 1.35/0.56  fof(f15,plain,(
% 1.35/0.56    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.35/0.56    inference(flattening,[],[f14])).
% 1.35/0.56  fof(f14,plain,(
% 1.35/0.56    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.35/0.56    inference(ennf_transformation,[],[f13])).
% 1.35/0.56  fof(f13,negated_conjecture,(
% 1.35/0.56    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.35/0.56    inference(negated_conjecture,[],[f12])).
% 1.35/0.56  fof(f12,conjecture,(
% 1.35/0.56    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 1.35/0.56  fof(f120,plain,(
% 1.35/0.56    ( ! [X0] : (sK1 = k1_relat_1(sK6(sK1,X0))) ) | spl11_1),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f52,f32])).
% 1.35/0.56  fof(f32,plain,(
% 1.35/0.56    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.35/0.56    inference(cnf_transformation,[],[f17])).
% 1.35/0.56  fof(f119,plain,(
% 1.35/0.56    ( ! [X0] : (v1_funct_1(sK6(sK1,X0))) ) | spl11_1),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f52,f31])).
% 1.35/0.56  fof(f31,plain,(
% 1.35/0.56    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1)) | k1_xboole_0 = X0) )),
% 1.35/0.56    inference(cnf_transformation,[],[f17])).
% 1.35/0.56  fof(f118,plain,(
% 1.35/0.56    ( ! [X0] : (v1_relat_1(sK6(sK1,X0))) ) | spl11_1),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f52,f30])).
% 1.35/0.56  fof(f30,plain,(
% 1.35/0.56    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1)) | k1_xboole_0 = X0) )),
% 1.35/0.56    inference(cnf_transformation,[],[f17])).
% 1.35/0.56  fof(f146,plain,(
% 1.35/0.56    ( ! [X0] : (~r2_hidden(sK2(k1_tarski(X0),sK0),k1_xboole_0)) ) | spl11_1),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f25,f143,f22])).
% 1.35/0.56  fof(f143,plain,(
% 1.35/0.56    ( ! [X0] : (~r2_hidden(sK2(k1_tarski(X0),sK0),sK0)) ) | spl11_1),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f141,f24])).
% 1.35/0.56  fof(f24,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f16])).
% 1.35/0.56  fof(f160,plain,(
% 1.35/0.56    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl11_1),
% 1.35/0.56    inference(backward_demodulation,[],[f143,f152])).
% 1.35/0.56  fof(f167,plain,(
% 1.35/0.56    sK0 = k2_relat_1(sK0) | spl11_1),
% 1.35/0.56    inference(unit_resulting_resolution,[],[f160,f160,f28])).
% 1.35/0.56  fof(f57,plain,(
% 1.35/0.56    k1_xboole_0 != sK0 | spl11_2),
% 1.35/0.56    inference(avatar_component_clause,[],[f55])).
% 1.35/0.56  fof(f55,plain,(
% 1.35/0.56    spl11_2 <=> k1_xboole_0 = sK0),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.35/0.56  fof(f117,plain,(
% 1.35/0.56    ~spl11_3 | ~spl11_4 | ~spl11_5 | ~spl11_1),
% 1.35/0.56    inference(avatar_split_clause,[],[f75,f51,f114,f110,f106])).
% 1.35/0.56  fof(f75,plain,(
% 1.35/0.56    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.35/0.56    inference(forward_demodulation,[],[f74,f34])).
% 1.35/0.56  fof(f34,plain,(
% 1.35/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.35/0.56    inference(cnf_transformation,[],[f9])).
% 1.35/0.56  fof(f9,axiom,(
% 1.35/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.35/0.56  fof(f74,plain,(
% 1.35/0.56    ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != sK1 | ~v1_relat_1(k1_xboole_0)),
% 1.35/0.56    inference(superposition,[],[f20,f35])).
% 1.35/0.56  fof(f35,plain,(
% 1.35/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.35/0.56    inference(cnf_transformation,[],[f9])).
% 1.35/0.56  fof(f58,plain,(
% 1.35/0.56    spl11_1 | ~spl11_2),
% 1.35/0.56    inference(avatar_split_clause,[],[f21,f55,f51])).
% 1.35/0.56  fof(f21,plain,(
% 1.35/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.35/0.56    inference(cnf_transformation,[],[f15])).
% 1.35/0.56  % SZS output end Proof for theBenchmark
% 1.35/0.56  % (19485)------------------------------
% 1.35/0.56  % (19485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (19485)Termination reason: Refutation
% 1.35/0.56  
% 1.35/0.56  % (19485)Memory used [KB]: 6396
% 1.35/0.56  % (19485)Time elapsed: 0.149 s
% 1.35/0.56  % (19485)------------------------------
% 1.35/0.56  % (19485)------------------------------
% 1.35/0.57  % (19480)Success in time 0.199 s
%------------------------------------------------------------------------------
