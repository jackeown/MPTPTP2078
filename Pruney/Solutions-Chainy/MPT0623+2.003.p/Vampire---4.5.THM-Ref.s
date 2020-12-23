%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 (  98 expanded)
%              Number of leaves         :   16 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  180 ( 283 expanded)
%              Number of equality atoms :   63 ( 114 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f59,f62,f67,f78,f81,f84])).

fof(f84,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f82,f20])).

fof(f20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f82,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_6 ),
    inference(resolution,[],[f77,f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f77,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_6
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f81,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f79,f20])).

fof(f79,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_5 ),
    inference(resolution,[],[f73,f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f73,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f78,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f69,f36,f75,f71])).

fof(f36,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f69,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f47,f38])).

fof(f38,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f47,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f46,f21])).

fof(f21,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f46,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != sK1
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f44,f23])).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f44,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != sK1
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f18,f22])).

fof(f22,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f18,plain,(
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

fof(f67,plain,
    ( spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f65,f37])).

fof(f37,plain,
    ( k1_xboole_0 != sK1
    | spl4_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f65,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0 )
    | ~ spl4_4 ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = X0 )
    | ~ spl4_4 ),
    inference(superposition,[],[f58,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
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

fof(f58,plain,
    ( ! [X0] :
        ( sK1 != k1_relat_1(sK2(X0,sK3(sK0)))
        | k1_xboole_0 = X0 )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_4
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | sK1 != k1_relat_1(sK2(X0,sK3(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f62,plain,
    ( spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f60,f42])).

fof(f42,plain,
    ( k1_xboole_0 != sK0
    | spl4_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f60,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_3 ),
    inference(resolution,[],[f55,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f55,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f59,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f51,f57,f53])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | sK1 != k1_relat_1(sK2(X0,sK3(sK0)))
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f50,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = X0
      | sK1 != k1_relat_1(sK2(X0,X1)) ) ),
    inference(resolution,[],[f49,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != k1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f48,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != k1_relat_1(sK2(X0,X1))
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f45,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | ~ v1_funct_1(sK2(X0,X1))
      | sK1 != k1_relat_1(sK2(X0,X1))
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f18,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f19,f40,f36])).

fof(f19,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:57:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (26998)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (27000)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (26998)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f43,f59,f62,f67,f78,f81,f84])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl4_6),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f83])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    $false | spl4_6),
% 0.22/0.48    inference(subsumption_resolution,[],[f82,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ~v1_xboole_0(k1_xboole_0) | spl4_6),
% 0.22/0.48    inference(resolution,[],[f77,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ~v1_funct_1(k1_xboole_0) | spl4_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    spl4_6 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    spl4_5),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f80])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    $false | spl4_5),
% 0.22/0.48    inference(subsumption_resolution,[],[f79,f20])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ~v1_xboole_0(k1_xboole_0) | spl4_5),
% 0.22/0.48    inference(resolution,[],[f73,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ~v1_relat_1(k1_xboole_0) | spl4_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f71])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl4_5 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ~spl4_5 | ~spl4_6 | ~spl4_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f69,f36,f75,f71])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    spl4_1 <=> k1_xboole_0 = sK1),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl4_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f47,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    k1_xboole_0 = sK1 | ~spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f36])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    k1_xboole_0 != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(forward_demodulation,[],[f46,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ~v1_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != sK1 | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f44,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != sK1 | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(superposition,[],[f18,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.48    inference(negated_conjecture,[],[f10])).
% 0.22/0.48  fof(f10,conjecture,(
% 0.22/0.48    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl4_1 | ~spl4_4),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f66])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    $false | (spl4_1 | ~spl4_4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f65,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    k1_xboole_0 != sK1 | spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f36])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    k1_xboole_0 = sK1 | ~spl4_4),
% 0.22/0.48    inference(equality_resolution,[],[f64])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = X0) ) | ~spl4_4),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = X0 | k1_xboole_0 = X0) ) | ~spl4_4),
% 0.22/0.48    inference(superposition,[],[f58,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X0] : (sK1 != k1_relat_1(sK2(X0,sK3(sK0))) | k1_xboole_0 = X0) ) | ~spl4_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    spl4_4 <=> ! [X0] : (k1_xboole_0 = X0 | sK1 != k1_relat_1(sK2(X0,sK3(sK0))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl4_2 | ~spl4_3),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    $false | (spl4_2 | ~spl4_3)),
% 0.22/0.48    inference(subsumption_resolution,[],[f60,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    k1_xboole_0 != sK0 | spl4_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    spl4_2 <=> k1_xboole_0 = sK0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    k1_xboole_0 = sK0 | ~spl4_3),
% 0.22/0.48    inference(resolution,[],[f55,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    v1_xboole_0(sK0) | ~spl4_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    spl4_3 <=> v1_xboole_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    spl4_3 | spl4_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f51,f57,f53])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = X0 | sK1 != k1_relat_1(sK2(X0,sK3(sK0))) | v1_xboole_0(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f50,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | k1_xboole_0 = X0 | sK1 != k1_relat_1(sK2(X0,X1))) )),
% 0.22/0.48    inference(resolution,[],[f49,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f48,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f45,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | ~v1_funct_1(sK2(X0,X1)) | sK1 != k1_relat_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(superposition,[],[f18,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    spl4_1 | ~spl4_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f40,f36])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (26998)------------------------------
% 0.22/0.48  % (26998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (26998)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (26998)Memory used [KB]: 10618
% 0.22/0.48  % (26998)Time elapsed: 0.033 s
% 0.22/0.48  % (26998)------------------------------
% 0.22/0.48  % (26998)------------------------------
% 0.22/0.49  % (26994)Success in time 0.119 s
%------------------------------------------------------------------------------
