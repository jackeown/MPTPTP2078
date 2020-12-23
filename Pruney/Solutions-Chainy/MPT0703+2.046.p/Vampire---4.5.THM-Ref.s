%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 118 expanded)
%              Number of leaves         :   17 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :  197 ( 341 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f295,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f52,f59,f65,f81,f117,f164,f198,f290])).

fof(f290,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | spl3_30 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | spl3_30 ),
    inference(subsumption_resolution,[],[f288,f51])).

fof(f51,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f288,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_4
    | spl3_30 ),
    inference(subsumption_resolution,[],[f286,f46])).

fof(f46,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f286,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_30 ),
    inference(resolution,[],[f197,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f197,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)
    | spl3_30 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl3_30
  <=> r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f198,plain,
    ( ~ spl3_30
    | ~ spl3_3
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f192,f162,f39,f195])).

fof(f39,plain,
    ( spl3_3
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f162,plain,
    ( spl3_24
  <=> ! [X0] :
        ( ~ r1_tarski(k10_relat_1(sK2,sK0),X0)
        | ~ r1_tarski(k9_relat_1(sK2,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f192,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)
    | ~ spl3_3
    | ~ spl3_24 ),
    inference(resolution,[],[f163,f41])).

fof(f41,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k10_relat_1(sK2,sK0),X0)
        | ~ r1_tarski(k9_relat_1(sK2,X0),sK1) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f162])).

fof(f164,plain,
    ( spl3_24
    | ~ spl3_6
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f159,f115,f57,f162])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f115,plain,
    ( spl3_16
  <=> ! [X1] :
        ( r1_tarski(sK0,k9_relat_1(sK2,X1))
        | ~ r1_tarski(k10_relat_1(sK2,sK0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k10_relat_1(sK2,sK0),X0)
        | ~ r1_tarski(k9_relat_1(sK2,X0),sK1) )
    | ~ spl3_6
    | ~ spl3_16 ),
    inference(resolution,[],[f116,f58])).

fof(f58,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f116,plain,
    ( ! [X1] :
        ( r1_tarski(sK0,k9_relat_1(sK2,X1))
        | ~ r1_tarski(k10_relat_1(sK2,sK0),X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f115])).

fof(f117,plain,
    ( spl3_16
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f113,f78,f49,f115])).

fof(f78,plain,
    ( spl3_10
  <=> sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f113,plain,
    ( ! [X1] :
        ( r1_tarski(sK0,k9_relat_1(sK2,X1))
        | ~ r1_tarski(k10_relat_1(sK2,sK0),X1) )
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f100,f51])).

fof(f100,plain,
    ( ! [X1] :
        ( r1_tarski(sK0,k9_relat_1(sK2,X1))
        | ~ r1_tarski(k10_relat_1(sK2,sK0),X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_10 ),
    inference(superposition,[],[f26,f80])).

fof(f80,plain,
    ( sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f81,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f68,f63,f34,f78])).

fof(f34,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f63,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f68,plain,
    ( sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(resolution,[],[f64,f36])).

fof(f36,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f65,plain,
    ( spl3_7
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f61,f49,f44,f63])).

fof(f61,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f60,f51])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl3_4 ),
    inference(resolution,[],[f25,f46])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f59,plain,
    ( spl3_6
    | spl3_1 ),
    inference(avatar_split_clause,[],[f54,f29,f57])).

fof(f29,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f54,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK0,X0) )
    | spl3_1 ),
    inference(resolution,[],[f53,f31])).

fof(f31,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f27,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f52,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f49])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f47,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f34])).

fof(f21,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f22,f29])).

fof(f22,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:14:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (16757)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.43  % (16749)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (16750)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.43  % (16749)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f295,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f52,f59,f65,f81,f117,f164,f198,f290])).
% 0.21/0.43  fof(f290,plain,(
% 0.21/0.43    ~spl3_4 | ~spl3_5 | spl3_30),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f289])).
% 0.21/0.43  fof(f289,plain,(
% 0.21/0.43    $false | (~spl3_4 | ~spl3_5 | spl3_30)),
% 0.21/0.43    inference(subsumption_resolution,[],[f288,f51])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    v1_relat_1(sK2) | ~spl3_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f49])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    spl3_5 <=> v1_relat_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.43  fof(f288,plain,(
% 0.21/0.43    ~v1_relat_1(sK2) | (~spl3_4 | spl3_30)),
% 0.21/0.43    inference(subsumption_resolution,[],[f286,f46])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    v1_funct_1(sK2) | ~spl3_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f44])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    spl3_4 <=> v1_funct_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.43  fof(f286,plain,(
% 0.21/0.43    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_30),
% 0.21/0.43    inference(resolution,[],[f197,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 0.21/0.43  fof(f197,plain,(
% 0.21/0.43    ~r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1) | spl3_30),
% 0.21/0.43    inference(avatar_component_clause,[],[f195])).
% 0.21/0.43  fof(f195,plain,(
% 0.21/0.43    spl3_30 <=> r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.43  fof(f198,plain,(
% 0.21/0.43    ~spl3_30 | ~spl3_3 | ~spl3_24),
% 0.21/0.43    inference(avatar_split_clause,[],[f192,f162,f39,f195])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    spl3_3 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f162,plain,(
% 0.21/0.43    spl3_24 <=> ! [X0] : (~r1_tarski(k10_relat_1(sK2,sK0),X0) | ~r1_tarski(k9_relat_1(sK2,X0),sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.43  fof(f192,plain,(
% 0.21/0.43    ~r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1) | (~spl3_3 | ~spl3_24)),
% 0.21/0.43    inference(resolution,[],[f163,f41])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f39])).
% 0.21/0.43  fof(f163,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(k10_relat_1(sK2,sK0),X0) | ~r1_tarski(k9_relat_1(sK2,X0),sK1)) ) | ~spl3_24),
% 0.21/0.43    inference(avatar_component_clause,[],[f162])).
% 0.21/0.43  fof(f164,plain,(
% 0.21/0.43    spl3_24 | ~spl3_6 | ~spl3_16),
% 0.21/0.43    inference(avatar_split_clause,[],[f159,f115,f57,f162])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    spl3_6 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK0,X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.43  fof(f115,plain,(
% 0.21/0.43    spl3_16 <=> ! [X1] : (r1_tarski(sK0,k9_relat_1(sK2,X1)) | ~r1_tarski(k10_relat_1(sK2,sK0),X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.43  fof(f159,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(k10_relat_1(sK2,sK0),X0) | ~r1_tarski(k9_relat_1(sK2,X0),sK1)) ) | (~spl3_6 | ~spl3_16)),
% 0.21/0.43    inference(resolution,[],[f116,f58])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_tarski(X0,sK1)) ) | ~spl3_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f57])).
% 0.21/0.43  fof(f116,plain,(
% 0.21/0.43    ( ! [X1] : (r1_tarski(sK0,k9_relat_1(sK2,X1)) | ~r1_tarski(k10_relat_1(sK2,sK0),X1)) ) | ~spl3_16),
% 0.21/0.43    inference(avatar_component_clause,[],[f115])).
% 0.21/0.43  fof(f117,plain,(
% 0.21/0.43    spl3_16 | ~spl3_5 | ~spl3_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f113,f78,f49,f115])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    spl3_10 <=> sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    ( ! [X1] : (r1_tarski(sK0,k9_relat_1(sK2,X1)) | ~r1_tarski(k10_relat_1(sK2,sK0),X1)) ) | (~spl3_5 | ~spl3_10)),
% 0.21/0.43    inference(subsumption_resolution,[],[f100,f51])).
% 0.21/0.43  fof(f100,plain,(
% 0.21/0.43    ( ! [X1] : (r1_tarski(sK0,k9_relat_1(sK2,X1)) | ~r1_tarski(k10_relat_1(sK2,sK0),X1) | ~v1_relat_1(sK2)) ) | ~spl3_10),
% 0.21/0.43    inference(superposition,[],[f26,f80])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | ~spl3_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f78])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(flattening,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    spl3_10 | ~spl3_2 | ~spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f68,f63,f34,f78])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    spl3_2 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    spl3_7 <=> ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | (~spl3_2 | ~spl3_7)),
% 0.21/0.43    inference(resolution,[],[f64,f36])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    r1_tarski(sK0,k2_relat_1(sK2)) | ~spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f34])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) ) | ~spl3_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f63])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    spl3_7 | ~spl3_4 | ~spl3_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f61,f49,f44,f63])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) ) | (~spl3_4 | ~spl3_5)),
% 0.21/0.43    inference(subsumption_resolution,[],[f60,f51])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_relat_1(sK2) | ~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) ) | ~spl3_4),
% 0.21/0.43    inference(resolution,[],[f25,f46])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    spl3_6 | spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f54,f29,f57])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK0,X0)) ) | spl3_1),
% 0.21/0.43    inference(resolution,[],[f53,f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f29])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(superposition,[],[f27,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f18,f49])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    v1_relat_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.44    inference(flattening,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.44    inference(negated_conjecture,[],[f6])).
% 0.21/0.44  fof(f6,conjecture,(
% 0.21/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f19,f44])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    v1_funct_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f39])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f34])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ~spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f29])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ~r1_tarski(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (16749)------------------------------
% 0.21/0.44  % (16749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (16749)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (16749)Memory used [KB]: 10746
% 0.21/0.44  % (16749)Time elapsed: 0.012 s
% 0.21/0.44  % (16749)------------------------------
% 0.21/0.44  % (16749)------------------------------
% 0.21/0.44  % (16747)Success in time 0.077 s
%------------------------------------------------------------------------------
