%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 128 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :  223 ( 365 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f57,f63,f69,f91,f124,f221,f368,f375,f379,f383])).

fof(f383,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_39 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_39 ),
    inference(subsumption_resolution,[],[f381,f44])).

fof(f44,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl5_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f381,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl5_2
    | spl5_39 ),
    inference(subsumption_resolution,[],[f380,f49])).

fof(f49,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl5_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f380,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_39 ),
    inference(resolution,[],[f367,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f367,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK1))
    | spl5_39 ),
    inference(avatar_component_clause,[],[f365])).

fof(f365,plain,
    ( spl5_39
  <=> v1_funct_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f379,plain,
    ( ~ spl5_1
    | ~ spl5_12
    | spl5_38 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_12
    | spl5_38 ),
    inference(subsumption_resolution,[],[f377,f44])).

fof(f377,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl5_12
    | spl5_38 ),
    inference(subsumption_resolution,[],[f376,f123])).

fof(f123,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_12
  <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f376,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    | ~ v1_relat_1(sK2)
    | spl5_38 ),
    inference(superposition,[],[f363,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f363,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | spl5_38 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl5_38
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f375,plain,
    ( ~ spl5_1
    | spl5_37 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | ~ spl5_1
    | spl5_37 ),
    inference(subsumption_resolution,[],[f370,f44])).

fof(f370,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_37 ),
    inference(resolution,[],[f359,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f359,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl5_37 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl5_37
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f368,plain,
    ( ~ spl5_37
    | ~ spl5_38
    | ~ spl5_39
    | spl5_5
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f238,f218,f66,f365,f361,f357])).

fof(f66,plain,
    ( spl5_5
  <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f218,plain,
    ( spl5_23
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f238,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl5_5
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f237,f68])).

fof(f68,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f237,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_funct_1(k7_relat_1(sK2,sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ spl5_23 ),
    inference(superposition,[],[f30,f220])).

fof(f220,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f218])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f221,plain,
    ( spl5_23
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f131,f121,f47,f42,f218])).

fof(f131,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(resolution,[],[f123,f52])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(sK2),X1))
        | k1_funct_1(k7_relat_1(sK2,X1),X0) = k1_funct_1(sK2,X0) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f51,f44])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(sK2),X1))
        | k1_funct_1(k7_relat_1(sK2,X1),X0) = k1_funct_1(sK2,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f49,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

fof(f124,plain,
    ( spl5_12
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f97,f88,f121])).

fof(f88,plain,
    ( spl5_8
  <=> sP4(sK0,sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f97,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    | ~ spl5_8 ),
    inference(resolution,[],[f90,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f90,plain,
    ( sP4(sK0,sK1,k1_relat_1(sK2))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f91,plain,
    ( spl5_8
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f72,f60,f54,f88])).

fof(f54,plain,
    ( spl5_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f60,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f72,plain,
    ( sP4(sK0,sK1,k1_relat_1(sK2))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f64,f56])).

fof(f56,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | sP4(sK0,X0,k1_relat_1(sK2)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f62,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f62,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f69,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f24,f66])).

fof(f24,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r2_hidden(X0,X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
         => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X0,X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
       => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

fof(f63,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f22,f60])).

fof(f22,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f23,f54])).

fof(f23,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:50:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (5788)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (5796)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.48  % (5796)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f384,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f45,f50,f57,f63,f69,f91,f124,f221,f368,f375,f379,f383])).
% 0.22/0.50  fof(f383,plain,(
% 0.22/0.50    ~spl5_1 | ~spl5_2 | spl5_39),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f382])).
% 0.22/0.50  fof(f382,plain,(
% 0.22/0.50    $false | (~spl5_1 | ~spl5_2 | spl5_39)),
% 0.22/0.50    inference(subsumption_resolution,[],[f381,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    v1_relat_1(sK2) | ~spl5_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    spl5_1 <=> v1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.50  fof(f381,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | (~spl5_2 | spl5_39)),
% 0.22/0.50    inference(subsumption_resolution,[],[f380,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    v1_funct_1(sK2) | ~spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    spl5_2 <=> v1_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.50  fof(f380,plain,(
% 0.22/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl5_39),
% 0.22/0.50    inference(resolution,[],[f367,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.22/0.50  fof(f367,plain,(
% 0.22/0.50    ~v1_funct_1(k7_relat_1(sK2,sK1)) | spl5_39),
% 0.22/0.50    inference(avatar_component_clause,[],[f365])).
% 0.22/0.50  fof(f365,plain,(
% 0.22/0.50    spl5_39 <=> v1_funct_1(k7_relat_1(sK2,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.22/0.50  fof(f379,plain,(
% 0.22/0.50    ~spl5_1 | ~spl5_12 | spl5_38),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f378])).
% 0.22/0.50  fof(f378,plain,(
% 0.22/0.50    $false | (~spl5_1 | ~spl5_12 | spl5_38)),
% 0.22/0.50    inference(subsumption_resolution,[],[f377,f44])).
% 0.22/0.50  fof(f377,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | (~spl5_12 | spl5_38)),
% 0.22/0.50    inference(subsumption_resolution,[],[f376,f123])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) | ~spl5_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f121])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    spl5_12 <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.50  fof(f376,plain,(
% 0.22/0.50    ~r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) | ~v1_relat_1(sK2) | spl5_38),
% 0.22/0.50    inference(superposition,[],[f363,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.50  fof(f363,plain,(
% 0.22/0.50    ~r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | spl5_38),
% 0.22/0.50    inference(avatar_component_clause,[],[f361])).
% 0.22/0.50  fof(f361,plain,(
% 0.22/0.50    spl5_38 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.22/0.50  fof(f375,plain,(
% 0.22/0.50    ~spl5_1 | spl5_37),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f374])).
% 0.22/0.50  fof(f374,plain,(
% 0.22/0.50    $false | (~spl5_1 | spl5_37)),
% 0.22/0.50    inference(subsumption_resolution,[],[f370,f44])).
% 0.22/0.50  fof(f370,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | spl5_37),
% 0.22/0.50    inference(resolution,[],[f359,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.50  fof(f359,plain,(
% 0.22/0.50    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl5_37),
% 0.22/0.50    inference(avatar_component_clause,[],[f357])).
% 0.22/0.50  fof(f357,plain,(
% 0.22/0.50    spl5_37 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.22/0.50  fof(f368,plain,(
% 0.22/0.50    ~spl5_37 | ~spl5_38 | ~spl5_39 | spl5_5 | ~spl5_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f238,f218,f66,f365,f361,f357])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl5_5 <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    spl5_23 <=> k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    ~v1_funct_1(k7_relat_1(sK2,sK1)) | ~r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | (spl5_5 | ~spl5_23)),
% 0.22/0.50    inference(subsumption_resolution,[],[f237,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) | spl5_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f66])).
% 0.22/0.50  fof(f237,plain,(
% 0.22/0.50    r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) | ~v1_funct_1(k7_relat_1(sK2,sK1)) | ~r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~spl5_23),
% 0.22/0.50    inference(superposition,[],[f30,f220])).
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) | ~spl5_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f218])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    spl5_23 | ~spl5_1 | ~spl5_2 | ~spl5_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f131,f121,f47,f42,f218])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) | (~spl5_1 | ~spl5_2 | ~spl5_12)),
% 0.22/0.50    inference(resolution,[],[f123,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_relat_1(sK2),X1)) | k1_funct_1(k7_relat_1(sK2,X1),X0) = k1_funct_1(sK2,X0)) ) | (~spl5_1 | ~spl5_2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f51,f44])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(sK2) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(sK2),X1)) | k1_funct_1(k7_relat_1(sK2,X1),X0) = k1_funct_1(sK2,X0)) ) | ~spl5_2),
% 0.22/0.50    inference(resolution,[],[f49,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    spl5_12 | ~spl5_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f97,f88,f121])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl5_8 <=> sP4(sK0,sK1,k1_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) | ~spl5_8),
% 0.22/0.50    inference(resolution,[],[f90,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(equality_resolution,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    sP4(sK0,sK1,k1_relat_1(sK2)) | ~spl5_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f88])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    spl5_8 | ~spl5_3 | ~spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f72,f60,f54,f88])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    spl5_3 <=> r2_hidden(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl5_4 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    sP4(sK0,sK1,k1_relat_1(sK2)) | (~spl5_3 | ~spl5_4)),
% 0.22/0.50    inference(resolution,[],[f64,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    r2_hidden(sK0,sK1) | ~spl5_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f54])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(sK0,X0) | sP4(sK0,X0,k1_relat_1(sK2))) ) | ~spl5_4),
% 0.22/0.50    inference(resolution,[],[f62,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | sP4(X3,X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl5_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f60])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ~spl5_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f24,f66])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & (r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f8])).
% 0.22/0.50  fof(f8,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f22,f60])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f23,f54])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    r2_hidden(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f21,f47])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    v1_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    spl5_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f20,f42])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    v1_relat_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (5796)------------------------------
% 0.22/0.50  % (5796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (5796)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (5796)Memory used [KB]: 11001
% 0.22/0.50  % (5796)Time elapsed: 0.072 s
% 0.22/0.50  % (5796)------------------------------
% 0.22/0.50  % (5796)------------------------------
% 0.22/0.50  % (5775)Success in time 0.135 s
%------------------------------------------------------------------------------
