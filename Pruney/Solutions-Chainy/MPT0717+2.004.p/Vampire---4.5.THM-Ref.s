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
% DateTime   : Thu Dec  3 12:54:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  82 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  146 ( 254 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f52,f57,f132,f137])).

fof(f137,plain,
    ( spl5_5
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl5_5
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f134,f56])).

fof(f56,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK2),sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_5
  <=> r2_hidden(k1_funct_1(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f134,plain,
    ( r2_hidden(k1_funct_1(sK1,sK2),sK0)
    | ~ spl5_13 ),
    inference(resolution,[],[f131,f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f131,plain,
    ( sP4(k1_funct_1(sK1,sK2),sK0,k2_relat_1(sK1))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_13
  <=> sP4(k1_funct_1(sK1,sK2),sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f132,plain,
    ( spl5_13
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f119,f49,f42,f37,f32,f129])).

fof(f32,plain,
    ( spl5_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f37,plain,
    ( spl5_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f42,plain,
    ( spl5_3
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f49,plain,
    ( spl5_4
  <=> r2_hidden(sK2,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f119,plain,
    ( sP4(k1_funct_1(sK1,sK2),sK0,k2_relat_1(sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f100,f44])).

fof(f44,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK1,X0)
        | sP4(k1_funct_1(sK1,sK2),X0,k2_relat_1(sK1)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f80,f51])).

fof(f51,plain,
    ( r2_hidden(sK2,k1_relat_1(sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v5_relat_1(sK1,X1)
        | sP4(k1_funct_1(sK1,X0),X1,k2_relat_1(sK1)) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f79,f34])).

fof(f34,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( sP4(k1_funct_1(sK1,X0),X1,k2_relat_1(sK1))
        | ~ v5_relat_1(sK1,X1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f78,f39])).

fof(f39,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( sP4(k1_funct_1(sK1,X0),X1,k2_relat_1(sK1))
        | ~ v5_relat_1(sK1,X1)
        | ~ v1_funct_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f69,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK1))
        | sP4(X1,X0,k2_relat_1(sK1))
        | ~ v5_relat_1(sK1,X0) )
    | ~ spl5_1 ),
    inference(superposition,[],[f29,f59])).

fof(f59,plain,
    ( ! [X0] :
        ( k2_relat_1(sK1) = k3_xboole_0(k2_relat_1(sK1),X0)
        | ~ v5_relat_1(sK1,X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f47,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f47,plain,
    ( ! [X1] :
        ( r1_tarski(k2_relat_1(sK1),X1)
        | ~ v5_relat_1(sK1,X1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f34,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f57,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f14,f54])).

fof(f14,plain,(
    ~ r2_hidden(k1_funct_1(sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( r2_hidden(X2,k1_relat_1(X1))
           => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(f52,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f13,f49])).

fof(f13,plain,(
    r2_hidden(sK2,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f45,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f16,f42])).

fof(f16,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:21:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (10401)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (10406)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (10394)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (10392)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (10390)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (10392)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f35,f40,f45,f52,f57,f132,f137])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl5_5 | ~spl5_13),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f136])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    $false | (spl5_5 | ~spl5_13)),
% 0.21/0.49    inference(subsumption_resolution,[],[f134,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK1,sK2),sK0) | spl5_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl5_5 <=> r2_hidden(k1_funct_1(sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    r2_hidden(k1_funct_1(sK1,sK2),sK0) | ~spl5_13),
% 0.21/0.49    inference(resolution,[],[f131,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    sP4(k1_funct_1(sK1,sK2),sK0,k2_relat_1(sK1)) | ~spl5_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f129])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    spl5_13 <=> sP4(k1_funct_1(sK1,sK2),sK0,k2_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl5_13 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f119,f49,f42,f37,f32,f129])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    spl5_1 <=> v1_relat_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    spl5_2 <=> v1_funct_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    spl5_3 <=> v5_relat_1(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl5_4 <=> r2_hidden(sK2,k1_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    sP4(k1_funct_1(sK1,sK2),sK0,k2_relat_1(sK1)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.21/0.49    inference(resolution,[],[f100,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    v5_relat_1(sK1,sK0) | ~spl5_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f42])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X0] : (~v5_relat_1(sK1,X0) | sP4(k1_funct_1(sK1,sK2),X0,k2_relat_1(sK1))) ) | (~spl5_1 | ~spl5_2 | ~spl5_4)),
% 0.21/0.49    inference(resolution,[],[f80,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    r2_hidden(sK2,k1_relat_1(sK1)) | ~spl5_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f49])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v5_relat_1(sK1,X1) | sP4(k1_funct_1(sK1,X0),X1,k2_relat_1(sK1))) ) | (~spl5_1 | ~spl5_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f79,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    v1_relat_1(sK1) | ~spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f32])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sP4(k1_funct_1(sK1,X0),X1,k2_relat_1(sK1)) | ~v5_relat_1(sK1,X1) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | (~spl5_1 | ~spl5_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f78,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    v1_funct_1(sK1) | ~spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f37])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sP4(k1_funct_1(sK1,X0),X1,k2_relat_1(sK1)) | ~v5_relat_1(sK1,X1) | ~v1_funct_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | ~spl5_1),
% 0.21/0.49    inference(resolution,[],[f69,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | sP4(X1,X0,k2_relat_1(sK1)) | ~v5_relat_1(sK1,X0)) ) | ~spl5_1),
% 0.21/0.49    inference(superposition,[],[f29,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0] : (k2_relat_1(sK1) = k3_xboole_0(k2_relat_1(sK1),X0) | ~v5_relat_1(sK1,X0)) ) | ~spl5_1),
% 0.21/0.49    inference(resolution,[],[f47,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(k2_relat_1(sK1),X1) | ~v5_relat_1(sK1,X1)) ) | ~spl5_1),
% 0.21/0.49    inference(resolution,[],[f34,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | sP4(X3,X1,X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ~spl5_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f14,f54])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK1,sK2),sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),X0) & r2_hidden(X2,k1_relat_1(X1))) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),X0) & r2_hidden(X2,k1_relat_1(X1))) & (v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl5_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f13,f49])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    r2_hidden(sK2,k1_relat_1(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f16,f42])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    v5_relat_1(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f17,f37])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    v1_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    spl5_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f15,f32])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (10392)------------------------------
% 0.21/0.49  % (10392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10392)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (10392)Memory used [KB]: 10618
% 0.21/0.49  % (10392)Time elapsed: 0.085 s
% 0.21/0.49  % (10392)------------------------------
% 0.21/0.49  % (10392)------------------------------
% 0.21/0.50  % (10393)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (10388)Success in time 0.143 s
%------------------------------------------------------------------------------
