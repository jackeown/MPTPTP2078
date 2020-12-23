%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  88 expanded)
%              Number of leaves         :   12 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  147 ( 239 expanded)
%              Number of equality atoms :   16 (  31 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f47,f54,f59,f67,f73,f134,f146])).

fof(f146,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_4
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_4
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f141,f53])).

fof(f53,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl5_4
  <=> k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f141,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(resolution,[],[f133,f42])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
        | k1_funct_1(k7_relat_1(sK2,X1),X0) = k1_funct_1(sK2,X0) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f41,f31])).

fof(f31,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl5_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f41,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
        | k1_funct_1(k7_relat_1(sK2,X1),X0) = k1_funct_1(sK2,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f36,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

fof(f36,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl5_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f133,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl5_13
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f134,plain,
    ( spl5_13
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f119,f70,f64,f29,f131])).

fof(f64,plain,
    ( spl5_6
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f70,plain,
    ( spl5_7
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f119,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(resolution,[],[f78,f66])).

fof(f66,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,X0))) )
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(resolution,[],[f40,f72])).

fof(f72,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f40,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,k1_relat_1(sK2))
        | ~ r2_hidden(X4,X5)
        | r2_hidden(X4,k1_relat_1(k7_relat_1(sK2,X5))) )
    | ~ spl5_1 ),
    inference(resolution,[],[f31,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f73,plain,
    ( spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f60,f56,f70])).

fof(f56,plain,
    ( spl5_5
  <=> sP4(sK0,sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f60,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl5_5 ),
    inference(resolution,[],[f58,f20])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f58,plain,
    ( sP4(sK0,sK1,k1_relat_1(sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f67,plain,
    ( spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f61,f56,f64])).

fof(f61,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f58,f21])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f59,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f48,f44,f56])).

fof(f44,plain,
    ( spl5_3
  <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f48,plain,
    ( sP4(sK0,sK1,k1_relat_1(sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f46,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f54,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f14,f51])).

fof(f14,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

fof(f47,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f13,f44])).

fof(f13,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f37,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f12,f34])).

fof(f12,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f11,f29])).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:22:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (29927)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (29927)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f32,f37,f47,f54,f59,f67,f73,f134,f146])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ~spl5_1 | ~spl5_2 | spl5_4 | ~spl5_13),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f145])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    $false | (~spl5_1 | ~spl5_2 | spl5_4 | ~spl5_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f141,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) | spl5_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl5_4 <=> k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0) | (~spl5_1 | ~spl5_2 | ~spl5_13)),
% 0.21/0.48    inference(resolution,[],[f133,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) | k1_funct_1(k7_relat_1(sK2,X1),X0) = k1_funct_1(sK2,X0)) ) | (~spl5_1 | ~spl5_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f41,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl5_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    spl5_1 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(sK2) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) | k1_funct_1(k7_relat_1(sK2,X1),X0) = k1_funct_1(sK2,X0)) ) | ~spl5_2),
% 0.21/0.48    inference(resolution,[],[f36,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    v1_funct_1(sK2) | ~spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    spl5_2 <=> v1_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | ~spl5_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f131])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl5_13 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl5_13 | ~spl5_1 | ~spl5_6 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f119,f70,f64,f29,f131])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl5_6 <=> r2_hidden(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl5_7 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | (~spl5_1 | ~spl5_6 | ~spl5_7)),
% 0.21/0.48    inference(resolution,[],[f78,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    r2_hidden(sK0,sK1) | ~spl5_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK0,X0) | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,X0)))) ) | (~spl5_1 | ~spl5_7)),
% 0.21/0.48    inference(resolution,[],[f40,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl5_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f70])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~r2_hidden(X4,k1_relat_1(sK2)) | ~r2_hidden(X4,X5) | r2_hidden(X4,k1_relat_1(k7_relat_1(sK2,X5)))) ) | ~spl5_1),
% 0.21/0.48    inference(resolution,[],[f31,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl5_7 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f60,f56,f70])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl5_5 <=> sP4(sK0,sK1,k1_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl5_5),
% 0.21/0.48    inference(resolution,[],[f58,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    sP4(sK0,sK1,k1_relat_1(sK2)) | ~spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f56])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl5_6 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f61,f56,f64])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    r2_hidden(sK0,sK1) | ~spl5_5),
% 0.21/0.48    inference(resolution,[],[f58,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl5_5 | ~spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f48,f44,f56])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl5_3 <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    sP4(sK0,sK1,k1_relat_1(sK2)) | ~spl5_3),
% 0.21/0.48    inference(resolution,[],[f46,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | sP4(X3,X1,X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) | ~spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f44])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f14,f51])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f13,f44])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f12,f34])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f11,f29])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (29927)------------------------------
% 0.21/0.48  % (29927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (29927)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (29927)Memory used [KB]: 10618
% 0.21/0.48  % (29927)Time elapsed: 0.070 s
% 0.21/0.48  % (29927)------------------------------
% 0.21/0.48  % (29927)------------------------------
% 0.21/0.48  % (29919)Success in time 0.118 s
%------------------------------------------------------------------------------
