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
% DateTime   : Thu Dec  3 12:53:13 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 101 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :  171 ( 312 expanded)
%              Number of equality atoms :   39 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f44,f48,f52,f57,f62,f70,f73])).

fof(f73,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f71,f24])).

fof(f24,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl3_1
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f71,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(resolution,[],[f69,f29])).

fof(f29,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl3_2
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
        | k1_funct_1(sK2,X0) = k1_funct_1(k7_relat_1(sK2,X1),X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k1_funct_1(sK2,X0) = k1_funct_1(k7_relat_1(sK2,X1),X0)
        | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f70,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f66,f60,f55,f50,f37,f32,f68])).

fof(f32,plain,
    ( spl3_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f37,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f50,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
        | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f55,plain,
    ( spl3_8
  <=> ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f60,plain,
    ( spl3_9
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK2,X0) = k1_funct_1(k7_relat_1(sK2,X1),X0)
        | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) )
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f65,f56])).

fof(f56,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
        | k1_funct_1(sK2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),sK2),X0) )
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f64,f61])).

fof(f61,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f60])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(sK2),X1))
        | k1_funct_1(sK2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),sK2),X0) )
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f63,f39])).

fof(f39,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(sK2),X1))
        | k1_funct_1(sK2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),sK2),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f51,f34])).

fof(f34,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f51,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        | k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
        | ~ v1_relat_1(X2) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f62,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f58,f46,f37,f60])).

fof(f46,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f58,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(resolution,[],[f47,f39])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f57,plain,
    ( spl3_8
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f53,f42,f37,f55])).

fof(f42,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f53,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(resolution,[],[f43,f39])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f52,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

fof(f48,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f46])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f44,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f40,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f14,f37])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
      & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f27])).

fof(f16,plain,(
    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f22])).

fof(f17,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:18:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (24309)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.13/0.42  % (24312)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.13/0.42  % (24309)Refutation found. Thanks to Tanya!
% 0.13/0.42  % SZS status Theorem for theBenchmark
% 0.13/0.42  % SZS output start Proof for theBenchmark
% 0.13/0.42  fof(f74,plain,(
% 0.13/0.42    $false),
% 0.13/0.42    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f44,f48,f52,f57,f62,f70,f73])).
% 0.13/0.42  fof(f73,plain,(
% 0.13/0.42    spl3_1 | ~spl3_2 | ~spl3_10),
% 0.13/0.42    inference(avatar_contradiction_clause,[],[f72])).
% 0.13/0.42  fof(f72,plain,(
% 0.13/0.42    $false | (spl3_1 | ~spl3_2 | ~spl3_10)),
% 0.13/0.42    inference(subsumption_resolution,[],[f71,f24])).
% 0.13/0.42  fof(f24,plain,(
% 0.13/0.42    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) | spl3_1),
% 0.13/0.42    inference(avatar_component_clause,[],[f22])).
% 0.13/0.42  fof(f22,plain,(
% 0.13/0.42    spl3_1 <=> k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.13/0.42  fof(f71,plain,(
% 0.13/0.42    k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) | (~spl3_2 | ~spl3_10)),
% 0.13/0.42    inference(resolution,[],[f69,f29])).
% 0.13/0.42  fof(f29,plain,(
% 0.13/0.42    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | ~spl3_2),
% 0.13/0.42    inference(avatar_component_clause,[],[f27])).
% 0.13/0.42  fof(f27,plain,(
% 0.13/0.42    spl3_2 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.13/0.42  fof(f69,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) | k1_funct_1(sK2,X0) = k1_funct_1(k7_relat_1(sK2,X1),X0)) ) | ~spl3_10),
% 0.13/0.42    inference(avatar_component_clause,[],[f68])).
% 0.13/0.42  fof(f68,plain,(
% 0.13/0.42    spl3_10 <=> ! [X1,X0] : (k1_funct_1(sK2,X0) = k1_funct_1(k7_relat_1(sK2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.13/0.42  fof(f70,plain,(
% 0.13/0.42    spl3_10 | ~spl3_3 | ~spl3_4 | ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.13/0.42    inference(avatar_split_clause,[],[f66,f60,f55,f50,f37,f32,f68])).
% 0.13/0.42  fof(f32,plain,(
% 0.13/0.42    spl3_3 <=> v1_funct_1(sK2)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.13/0.42  fof(f37,plain,(
% 0.13/0.42    spl3_4 <=> v1_relat_1(sK2)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.13/0.42  fof(f50,plain,(
% 0.13/0.42    spl3_7 <=> ! [X1,X0,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.13/0.42  fof(f55,plain,(
% 0.13/0.42    spl3_8 <=> ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.13/0.42  fof(f60,plain,(
% 0.13/0.42    spl3_9 <=> ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.13/0.42  fof(f66,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k1_funct_1(sK2,X0) = k1_funct_1(k7_relat_1(sK2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))) ) | (~spl3_3 | ~spl3_4 | ~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.13/0.42    inference(forward_demodulation,[],[f65,f56])).
% 0.13/0.42  fof(f56,plain,(
% 0.13/0.42    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | ~spl3_8),
% 0.13/0.42    inference(avatar_component_clause,[],[f55])).
% 0.13/0.42  fof(f65,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) | k1_funct_1(sK2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),sK2),X0)) ) | (~spl3_3 | ~spl3_4 | ~spl3_7 | ~spl3_9)),
% 0.13/0.42    inference(forward_demodulation,[],[f64,f61])).
% 0.13/0.42  fof(f61,plain,(
% 0.13/0.42    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)) ) | ~spl3_9),
% 0.13/0.42    inference(avatar_component_clause,[],[f60])).
% 0.13/0.42  fof(f64,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_relat_1(sK2),X1)) | k1_funct_1(sK2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),sK2),X0)) ) | (~spl3_3 | ~spl3_4 | ~spl3_7)),
% 0.13/0.42    inference(subsumption_resolution,[],[f63,f39])).
% 0.13/0.42  fof(f39,plain,(
% 0.13/0.42    v1_relat_1(sK2) | ~spl3_4),
% 0.13/0.42    inference(avatar_component_clause,[],[f37])).
% 0.13/0.42  fof(f63,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_relat_1(sK2),X1)) | k1_funct_1(sK2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),sK2),X0) | ~v1_relat_1(sK2)) ) | (~spl3_3 | ~spl3_7)),
% 0.13/0.42    inference(resolution,[],[f51,f34])).
% 0.13/0.42  fof(f34,plain,(
% 0.13/0.42    v1_funct_1(sK2) | ~spl3_3),
% 0.13/0.42    inference(avatar_component_clause,[],[f32])).
% 0.13/0.42  fof(f51,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) | k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) | ~v1_relat_1(X2)) ) | ~spl3_7),
% 0.13/0.42    inference(avatar_component_clause,[],[f50])).
% 0.13/0.42  fof(f62,plain,(
% 0.13/0.42    spl3_9 | ~spl3_4 | ~spl3_6),
% 0.13/0.42    inference(avatar_split_clause,[],[f58,f46,f37,f60])).
% 0.13/0.42  fof(f46,plain,(
% 0.13/0.42    spl3_6 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.13/0.42  fof(f58,plain,(
% 0.13/0.42    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)) ) | (~spl3_4 | ~spl3_6)),
% 0.13/0.42    inference(resolution,[],[f47,f39])).
% 0.13/0.42  fof(f47,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) ) | ~spl3_6),
% 0.13/0.42    inference(avatar_component_clause,[],[f46])).
% 0.13/0.42  fof(f57,plain,(
% 0.13/0.42    spl3_8 | ~spl3_4 | ~spl3_5),
% 0.13/0.42    inference(avatar_split_clause,[],[f53,f42,f37,f55])).
% 0.13/0.42  fof(f42,plain,(
% 0.13/0.42    spl3_5 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.13/0.42  fof(f53,plain,(
% 0.13/0.42    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | (~spl3_4 | ~spl3_5)),
% 0.13/0.42    inference(resolution,[],[f43,f39])).
% 0.13/0.42  fof(f43,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl3_5),
% 0.13/0.42    inference(avatar_component_clause,[],[f42])).
% 0.13/0.42  fof(f52,plain,(
% 0.13/0.42    spl3_7),
% 0.13/0.42    inference(avatar_split_clause,[],[f20,f50])).
% 0.13/0.42  fof(f20,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f11])).
% 0.13/0.42  fof(f11,plain,(
% 0.13/0.42    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.13/0.42    inference(flattening,[],[f10])).
% 0.13/0.42  fof(f10,plain,(
% 0.13/0.42    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.13/0.42    inference(ennf_transformation,[],[f3])).
% 0.13/0.42  fof(f3,axiom,(
% 0.13/0.42    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).
% 0.13/0.42  fof(f48,plain,(
% 0.13/0.42    spl3_6),
% 0.13/0.42    inference(avatar_split_clause,[],[f19,f46])).
% 0.13/0.42  fof(f19,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f9])).
% 0.13/0.42  fof(f9,plain,(
% 0.13/0.42    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f1])).
% 0.13/0.42  fof(f1,axiom,(
% 0.13/0.42    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.13/0.42  fof(f44,plain,(
% 0.13/0.42    spl3_5),
% 0.13/0.42    inference(avatar_split_clause,[],[f18,f42])).
% 0.13/0.42  fof(f18,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f8])).
% 0.13/0.42  fof(f8,plain,(
% 0.13/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f2])).
% 0.13/0.42  fof(f2,axiom,(
% 0.13/0.42    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.13/0.42  fof(f40,plain,(
% 0.13/0.42    spl3_4),
% 0.13/0.42    inference(avatar_split_clause,[],[f14,f37])).
% 0.13/0.42  fof(f14,plain,(
% 0.13/0.42    v1_relat_1(sK2)),
% 0.13/0.42    inference(cnf_transformation,[],[f13])).
% 0.13/0.42  fof(f13,plain,(
% 0.13/0.42    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.13/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12])).
% 0.13/0.42  fof(f12,plain,(
% 0.13/0.42    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.13/0.42    introduced(choice_axiom,[])).
% 0.13/0.42  fof(f7,plain,(
% 0.13/0.42    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.13/0.42    inference(flattening,[],[f6])).
% 0.13/0.42  fof(f6,plain,(
% 0.13/0.42    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.13/0.42    inference(ennf_transformation,[],[f5])).
% 0.13/0.42  fof(f5,negated_conjecture,(
% 0.13/0.42    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 0.13/0.42    inference(negated_conjecture,[],[f4])).
% 0.13/0.42  fof(f4,conjecture,(
% 0.13/0.42    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).
% 0.13/0.42  fof(f35,plain,(
% 0.13/0.42    spl3_3),
% 0.13/0.42    inference(avatar_split_clause,[],[f15,f32])).
% 0.13/0.42  fof(f15,plain,(
% 0.13/0.42    v1_funct_1(sK2)),
% 0.13/0.42    inference(cnf_transformation,[],[f13])).
% 0.13/0.42  fof(f30,plain,(
% 0.13/0.42    spl3_2),
% 0.13/0.42    inference(avatar_split_clause,[],[f16,f27])).
% 0.13/0.42  fof(f16,plain,(
% 0.13/0.42    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.13/0.42    inference(cnf_transformation,[],[f13])).
% 0.13/0.42  fof(f25,plain,(
% 0.13/0.42    ~spl3_1),
% 0.13/0.42    inference(avatar_split_clause,[],[f17,f22])).
% 0.13/0.42  fof(f17,plain,(
% 0.13/0.42    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)),
% 0.13/0.42    inference(cnf_transformation,[],[f13])).
% 0.13/0.42  % SZS output end Proof for theBenchmark
% 0.13/0.42  % (24309)------------------------------
% 0.13/0.42  % (24309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.42  % (24309)Termination reason: Refutation
% 0.13/0.42  
% 0.13/0.42  % (24309)Memory used [KB]: 10490
% 0.13/0.42  % (24309)Time elapsed: 0.006 s
% 0.13/0.42  % (24309)------------------------------
% 0.13/0.42  % (24309)------------------------------
% 0.22/0.42  % (24301)Success in time 0.064 s
%------------------------------------------------------------------------------
