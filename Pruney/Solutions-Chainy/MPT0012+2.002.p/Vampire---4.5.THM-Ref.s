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
% DateTime   : Thu Dec  3 12:29:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 (  73 expanded)
%              Number of leaves         :   12 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  139 ( 208 expanded)
%              Number of equality atoms :   37 (  57 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f25,f33,f48,f52,f56,f70,f92,f190,f209])).

fof(f209,plain,
    ( spl4_7
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl4_7
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(trivial_inequality_removal,[],[f207])).

fof(f207,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl4_7
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f51,f203])).

fof(f203,plain,
    ( ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f202,f91])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1,X1),X0)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(X0,X1,X1),X0)
        | k2_xboole_0(X0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))
        | ~ r2_hidden(sK3(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)),X0) )
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))
        | ~ r2_hidden(sK3(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)),X0)
        | k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) )
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(resolution,[],[f189,f91])).

fof(f189,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r2_hidden(sK3(X4,X5,k2_xboole_0(X6,X7)),X7)
        | k2_xboole_0(X4,X5) = k2_xboole_0(X6,X7)
        | ~ r2_hidden(sK3(X4,X5,k2_xboole_0(X6,X7)),X4) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl4_18
  <=> ! [X5,X7,X4,X6] :
        ( ~ r2_hidden(sK3(X4,X5,k2_xboole_0(X6,X7)),X4)
        | k2_xboole_0(X4,X5) = k2_xboole_0(X6,X7)
        | ~ r2_hidden(sK3(X4,X5,k2_xboole_0(X6,X7)),X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f51,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_7
  <=> k2_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f190,plain,
    ( spl4_18
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f58,f46,f23,f188])).

fof(f23,plain,
    ( spl4_2
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X1)
        | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f46,plain,
    ( spl4_6
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK3(X0,X1,X2),X0)
        | ~ r2_hidden(sK3(X0,X1,X2),X2)
        | k2_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f58,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r2_hidden(sK3(X4,X5,k2_xboole_0(X6,X7)),X4)
        | k2_xboole_0(X4,X5) = k2_xboole_0(X6,X7)
        | ~ r2_hidden(sK3(X4,X5,k2_xboole_0(X6,X7)),X7) )
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(resolution,[],[f47,f24])).

fof(f24,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(X3,k2_xboole_0(X0,X1))
        | ~ r2_hidden(X3,X1) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f47,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1,X2),X2)
        | ~ r2_hidden(sK3(X0,X1,X2),X0)
        | k2_xboole_0(X0,X1) = X2 )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f92,plain,
    ( spl4_12
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f79,f68,f54,f90])).

fof(f54,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK3(X0,X1,X2),X1)
        | ~ r2_hidden(sK3(X0,X1,X2),X2)
        | k2_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f68,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK3(X0,X1,X2),X0)
        | r2_hidden(sK3(X0,X1,X2),X1)
        | r2_hidden(sK3(X0,X1,X2),X2)
        | k2_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1,X1),X0)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f75,f55])).

fof(f55,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1,X2),X2)
        | ~ r2_hidden(sK3(X0,X1,X2),X1)
        | k2_xboole_0(X0,X1) = X2 )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1,X1),X1)
        | r2_hidden(sK3(X0,X1,X1),X0)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl4_10 ),
    inference(factoring,[],[f69])).

% (28280)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK3(X0,X1,X2),X2)
        | r2_hidden(sK3(X0,X1,X2),X1)
        | r2_hidden(sK3(X0,X1,X2),X0)
        | k2_xboole_0(X0,X1) = X2 )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f70,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f10,f68])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f56,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f9,f54])).

fof(f9,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f52,plain,
    ( ~ spl4_7
    | spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f41,f31,f19,f50])).

fof(f19,plain,
    ( spl4_1
  <=> k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f31,plain,
    ( spl4_4
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f41,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl4_1
    | ~ spl4_4 ),
    inference(superposition,[],[f20,f32])).

fof(f32,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f20,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f48,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f8,f46])).

fof(f8,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f33,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f7,f31])).

fof(f7,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f25,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f14,f23])).

fof(f14,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f21,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f17,f19])).

fof(f17,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f6,f7])).

fof(f6,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (28272)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (28268)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (28272)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (28283)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  % (28264)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f211,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f21,f25,f33,f48,f52,f56,f70,f92,f190,f209])).
% 0.20/0.49  fof(f209,plain,(
% 0.20/0.49    spl4_7 | ~spl4_12 | ~spl4_18),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f208])).
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    $false | (spl4_7 | ~spl4_12 | ~spl4_18)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f207])).
% 0.20/0.49  fof(f207,plain,(
% 0.20/0.49    k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (spl4_7 | ~spl4_12 | ~spl4_18)),
% 0.20/0.49    inference(backward_demodulation,[],[f51,f203])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) ) | (~spl4_12 | ~spl4_18)),
% 0.20/0.49    inference(subsumption_resolution,[],[f202,f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) ) | ~spl4_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    spl4_12 <=> ! [X1,X0] : (r2_hidden(sK3(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) | ~r2_hidden(sK3(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)),X0)) ) | (~spl4_12 | ~spl4_18)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f191])).
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) | ~r2_hidden(sK3(X0,k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)),X0) | k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) ) | (~spl4_12 | ~spl4_18)),
% 0.20/0.49    inference(resolution,[],[f189,f91])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    ( ! [X6,X4,X7,X5] : (~r2_hidden(sK3(X4,X5,k2_xboole_0(X6,X7)),X7) | k2_xboole_0(X4,X5) = k2_xboole_0(X6,X7) | ~r2_hidden(sK3(X4,X5,k2_xboole_0(X6,X7)),X4)) ) | ~spl4_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f188])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    spl4_18 <=> ! [X5,X7,X4,X6] : (~r2_hidden(sK3(X4,X5,k2_xboole_0(X6,X7)),X4) | k2_xboole_0(X4,X5) = k2_xboole_0(X6,X7) | ~r2_hidden(sK3(X4,X5,k2_xboole_0(X6,X7)),X7))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    k2_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl4_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    spl4_7 <=> k2_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    spl4_18 | ~spl4_2 | ~spl4_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f58,f46,f23,f188])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    spl4_2 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X1) | r2_hidden(X3,k2_xboole_0(X0,X1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    spl4_6 <=> ! [X1,X0,X2] : (~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X6,X4,X7,X5] : (~r2_hidden(sK3(X4,X5,k2_xboole_0(X6,X7)),X4) | k2_xboole_0(X4,X5) = k2_xboole_0(X6,X7) | ~r2_hidden(sK3(X4,X5,k2_xboole_0(X6,X7)),X7)) ) | (~spl4_2 | ~spl4_6)),
% 0.20/0.49    inference(resolution,[],[f47,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) ) | ~spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f23])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) ) | ~spl4_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f46])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    spl4_12 | ~spl4_8 | ~spl4_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f79,f68,f54,f90])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    spl4_8 <=> ! [X1,X0,X2] : (~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl4_10 <=> ! [X1,X0,X2] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) ) | (~spl4_8 | ~spl4_10)),
% 0.20/0.49    inference(subsumption_resolution,[],[f75,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | k2_xboole_0(X0,X1) = X2) ) | ~spl4_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f54])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | r2_hidden(sK3(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) ) | ~spl4_10),
% 0.20/0.49    inference(factoring,[],[f69])).
% 0.20/0.49  % (28280)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) ) | ~spl4_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f68])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl4_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f10,f68])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl4_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f9,f54])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ~spl4_7 | spl4_1 | ~spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f41,f31,f19,f50])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    spl4_1 <=> k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    spl4_4 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    k2_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (spl4_1 | ~spl4_4)),
% 0.20/0.49    inference(superposition,[],[f20,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f31])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f19])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    spl4_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f8,f46])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f7,f31])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    spl4_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f14,f23])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(equality_resolution,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ~spl4_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f17,f19])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(backward_demodulation,[],[f6,f7])).
% 0.20/0.49  fof(f6,plain,(
% 0.20/0.49    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,plain,(
% 0.20/0.49    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))),
% 0.20/0.49    inference(negated_conjecture,[],[f3])).
% 0.20/0.49  fof(f3,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (28272)------------------------------
% 0.20/0.49  % (28272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (28272)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (28272)Memory used [KB]: 10746
% 0.20/0.49  % (28272)Time elapsed: 0.058 s
% 0.20/0.49  % (28272)------------------------------
% 0.20/0.49  % (28272)------------------------------
% 0.20/0.49  % (28271)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (28261)Success in time 0.132 s
%------------------------------------------------------------------------------
