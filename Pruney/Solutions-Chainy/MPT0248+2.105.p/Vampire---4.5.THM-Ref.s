%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 107 expanded)
%              Number of leaves         :   15 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :  180 ( 378 expanded)
%              Number of equality atoms :   91 ( 254 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f67,f76,f84,f89,f106,f128,f135,f169,f177])).

fof(f177,plain,
    ( spl4_10
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f174,f132,f73,f125])).

fof(f125,plain,
    ( spl4_10
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f73,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f132,plain,
    ( spl4_11
  <=> k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f174,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f172,f32])).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f172,plain,
    ( k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f134,f74])).

fof(f74,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f134,plain,
    ( k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f169,plain,
    ( ~ spl4_1
    | spl4_3
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl4_1
    | spl4_3
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f51,f75,f66,f104])).

fof(f104,plain,
    ( ! [X0] :
        ( k1_tarski(sK0) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f77,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f77,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_tarski(sK0))
        | ~ r1_tarski(X0,sK2) )
    | ~ spl4_1 ),
    inference(superposition,[],[f46,f57])).

fof(f57,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_1
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f66,plain,
    ( sK2 != k1_tarski(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_3
  <=> sK2 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f75,plain,
    ( k1_xboole_0 != sK2
    | spl4_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f135,plain,
    ( spl4_11
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f129,f60,f55,f132])).

fof(f60,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f129,plain,
    ( k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f57,f61])).

fof(f61,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f128,plain,
    ( ~ spl4_10
    | ~ spl4_2
    | spl4_4 ),
    inference(avatar_split_clause,[],[f122,f69,f60,f125])).

fof(f69,plain,
    ( spl4_4
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f122,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | ~ spl4_2
    | spl4_4 ),
    inference(forward_demodulation,[],[f71,f61])).

fof(f71,plain,
    ( sK1 != k1_tarski(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f106,plain,
    ( spl4_4
    | spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f86,f81,f60,f69])).

fof(f81,plain,
    ( spl4_6
  <=> r1_tarski(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f86,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_tarski(sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f83,f43])).

fof(f83,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f89,plain,
    ( ~ spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f28,f64,f69])).

fof(f28,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f84,plain,
    ( spl4_6
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f79,f55,f81])).

fof(f79,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl4_1 ),
    inference(superposition,[],[f34,f57])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f76,plain,
    ( ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f30,f73,f69])).

fof(f30,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,
    ( ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f29,f64,f60])).

fof(f29,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f27,f55])).

fof(f27,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:36:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.50  % (7467)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (7444)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (7451)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (7451)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f178,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f58,f67,f76,f84,f89,f106,f128,f135,f169,f177])).
% 0.20/0.52  fof(f177,plain,(
% 0.20/0.52    spl4_10 | ~spl4_5 | ~spl4_11),
% 0.20/0.52    inference(avatar_split_clause,[],[f174,f132,f73,f125])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    spl4_10 <=> k1_xboole_0 = k1_tarski(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    spl4_5 <=> k1_xboole_0 = sK2),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    spl4_11 <=> k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.52  fof(f174,plain,(
% 0.20/0.52    k1_xboole_0 = k1_tarski(sK0) | (~spl4_5 | ~spl4_11)),
% 0.20/0.52    inference(forward_demodulation,[],[f172,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl4_5 | ~spl4_11)),
% 0.20/0.52    inference(backward_demodulation,[],[f134,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    k1_xboole_0 = sK2 | ~spl4_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f73])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) | ~spl4_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f132])).
% 0.20/0.52  fof(f169,plain,(
% 0.20/0.52    ~spl4_1 | spl4_3 | spl4_5),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f157])).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    $false | (~spl4_1 | spl4_3 | spl4_5)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f51,f75,f66,f104])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(sK0) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,sK2)) ) | ~spl4_1),
% 0.20/0.52    inference(resolution,[],[f77,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.52    inference(flattening,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(X0,k1_tarski(sK0)) | ~r1_tarski(X0,sK2)) ) | ~spl4_1),
% 0.20/0.52    inference(superposition,[],[f46,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) | ~spl4_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    spl4_1 <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    sK2 != k1_tarski(sK0) | spl4_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    spl4_3 <=> sK2 = k1_tarski(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    k1_xboole_0 != sK2 | spl4_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f73])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(flattening,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    spl4_11 | ~spl4_1 | ~spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f129,f60,f55,f132])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    spl4_2 <=> k1_xboole_0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) | (~spl4_1 | ~spl4_2)),
% 0.20/0.52    inference(forward_demodulation,[],[f57,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | ~spl4_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f60])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    ~spl4_10 | ~spl4_2 | spl4_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f122,f69,f60,f125])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    spl4_4 <=> sK1 = k1_tarski(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    k1_xboole_0 != k1_tarski(sK0) | (~spl4_2 | spl4_4)),
% 0.20/0.52    inference(forward_demodulation,[],[f71,f61])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    sK1 != k1_tarski(sK0) | spl4_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f69])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    spl4_4 | spl4_2 | ~spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f86,f81,f60,f69])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    spl4_6 <=> r1_tarski(sK1,k1_tarski(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | sK1 = k1_tarski(sK0) | ~spl4_6),
% 0.20/0.52    inference(resolution,[],[f83,f43])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    r1_tarski(sK1,k1_tarski(sK0)) | ~spl4_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f81])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    ~spl4_4 | ~spl4_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f28,f64,f69])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.52    inference(negated_conjecture,[],[f12])).
% 0.20/0.52  fof(f12,conjecture,(
% 0.20/0.52    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    spl4_6 | ~spl4_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f79,f55,f81])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    r1_tarski(sK1,k1_tarski(sK0)) | ~spl4_1),
% 0.20/0.52    inference(superposition,[],[f34,f57])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ~spl4_4 | ~spl4_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f30,f73,f69])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ~spl4_2 | ~spl4_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f29,f64,f60])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    spl4_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f27,f55])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (7451)------------------------------
% 0.20/0.52  % (7451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7451)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (7451)Memory used [KB]: 10746
% 0.20/0.52  % (7451)Time elapsed: 0.087 s
% 0.20/0.52  % (7451)------------------------------
% 0.20/0.52  % (7451)------------------------------
% 0.20/0.52  % (7439)Success in time 0.158 s
%------------------------------------------------------------------------------
