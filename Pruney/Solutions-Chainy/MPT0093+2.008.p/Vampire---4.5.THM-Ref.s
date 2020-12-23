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
% DateTime   : Thu Dec  3 12:31:43 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 142 expanded)
%              Number of leaves         :   14 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  221 ( 552 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f45,f49,f54,f70,f74,f119,f126])).

fof(f126,plain,
    ( ~ spl5_6
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f124,f117,f52,f72])).

fof(f72,plain,
    ( spl5_6
  <=> r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f52,plain,
    ( spl5_4
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f117,plain,
    ( spl5_7
  <=> r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f124,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(superposition,[],[f122,f53])).

fof(f53,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f122,plain,
    ( ! [X2] : ~ r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(X2,sK2))
    | ~ spl5_7 ),
    inference(resolution,[],[f118,f36])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f118,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f119,plain,
    ( spl5_1
    | spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f111,f68,f117,f39])).

fof(f39,plain,
    ( spl5_1
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f68,plain,
    ( spl5_5
  <=> r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f111,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK2)
    | r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl5_5 ),
    inference(resolution,[],[f75,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f75,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,X0))
        | r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),X0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f69,f35])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X1)
      | r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f74,plain,
    ( spl5_6
    | spl5_1 ),
    inference(avatar_split_clause,[],[f65,f39,f72])).

fof(f65,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK0)
    | spl5_1 ),
    inference(resolution,[],[f63,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),X0) )
    | spl5_1 ),
    inference(resolution,[],[f60,f40])).

fof(f40,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r2_hidden(sK3(X0,X1),X2) ) ),
    inference(resolution,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,
    ( spl5_5
    | spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f64,f47,f39,f68])).

fof(f47,plain,
    ( spl5_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f64,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK1)
    | spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f63,f48])).

fof(f48,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f54,plain,
    ( spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f50,f43,f52])).

fof(f43,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f50,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f25,f44])).

fof(f44,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f49,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) )
       => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f45,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f23,f43])).

% (25942)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f23,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f24,f39])).

fof(f24,plain,(
    ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 17:57:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (25956)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.50  % (25948)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.18/0.52  % (25941)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.18/0.52  % (25956)Refutation found. Thanks to Tanya!
% 1.18/0.52  % SZS status Theorem for theBenchmark
% 1.18/0.52  % SZS output start Proof for theBenchmark
% 1.18/0.52  fof(f127,plain,(
% 1.18/0.52    $false),
% 1.18/0.52    inference(avatar_sat_refutation,[],[f41,f45,f49,f54,f70,f74,f119,f126])).
% 1.18/0.52  fof(f126,plain,(
% 1.18/0.52    ~spl5_6 | ~spl5_4 | ~spl5_7),
% 1.18/0.52    inference(avatar_split_clause,[],[f124,f117,f52,f72])).
% 1.18/0.52  fof(f72,plain,(
% 1.18/0.52    spl5_6 <=> r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK0)),
% 1.18/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.18/0.52  fof(f52,plain,(
% 1.18/0.52    spl5_4 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 1.18/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.18/0.52  fof(f117,plain,(
% 1.18/0.52    spl5_7 <=> r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK2)),
% 1.18/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.18/0.52  fof(f124,plain,(
% 1.18/0.52    ~r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK0) | (~spl5_4 | ~spl5_7)),
% 1.18/0.52    inference(superposition,[],[f122,f53])).
% 1.18/0.52  fof(f53,plain,(
% 1.18/0.52    sK0 = k4_xboole_0(sK0,sK2) | ~spl5_4),
% 1.18/0.52    inference(avatar_component_clause,[],[f52])).
% 1.18/0.52  fof(f122,plain,(
% 1.18/0.52    ( ! [X2] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(X2,sK2))) ) | ~spl5_7),
% 1.18/0.52    inference(resolution,[],[f118,f36])).
% 1.18/0.52  fof(f36,plain,(
% 1.18/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.18/0.52    inference(equality_resolution,[],[f30])).
% 1.18/0.52  fof(f30,plain,(
% 1.18/0.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.18/0.52    inference(cnf_transformation,[],[f21])).
% 1.18/0.52  fof(f21,plain,(
% 1.18/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.18/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 1.18/0.52  fof(f20,plain,(
% 1.18/0.52    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.18/0.52    introduced(choice_axiom,[])).
% 1.18/0.52  fof(f19,plain,(
% 1.18/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.18/0.52    inference(rectify,[],[f18])).
% 1.18/0.52  fof(f18,plain,(
% 1.18/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.18/0.52    inference(flattening,[],[f17])).
% 1.18/0.52  fof(f17,plain,(
% 1.18/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.18/0.52    inference(nnf_transformation,[],[f2])).
% 1.18/0.52  fof(f2,axiom,(
% 1.18/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.18/0.52  fof(f118,plain,(
% 1.18/0.52    r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK2) | ~spl5_7),
% 1.18/0.52    inference(avatar_component_clause,[],[f117])).
% 1.18/0.52  fof(f119,plain,(
% 1.18/0.52    spl5_1 | spl5_7 | ~spl5_5),
% 1.18/0.52    inference(avatar_split_clause,[],[f111,f68,f117,f39])).
% 1.18/0.52  fof(f39,plain,(
% 1.18/0.52    spl5_1 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.18/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.18/0.52  fof(f68,plain,(
% 1.18/0.52    spl5_5 <=> r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK1)),
% 1.18/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.18/0.52  fof(f111,plain,(
% 1.18/0.52    r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK2) | r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | ~spl5_5),
% 1.18/0.52    inference(resolution,[],[f75,f28])).
% 1.18/0.52  fof(f28,plain,(
% 1.18/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f16])).
% 1.18/0.52  fof(f16,plain,(
% 1.18/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.18/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).
% 1.18/0.52  fof(f15,plain,(
% 1.18/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.18/0.52    introduced(choice_axiom,[])).
% 1.18/0.52  fof(f14,plain,(
% 1.18/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.18/0.52    inference(rectify,[],[f13])).
% 1.18/0.52  fof(f13,plain,(
% 1.18/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.18/0.52    inference(nnf_transformation,[],[f10])).
% 1.18/0.52  fof(f10,plain,(
% 1.18/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.18/0.52    inference(ennf_transformation,[],[f1])).
% 1.18/0.52  fof(f1,axiom,(
% 1.18/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.18/0.52  fof(f75,plain,(
% 1.18/0.52    ( ! [X0] : (r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,X0)) | r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),X0)) ) | ~spl5_5),
% 1.18/0.52    inference(resolution,[],[f69,f35])).
% 1.18/0.52  fof(f35,plain,(
% 1.18/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,X0) | r2_hidden(X4,X1) | r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.18/0.52    inference(equality_resolution,[],[f31])).
% 1.18/0.52  fof(f31,plain,(
% 1.18/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.18/0.52    inference(cnf_transformation,[],[f21])).
% 1.18/0.52  fof(f69,plain,(
% 1.18/0.52    r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK1) | ~spl5_5),
% 1.18/0.52    inference(avatar_component_clause,[],[f68])).
% 1.18/0.52  fof(f74,plain,(
% 1.18/0.52    spl5_6 | spl5_1),
% 1.18/0.52    inference(avatar_split_clause,[],[f65,f39,f72])).
% 1.18/0.52  fof(f65,plain,(
% 1.18/0.52    r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK0) | spl5_1),
% 1.18/0.52    inference(resolution,[],[f63,f56])).
% 1.18/0.52  fof(f56,plain,(
% 1.18/0.52    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.18/0.52    inference(duplicate_literal_removal,[],[f55])).
% 1.18/0.52  fof(f55,plain,(
% 1.18/0.52    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.18/0.52    inference(resolution,[],[f28,f27])).
% 1.18/0.52  fof(f27,plain,(
% 1.18/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f16])).
% 1.18/0.52  fof(f63,plain,(
% 1.18/0.52    ( ! [X0] : (~r1_tarski(sK0,X0) | r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),X0)) ) | spl5_1),
% 1.18/0.52    inference(resolution,[],[f60,f40])).
% 1.18/0.52  fof(f40,plain,(
% 1.18/0.52    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | spl5_1),
% 1.18/0.52    inference(avatar_component_clause,[],[f39])).
% 1.18/0.52  fof(f60,plain,(
% 1.18/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r2_hidden(sK3(X0,X1),X2)) )),
% 1.18/0.52    inference(resolution,[],[f26,f27])).
% 1.18/0.52  fof(f26,plain,(
% 1.18/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f16])).
% 1.18/0.52  fof(f70,plain,(
% 1.18/0.52    spl5_5 | spl5_1 | ~spl5_3),
% 1.18/0.52    inference(avatar_split_clause,[],[f64,f47,f39,f68])).
% 1.18/0.52  fof(f47,plain,(
% 1.18/0.52    spl5_3 <=> r1_tarski(sK0,sK1)),
% 1.18/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.18/0.52  fof(f64,plain,(
% 1.18/0.52    r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK1) | (spl5_1 | ~spl5_3)),
% 1.18/0.52    inference(resolution,[],[f63,f48])).
% 1.18/0.52  fof(f48,plain,(
% 1.18/0.52    r1_tarski(sK0,sK1) | ~spl5_3),
% 1.18/0.52    inference(avatar_component_clause,[],[f47])).
% 1.18/0.52  fof(f54,plain,(
% 1.18/0.52    spl5_4 | ~spl5_2),
% 1.18/0.52    inference(avatar_split_clause,[],[f50,f43,f52])).
% 1.18/0.52  fof(f43,plain,(
% 1.18/0.52    spl5_2 <=> r1_xboole_0(sK0,sK2)),
% 1.18/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.18/0.52  fof(f50,plain,(
% 1.18/0.52    sK0 = k4_xboole_0(sK0,sK2) | ~spl5_2),
% 1.18/0.52    inference(resolution,[],[f25,f44])).
% 1.18/0.52  fof(f44,plain,(
% 1.18/0.52    r1_xboole_0(sK0,sK2) | ~spl5_2),
% 1.18/0.52    inference(avatar_component_clause,[],[f43])).
% 1.18/0.52  fof(f25,plain,(
% 1.18/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.18/0.52    inference(cnf_transformation,[],[f9])).
% 1.18/0.52  fof(f9,plain,(
% 1.18/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.18/0.52    inference(ennf_transformation,[],[f6])).
% 1.18/0.52  fof(f6,plain,(
% 1.18/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 1.18/0.52    inference(unused_predicate_definition_removal,[],[f3])).
% 1.18/0.52  fof(f3,axiom,(
% 1.18/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.18/0.52  fof(f49,plain,(
% 1.18/0.52    spl5_3),
% 1.18/0.52    inference(avatar_split_clause,[],[f22,f47])).
% 1.18/0.52  fof(f22,plain,(
% 1.18/0.52    r1_tarski(sK0,sK1)),
% 1.18/0.52    inference(cnf_transformation,[],[f12])).
% 1.18/0.52  fof(f12,plain,(
% 1.18/0.52    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,sK1)),
% 1.18/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).
% 1.18/0.52  fof(f11,plain,(
% 1.18/0.52    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => (~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,sK1))),
% 1.18/0.52    introduced(choice_axiom,[])).
% 1.18/0.52  fof(f8,plain,(
% 1.18/0.52    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & r1_tarski(X0,X1))),
% 1.18/0.52    inference(flattening,[],[f7])).
% 1.18/0.52  fof(f7,plain,(
% 1.18/0.52    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.18/0.52    inference(ennf_transformation,[],[f5])).
% 1.18/0.52  fof(f5,negated_conjecture,(
% 1.18/0.52    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.18/0.52    inference(negated_conjecture,[],[f4])).
% 1.18/0.52  fof(f4,conjecture,(
% 1.18/0.52    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.18/0.52  fof(f45,plain,(
% 1.18/0.52    spl5_2),
% 1.18/0.52    inference(avatar_split_clause,[],[f23,f43])).
% 1.18/0.52  % (25942)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.18/0.52  fof(f23,plain,(
% 1.18/0.52    r1_xboole_0(sK0,sK2)),
% 1.18/0.52    inference(cnf_transformation,[],[f12])).
% 1.18/0.52  fof(f41,plain,(
% 1.18/0.52    ~spl5_1),
% 1.18/0.52    inference(avatar_split_clause,[],[f24,f39])).
% 1.18/0.52  fof(f24,plain,(
% 1.18/0.52    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.18/0.52    inference(cnf_transformation,[],[f12])).
% 1.18/0.52  % SZS output end Proof for theBenchmark
% 1.18/0.52  % (25956)------------------------------
% 1.18/0.52  % (25956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (25956)Termination reason: Refutation
% 1.18/0.52  
% 1.18/0.52  % (25956)Memory used [KB]: 10746
% 1.18/0.52  % (25956)Time elapsed: 0.099 s
% 1.18/0.52  % (25956)------------------------------
% 1.18/0.52  % (25956)------------------------------
% 1.18/0.52  % (25936)Success in time 0.153 s
%------------------------------------------------------------------------------
