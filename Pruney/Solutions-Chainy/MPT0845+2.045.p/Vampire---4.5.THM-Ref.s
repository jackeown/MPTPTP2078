%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 104 expanded)
%              Number of leaves         :   14 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  150 ( 328 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f167,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f50,f64,f70,f76,f80,f150,f162])).

fof(f162,plain,
    ( ~ spl3_4
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f49,f148])).

fof(f148,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl3_20
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f49,plain,
    ( r2_hidden(sK1(sK1(sK0,sK0),sK0),sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_4
  <=> r2_hidden(sK1(sK1(sK0,sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f150,plain,
    ( spl3_20
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f143,f78,f74,f147])).

fof(f74,plain,
    ( spl3_9
  <=> r2_hidden(sK1(sK2(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f78,plain,
    ( spl3_10
  <=> r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(sK2(sK0),sK0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl3_10 ),
    inference(resolution,[],[f25,f79])).

fof(f79,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK2(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f15])).

fof(f15,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f80,plain,
    ( spl3_10
    | spl3_8 ),
    inference(avatar_split_clause,[],[f72,f68,f78])).

fof(f68,plain,
    ( spl3_8
  <=> r1_xboole_0(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f72,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))
    | spl3_8 ),
    inference(resolution,[],[f69,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f69,plain,
    ( ~ r1_xboole_0(sK2(sK0),sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f76,plain,
    ( spl3_9
    | spl3_8 ),
    inference(avatar_split_clause,[],[f71,f68,f74])).

fof(f71,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK0)
    | spl3_8 ),
    inference(resolution,[],[f69,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,
    ( ~ spl3_8
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f65,f62,f68])).

fof(f62,plain,
    ( spl3_7
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f65,plain,
    ( ~ r1_xboole_0(sK2(sK0),sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f63,f18])).

fof(f18,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r1_xboole_0(X1,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK0)
          | ~ r2_hidden(X1,sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f63,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f56,f48,f62])).

fof(f56,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f49,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK2(X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,
    ( spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f45,f42,f48])).

fof(f42,plain,
    ( spl3_3
  <=> r1_xboole_0(sK1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f45,plain,
    ( r2_hidden(sK1(sK1(sK0,sK0),sK0),sK0)
    | spl3_3 ),
    inference(resolution,[],[f43,f22])).

fof(f43,plain,
    ( ~ r1_xboole_0(sK1(sK0,sK0),sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f44,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f40,f42])).

fof(f40,plain,(
    ~ r1_xboole_0(sK1(sK0,sK0),sK0) ),
    inference(global_subsumption,[],[f17,f38])).

fof(f38,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_xboole_0(sK1(sK0,sK0),sK0) ),
    inference(resolution,[],[f36,f18])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f21,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:57:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (1760)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (1760)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (1769)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (1768)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f44,f50,f64,f70,f76,f80,f150,f162])).
% 0.20/0.48  fof(f162,plain,(
% 0.20/0.48    ~spl3_4 | ~spl3_20),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f156])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    $false | (~spl3_4 | ~spl3_20)),
% 0.20/0.48    inference(subsumption_resolution,[],[f49,f148])).
% 0.20/0.48  fof(f148,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl3_20),
% 0.20/0.48    inference(avatar_component_clause,[],[f147])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    spl3_20 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    r2_hidden(sK1(sK1(sK0,sK0),sK0),sK0) | ~spl3_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    spl3_4 <=> r2_hidden(sK1(sK1(sK0,sK0),sK0),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.48  fof(f150,plain,(
% 0.20/0.48    spl3_20 | ~spl3_9 | ~spl3_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f143,f78,f74,f147])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    spl3_9 <=> r2_hidden(sK1(sK2(sK0),sK0),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    spl3_10 <=> r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(sK1(sK2(sK0),sK0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl3_10),
% 0.20/0.48    inference(resolution,[],[f25,f79])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) | ~spl3_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f78])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    spl3_10 | spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f72,f68,f78])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    spl3_8 <=> r1_xboole_0(sK2(sK0),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) | spl3_8),
% 0.20/0.48    inference(resolution,[],[f69,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    ~r1_xboole_0(sK2(sK0),sK0) | spl3_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f68])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    spl3_9 | spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f71,f68,f74])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    r2_hidden(sK1(sK2(sK0),sK0),sK0) | spl3_8),
% 0.20/0.48    inference(resolution,[],[f69,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ~spl3_8 | ~spl3_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f65,f62,f68])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    spl3_7 <=> r2_hidden(sK2(sK0),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ~r1_xboole_0(sK2(sK0),sK0) | ~spl3_7),
% 0.20/0.48    inference(resolution,[],[f63,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.48    inference(negated_conjecture,[],[f4])).
% 0.20/0.48  fof(f4,conjecture,(
% 0.20/0.48    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    r2_hidden(sK2(sK0),sK0) | ~spl3_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f62])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    spl3_7 | ~spl3_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f56,f48,f62])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    r2_hidden(sK2(sK0),sK0) | ~spl3_4),
% 0.20/0.48    inference(resolution,[],[f49,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK2(X1),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    spl3_4 | spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f45,f42,f48])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    spl3_3 <=> r1_xboole_0(sK1(sK0,sK0),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    r2_hidden(sK1(sK1(sK0,sK0),sK0),sK0) | spl3_3),
% 0.20/0.48    inference(resolution,[],[f43,f22])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ~r1_xboole_0(sK1(sK0,sK0),sK0) | spl3_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f42])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ~spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f40,f42])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ~r1_xboole_0(sK1(sK0,sK0),sK0)),
% 0.20/0.48    inference(global_subsumption,[],[f17,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | ~r1_xboole_0(sK1(sK0,sK0),sK0)),
% 0.20/0.48    inference(resolution,[],[f36,f18])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK1(X0,X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(resolution,[],[f21,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    k1_xboole_0 != sK0),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (1760)------------------------------
% 0.20/0.48  % (1760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (1760)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (1760)Memory used [KB]: 10618
% 0.20/0.48  % (1760)Time elapsed: 0.065 s
% 0.20/0.48  % (1760)------------------------------
% 0.20/0.48  % (1760)------------------------------
% 0.20/0.48  % (1753)Success in time 0.121 s
%------------------------------------------------------------------------------
