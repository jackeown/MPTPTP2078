%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  74 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 184 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f64,f78,f85])).

% (10705)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (10702)Refutation not found, incomplete strategy% (10702)------------------------------
% (10702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10702)Termination reason: Refutation not found, incomplete strategy

% (10702)Memory used [KB]: 1535
% (10702)Time elapsed: 0.092 s
% (10702)------------------------------
% (10702)------------------------------
fof(f85,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f79,f59,f30])).

fof(f30,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f59,plain,
    ( spl3_3
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f79,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_3 ),
    inference(resolution,[],[f60,f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f60,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f78,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f71,f62,f34,f30])).

fof(f34,plain,
    ( spl3_2
  <=> r1_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f62,plain,
    ( spl3_4
  <=> ! [X0] : ~ r2_hidden(sK2(k1_xboole_0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f71,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f70,f23])).

fof(f70,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f65,f35])).

fof(f35,plain,
    ( r1_setfam_1(sK0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ r1_setfam_1(X1,k1_xboole_0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_4 ),
    inference(resolution,[],[f63,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X1),X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(sK2(X1),X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f17])).

fof(f17,plain,(
    ! [X1] :
      ( ? [X3] : r2_hidden(X3,X1)
     => r2_hidden(sK2(X1),X1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] : r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] : ~ r2_hidden(X3,X1)
            & r2_hidden(X2,X0) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f63,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k1_xboole_0),X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,
    ( spl3_3
    | spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f57,f34,f62,f59])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(k1_xboole_0),X0)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(k1_xboole_0),X0)
        | ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(sK2(k1_xboole_0),X0) )
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f55,f22])).

fof(f22,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(k1_xboole_0),k5_xboole_0(X0,k1_xboole_0))
        | ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(sK2(k1_xboole_0),X0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f39,f35])).

fof(f39,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_setfam_1(X5,X2)
      | ~ r2_hidden(sK2(X2),k5_xboole_0(X3,X2))
      | ~ r2_hidden(X4,X5)
      | ~ r2_hidden(sK2(X2),X3) ) ),
    inference(resolution,[],[f26,f24])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f36,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f34])).

fof(f20,plain,(
    r1_setfam_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != sK0
    & r1_setfam_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK0
      & r1_setfam_1(sK0,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f32,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f30])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (10695)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (10694)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (10697)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (10702)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (10695)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (10703)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f32,f36,f64,f78,f85])).
% 0.21/0.52  % (10705)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.53  % (10702)Refutation not found, incomplete strategy% (10702)------------------------------
% 0.21/0.53  % (10702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10702)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10702)Memory used [KB]: 1535
% 0.21/0.53  % (10702)Time elapsed: 0.092 s
% 0.21/0.53  % (10702)------------------------------
% 0.21/0.53  % (10702)------------------------------
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    spl3_1 | ~spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f79,f59,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    spl3_1 <=> k1_xboole_0 = sK0),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    spl3_3 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | ~spl3_3),
% 0.21/0.53    inference(resolution,[],[f60,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f59])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    spl3_1 | ~spl3_2 | ~spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f71,f62,f34,f30])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    spl3_2 <=> r1_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    spl3_4 <=> ! [X0] : ~r2_hidden(sK2(k1_xboole_0),X0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | (~spl3_2 | ~spl3_4)),
% 0.21/0.53    inference(resolution,[],[f70,f23])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | (~spl3_2 | ~spl3_4)),
% 0.21/0.53    inference(resolution,[],[f65,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    r1_setfam_1(sK0,k1_xboole_0) | ~spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f34])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_setfam_1(X1,k1_xboole_0) | ~r2_hidden(X0,X1)) ) | ~spl3_4),
% 0.21/0.53    inference(resolution,[],[f63,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X2,X0) | ~r1_setfam_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X1] : (? [X3] : r2_hidden(X3,X1) => r2_hidden(sK2(X1),X1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (? [X3] : r2_hidden(X3,X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~r2_hidden(X3,X1) & r2_hidden(X2,X0)))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.53  fof(f7,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.53    inference(unused_predicate_definition_removal,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK2(k1_xboole_0),X0)) ) | ~spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f62])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    spl3_3 | spl3_4 | ~spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f57,f34,f62,f59])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK2(k1_xboole_0),X0) | ~r2_hidden(X1,sK0)) ) | ~spl3_2),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK2(k1_xboole_0),X0) | ~r2_hidden(X1,sK0) | ~r2_hidden(sK2(k1_xboole_0),X0)) ) | ~spl3_2),
% 0.21/0.53    inference(forward_demodulation,[],[f55,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK2(k1_xboole_0),k5_xboole_0(X0,k1_xboole_0)) | ~r2_hidden(X1,sK0) | ~r2_hidden(sK2(k1_xboole_0),X0)) ) | ~spl3_2),
% 0.21/0.53    inference(resolution,[],[f39,f35])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X4,X2,X5,X3] : (~r1_setfam_1(X5,X2) | ~r2_hidden(sK2(X2),k5_xboole_0(X3,X2)) | ~r2_hidden(X4,X5) | ~r2_hidden(sK2(X2),X3)) )),
% 0.21/0.53    inference(resolution,[],[f26,f24])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.21/0.53    inference(nnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f20,f34])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    r1_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0)) => (k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.53    inference(negated_conjecture,[],[f5])).
% 0.21/0.53  fof(f5,conjecture,(
% 0.21/0.53    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ~spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f21,f30])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    k1_xboole_0 != sK0),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (10695)------------------------------
% 0.21/0.53  % (10695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10695)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (10695)Memory used [KB]: 10618
% 0.21/0.53  % (10695)Time elapsed: 0.084 s
% 0.21/0.53  % (10695)------------------------------
% 0.21/0.53  % (10695)------------------------------
% 0.21/0.53  % (10688)Success in time 0.169 s
%------------------------------------------------------------------------------
