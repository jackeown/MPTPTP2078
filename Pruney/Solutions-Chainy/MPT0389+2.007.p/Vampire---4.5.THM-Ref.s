%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  72 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  125 ( 209 expanded)
%              Number of equality atoms :   19 (  39 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f39,f50,f62])).

fof(f62,plain,
    ( spl3_2
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f60,f48,f29,f33])).

fof(f33,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f29,plain,
    ( spl3_1
  <=> r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f48,plain,
    ( spl3_4
  <=> ! [X5] :
        ( r1_tarski(X5,k1_setfam_1(sK0))
        | r1_tarski(k1_tarski(sK2(sK0,X5)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f60,plain,
    ( r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    | k1_xboole_0 = sK0
    | ~ spl3_4 ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,
    ( r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    | k1_xboole_0 = sK0
    | r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f57,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK2(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f57,plain,
    ( ! [X1] :
        ( r1_tarski(k1_setfam_1(sK1),sK2(sK0,X1))
        | r1_tarski(X1,k1_setfam_1(sK0)) )
    | ~ spl3_4 ),
    inference(resolution,[],[f51,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f51,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK0,X0),sK1)
        | r1_tarski(X0,k1_setfam_1(sK0)) )
    | ~ spl3_4 ),
    inference(resolution,[],[f49,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

% (22018)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f49,plain,
    ( ! [X5] :
        ( r1_tarski(k1_tarski(sK2(sK0,X5)),sK1)
        | r1_tarski(X5,k1_setfam_1(sK0)) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f50,plain,
    ( spl3_2
    | spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f45,f37,f48,f33])).

fof(f37,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f45,plain,
    ( ! [X5] :
        ( r1_tarski(X5,k1_setfam_1(sK0))
        | k1_xboole_0 = sK0
        | r1_tarski(k1_tarski(sK2(sK0,X5)),sK1) )
    | ~ spl3_3 ),
    inference(resolution,[],[f41,f40])).

fof(f40,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl3_3 ),
    inference(resolution,[],[f27,f38])).

fof(f38,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(sK2(X0,X1)),X0)
      | r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f23,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    & k1_xboole_0 != sK0
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
      & k1_xboole_0 != sK0
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f35,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f20,f33])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f29])).

fof(f21,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (22011)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (22008)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (22011)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f31,f35,f39,f50,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl3_2 | spl3_1 | ~spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f60,f48,f29,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    spl3_2 <=> k1_xboole_0 = sK0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    spl3_1 <=> r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    spl3_4 <=> ! [X5] : (r1_tarski(X5,k1_setfam_1(sK0)) | r1_tarski(k1_tarski(sK2(sK0,X5)),sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) | k1_xboole_0 = sK0 | ~spl3_4),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) | k1_xboole_0 = sK0 | r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) | ~spl3_4),
% 0.20/0.47    inference(resolution,[],[f57,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X1,sK2(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X1] : (r1_tarski(k1_setfam_1(sK1),sK2(sK0,X1)) | r1_tarski(X1,k1_setfam_1(sK0))) ) | ~spl3_4),
% 0.20/0.47    inference(resolution,[],[f51,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK2(sK0,X0),sK1) | r1_tarski(X0,k1_setfam_1(sK0))) ) | ~spl3_4),
% 0.20/0.47    inference(resolution,[],[f49,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  % (22018)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X5] : (r1_tarski(k1_tarski(sK2(sK0,X5)),sK1) | r1_tarski(X5,k1_setfam_1(sK0))) ) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f48])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    spl3_2 | spl3_4 | ~spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f45,f37,f48,f33])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X5] : (r1_tarski(X5,k1_setfam_1(sK0)) | k1_xboole_0 = sK0 | r1_tarski(k1_tarski(sK2(sK0,X5)),sK1)) ) | ~spl3_3),
% 0.20/0.47    inference(resolution,[],[f41,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,sK1)) ) | ~spl3_3),
% 0.20/0.47    inference(resolution,[],[f27,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f37])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k1_tarski(sK2(X0,X1)),X0) | r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(resolution,[],[f23,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f37])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r1_tarski(X0,X1)) => (~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ? [X0,X1] : ((~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0) & r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.20/0.47    inference(negated_conjecture,[],[f5])).
% 0.20/0.47  fof(f5,conjecture,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ~spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f33])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    k1_xboole_0 != sK0),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ~spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f21,f29])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (22011)------------------------------
% 0.20/0.47  % (22011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (22011)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (22011)Memory used [KB]: 10618
% 0.20/0.47  % (22011)Time elapsed: 0.064 s
% 0.20/0.47  % (22011)------------------------------
% 0.20/0.47  % (22011)------------------------------
% 0.20/0.47  % (22023)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.48  % (22004)Success in time 0.119 s
%------------------------------------------------------------------------------
