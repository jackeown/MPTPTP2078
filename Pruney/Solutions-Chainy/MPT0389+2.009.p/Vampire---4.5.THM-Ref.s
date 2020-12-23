%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 110 expanded)
%              Number of leaves         :   17 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :  172 ( 284 expanded)
%              Number of equality atoms :   37 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f47,f73,f85,f98,f110,f123,f129,f134])).

fof(f134,plain,
    ( spl3_1
    | spl3_2
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f130,f127,f41,f37])).

fof(f37,plain,
    ( spl3_1
  <=> r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f41,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f127,plain,
    ( spl3_13
  <=> r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f130,plain,
    ( k1_xboole_0 = sK0
    | r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f128,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK2(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f128,plain,
    ( r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f129,plain,
    ( spl3_13
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f125,f121,f127])).

fof(f121,plain,
    ( spl3_12
  <=> r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f125,plain,
    ( r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1)))
    | ~ spl3_12 ),
    inference(resolution,[],[f122,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f122,plain,
    ( r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,
    ( spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f119,f108,f121])).

fof(f108,plain,
    ( spl3_11
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f119,plain,
    ( r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1)
    | ~ spl3_11 ),
    inference(trivial_inequality_removal,[],[f116])).

fof(f116,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f33,f109])).

fof(f109,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f110,plain,
    ( spl3_11
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f106,f96,f108])).

fof(f96,plain,
    ( spl3_9
  <=> r1_tarski(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f106,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK1)
    | ~ spl3_9 ),
    inference(resolution,[],[f97,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f97,plain,
    ( r1_tarski(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f92,f83,f45,f96])).

fof(f45,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f83,plain,
    ( spl3_7
  <=> r1_tarski(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f92,plain,
    ( r1_tarski(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK1)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f84,f55])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl3_3 ),
    inference(resolution,[],[f35,f46])).

fof(f46,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f84,plain,
    ( r1_tarski(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f85,plain,
    ( spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f76,f70,f83])).

fof(f70,plain,
    ( spl3_5
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f76,plain,
    ( r1_tarski(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK0)
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK0)
    | ~ spl3_5 ),
    inference(superposition,[],[f29,f71])).

fof(f71,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,
    ( spl3_5
    | spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f66,f37,f41,f70])).

fof(f66,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK0)
    | spl3_1 ),
    inference(resolution,[],[f56,f38])).

fof(f38,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK2(X0,X1)),X0) ) ),
    inference(resolution,[],[f27,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    & k1_xboole_0 != sK0
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
      & k1_xboole_0 != sK0
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f43,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f24,f41])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f25,f37])).

fof(f25,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (15317)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (15312)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (15327)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.47  % (15317)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f139,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f39,f43,f47,f73,f85,f98,f110,f123,f129,f134])).
% 0.22/0.47  fof(f134,plain,(
% 0.22/0.47    spl3_1 | spl3_2 | ~spl3_13),
% 0.22/0.47    inference(avatar_split_clause,[],[f130,f127,f41,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    spl3_1 <=> r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    spl3_2 <=> k1_xboole_0 = sK0),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f127,plain,(
% 0.22/0.47    spl3_13 <=> r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.47  fof(f130,plain,(
% 0.22/0.47    k1_xboole_0 = sK0 | r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) | ~spl3_13),
% 0.22/0.47    inference(resolution,[],[f128,f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X1,sK2(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.22/0.47    inference(flattening,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).
% 0.22/0.47  fof(f128,plain,(
% 0.22/0.47    r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1))) | ~spl3_13),
% 0.22/0.47    inference(avatar_component_clause,[],[f127])).
% 0.22/0.47  fof(f129,plain,(
% 0.22/0.47    spl3_13 | ~spl3_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f125,f121,f127])).
% 0.22/0.47  fof(f121,plain,(
% 0.22/0.47    spl3_12 <=> r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.47  fof(f125,plain,(
% 0.22/0.47    r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1))) | ~spl3_12),
% 0.22/0.47    inference(resolution,[],[f122,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.22/0.47  fof(f122,plain,(
% 0.22/0.47    r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1) | ~spl3_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f121])).
% 0.22/0.47  fof(f123,plain,(
% 0.22/0.47    spl3_12 | ~spl3_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f119,f108,f121])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    spl3_11 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1) | ~spl3_11),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f116])).
% 0.22/0.47  fof(f116,plain,(
% 0.22/0.47    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1) | ~spl3_11),
% 0.22/0.47    inference(superposition,[],[f33,f109])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK1) | ~spl3_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f108])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.22/0.47    inference(nnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 0.22/0.47  fof(f110,plain,(
% 0.22/0.47    spl3_11 | ~spl3_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f106,f96,f108])).
% 0.22/0.47  fof(f96,plain,(
% 0.22/0.47    spl3_9 <=> r1_tarski(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.47  fof(f106,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK1) | ~spl3_9),
% 0.22/0.47    inference(resolution,[],[f97,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.47    inference(nnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.47  fof(f97,plain,(
% 0.22/0.47    r1_tarski(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK1) | ~spl3_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f96])).
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    spl3_9 | ~spl3_3 | ~spl3_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f92,f83,f45,f96])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    spl3_7 <=> r1_tarski(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    r1_tarski(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK1) | (~spl3_3 | ~spl3_7)),
% 0.22/0.47    inference(resolution,[],[f84,f55])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,sK1)) ) | ~spl3_3),
% 0.22/0.47    inference(resolution,[],[f35,f46])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f45])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    r1_tarski(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK0) | ~spl3_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f83])).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    spl3_7 | ~spl3_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f76,f70,f83])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    spl3_5 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    r1_tarski(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK0) | ~spl3_5),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f75])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK0) | ~spl3_5),
% 0.22/0.47    inference(superposition,[],[f29,f71])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK0) | ~spl3_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f70])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    spl3_5 | spl3_2 | spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f66,f37,f41,f70])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(k1_tarski(sK2(sK0,k1_setfam_1(sK1))),sK0) | spl3_1),
% 0.22/0.47    inference(resolution,[],[f56,f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) | spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f37])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(k1_tarski(sK2(X0,X1)),X0)) )),
% 0.22/0.47    inference(resolution,[],[f27,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f23,f45])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    r1_tarski(sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r1_tarski(X0,X1)) => (~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r1_tarski(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0,X1] : ((~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0) & r1_tarski(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.22/0.47    inference(negated_conjecture,[],[f7])).
% 0.22/0.47  fof(f7,conjecture,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ~spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f24,f41])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    k1_xboole_0 != sK0),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ~spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f25,f37])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (15317)------------------------------
% 0.22/0.47  % (15317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (15317)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (15317)Memory used [KB]: 10618
% 0.22/0.47  % (15317)Time elapsed: 0.058 s
% 0.22/0.47  % (15317)------------------------------
% 0.22/0.47  % (15317)------------------------------
% 0.22/0.47  % (15310)Success in time 0.112 s
%------------------------------------------------------------------------------
