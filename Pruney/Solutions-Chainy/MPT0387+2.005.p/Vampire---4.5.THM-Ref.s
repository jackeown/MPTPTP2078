%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 (  80 expanded)
%              Number of leaves         :   16 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  153 ( 200 expanded)
%              Number of equality atoms :   41 (  65 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f60,f98,f125,f272])).

fof(f272,plain,
    ( ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f270,f124])).

fof(f124,plain,
    ( r1_tarski(k1_setfam_1(sK1),k1_xboole_0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_11
  <=> r1_tarski(k1_setfam_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f270,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_xboole_0)
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f259,f42])).

fof(f42,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f259,plain,
    ( ! [X0] : ~ r1_tarski(k1_setfam_1(sK1),k2_zfmisc_1(k1_xboole_0,X0))
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f127,f97,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | sP0(X3,X2,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( sP0(X3,X2,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(definition_folding,[],[f12,f13])).

fof(f13,plain,(
    ! [X3,X2,X1] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ sP0(X3,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f97,plain,
    ( r2_hidden(sK2(k1_setfam_1(sK1)),k1_setfam_1(sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_8
  <=> r2_hidden(sK2(k1_setfam_1(sK1)),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f127,plain,(
    ! [X0,X1] : ~ sP0(X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f75,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X0
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( k4_tarski(X3,X4) = X0
          & r2_hidden(X4,X1)
          & r2_hidden(X3,X2) )
     => ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X0
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] :
          ( k4_tarski(X3,X4) = X0
          & r2_hidden(X4,X1)
          & r2_hidden(X3,X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X3,X2,X1] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ sP0(X3,X2,X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f32,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f125,plain,
    ( spl5_11
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f108,f49,f122])).

fof(f49,plain,
    ( spl5_2
  <=> r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f108,plain,
    ( r1_tarski(k1_setfam_1(sK1),k1_xboole_0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f51,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f51,plain,
    ( r2_hidden(k1_xboole_0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f98,plain,
    ( spl5_8
    | spl5_3 ),
    inference(avatar_split_clause,[],[f79,f57,f95])).

fof(f57,plain,
    ( spl5_3
  <=> v1_xboole_0(k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f79,plain,
    ( r2_hidden(sK2(k1_setfam_1(sK1)),k1_setfam_1(sK1))
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f59,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f59,plain,
    ( ~ v1_xboole_0(k1_setfam_1(sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f60,plain,
    ( ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f53,f44,f57])).

fof(f44,plain,
    ( spl5_1
  <=> k1_xboole_0 = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f53,plain,
    ( ~ v1_xboole_0(k1_setfam_1(sK1))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f46,f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f46,plain,
    ( k1_xboole_0 != k1_setfam_1(sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f52,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f27,f49])).

fof(f27,plain,(
    r2_hidden(k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_xboole_0 != k1_setfam_1(sK1)
    & r2_hidden(k1_xboole_0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k1_setfam_1(X0)
        & r2_hidden(k1_xboole_0,X0) )
   => ( k1_xboole_0 != k1_setfam_1(sK1)
      & r2_hidden(k1_xboole_0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_setfam_1(X0)
      & r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k1_setfam_1(X0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_xboole_0 = k1_setfam_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

fof(f47,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f28,f44])).

fof(f28,plain,(
    k1_xboole_0 != k1_setfam_1(sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:29:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.43  % (29798)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.45  % (29791)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (29804)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.46  % (29794)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (29787)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (29787)Refutation not found, incomplete strategy% (29787)------------------------------
% 0.21/0.46  % (29787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (29787)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (29787)Memory used [KB]: 10490
% 0.21/0.46  % (29787)Time elapsed: 0.050 s
% 0.21/0.46  % (29787)------------------------------
% 0.21/0.46  % (29787)------------------------------
% 0.21/0.46  % (29802)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.46  % (29802)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f281,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f47,f52,f60,f98,f125,f272])).
% 0.21/0.46  fof(f272,plain,(
% 0.21/0.46    ~spl5_8 | ~spl5_11),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f271])).
% 0.21/0.46  fof(f271,plain,(
% 0.21/0.46    $false | (~spl5_8 | ~spl5_11)),
% 0.21/0.46    inference(subsumption_resolution,[],[f270,f124])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    r1_tarski(k1_setfam_1(sK1),k1_xboole_0) | ~spl5_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f122])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    spl5_11 <=> r1_tarski(k1_setfam_1(sK1),k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.46  fof(f270,plain,(
% 0.21/0.46    ~r1_tarski(k1_setfam_1(sK1),k1_xboole_0) | ~spl5_8),
% 0.21/0.46    inference(forward_demodulation,[],[f259,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.46    inference(equality_resolution,[],[f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.46    inference(flattening,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.46  fof(f259,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(k1_setfam_1(sK1),k2_zfmisc_1(k1_xboole_0,X0))) ) | ~spl5_8),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f127,f97,f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~r2_hidden(X3,X0) | sP0(X3,X2,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (sP0(X3,X2,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.46    inference(definition_folding,[],[f12,f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X3,X2,X1] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~sP0(X3,X2,X1))),
% 0.21/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    r2_hidden(sK2(k1_setfam_1(sK1)),k1_setfam_1(sK1)) | ~spl5_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f95])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    spl5_8 <=> r2_hidden(sK2(k1_setfam_1(sK1)),k1_setfam_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~sP0(X0,X1,k1_xboole_0)) )),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f75,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | ~sP0(X0,X1,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X0 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X2)) | ~sP0(X0,X1,X2))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X2,X1,X0] : (? [X3,X4] : (k4_tarski(X3,X4) = X0 & r2_hidden(X4,X1) & r2_hidden(X3,X2)) => (k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X0 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X2)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (? [X3,X4] : (k4_tarski(X3,X4) = X0 & r2_hidden(X4,X1) & r2_hidden(X3,X2)) | ~sP0(X0,X1,X2))),
% 0.21/0.46    inference(rectify,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X3,X2,X1] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~sP0(X3,X2,X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f13])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.46    inference(superposition,[],[f32,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    spl5_11 | ~spl5_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f108,f49,f122])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    spl5_2 <=> r2_hidden(k1_xboole_0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    r1_tarski(k1_setfam_1(sK1),k1_xboole_0) | ~spl5_2),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f51,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    r2_hidden(k1_xboole_0,sK1) | ~spl5_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f49])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    spl5_8 | spl5_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f79,f57,f95])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    spl5_3 <=> v1_xboole_0(k1_setfam_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    r2_hidden(sK2(k1_setfam_1(sK1)),k1_setfam_1(sK1)) | spl5_3),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f59,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.47    inference(rectify,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ~v1_xboole_0(k1_setfam_1(sK1)) | spl5_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f57])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ~spl5_3 | spl5_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f53,f44,f57])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl5_1 <=> k1_xboole_0 = k1_setfam_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ~v1_xboole_0(k1_setfam_1(sK1)) | spl5_1),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f46,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    k1_xboole_0 != k1_setfam_1(sK1) | spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f44])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f49])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    r2_hidden(k1_xboole_0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    k1_xboole_0 != k1_setfam_1(sK1) & r2_hidden(k1_xboole_0,sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0] : (k1_xboole_0 != k1_setfam_1(X0) & r2_hidden(k1_xboole_0,X0)) => (k1_xboole_0 != k1_setfam_1(sK1) & r2_hidden(k1_xboole_0,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0] : (k1_xboole_0 != k1_setfam_1(X0) & r2_hidden(k1_xboole_0,X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k1_setfam_1(X0))),
% 0.21/0.47    inference(negated_conjecture,[],[f7])).
% 0.21/0.47  fof(f7,conjecture,(
% 0.21/0.47    ! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k1_setfam_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ~spl5_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f44])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    k1_xboole_0 != k1_setfam_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (29802)------------------------------
% 0.21/0.47  % (29802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (29802)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (29802)Memory used [KB]: 10746
% 0.21/0.47  % (29802)Time elapsed: 0.078 s
% 0.21/0.47  % (29799)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (29802)------------------------------
% 0.21/0.47  % (29802)------------------------------
% 0.21/0.47  % (29785)Success in time 0.114 s
%------------------------------------------------------------------------------
