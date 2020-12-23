%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 182 expanded)
%              Number of leaves         :   13 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  207 ( 650 expanded)
%              Number of equality atoms :   53 ( 190 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f326,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f170,f177,f247,f264,f325])).

fof(f325,plain,
    ( ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f323,f317])).

fof(f317,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f316,f39])).

fof(f39,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK2 != sK3
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f11,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK2 != sK3
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f316,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK2,sK3)
    | ~ spl6_2 ),
    inference(resolution,[],[f313,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

% (3132)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f313,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl6_2 ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,
    ( r1_tarski(sK3,sK2)
    | r1_tarski(sK3,sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f281,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f281,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK4(X3,sK2),sK3)
        | r1_tarski(X3,sK2) )
    | ~ spl6_2 ),
    inference(resolution,[],[f169,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f169,plain,
    ( ! [X8] :
        ( r2_hidden(X8,sK2)
        | ~ r2_hidden(X8,sK3) )
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl6_2
  <=> ! [X8] :
        ( ~ r2_hidden(X8,sK3)
        | r2_hidden(X8,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f323,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,
    ( r1_tarski(sK2,sK3)
    | r1_tarski(sK2,sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f285,f46])).

fof(f285,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK4(X3,sK3),sK2)
        | r1_tarski(X3,sK3) )
    | ~ spl6_3 ),
    inference(resolution,[],[f173,f47])).

fof(f173,plain,
    ( ! [X11] :
        ( r2_hidden(X11,sK3)
        | ~ r2_hidden(X11,sK2) )
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl6_3
  <=> ! [X11] :
        ( ~ r2_hidden(X11,sK2)
        | r2_hidden(X11,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f264,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f261,f38])).

fof(f38,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f261,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_4 ),
    inference(resolution,[],[f255,f76])).

fof(f76,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f44,f72])).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f46,f71])).

fof(f71,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f69,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f69,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_tarski(X2,X2))) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2))) ) ),
    inference(definition_unfolding,[],[f58,f41])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f255,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | ~ spl6_4 ),
    inference(resolution,[],[f176,f46])).

fof(f176,plain,
    ( ! [X10] : ~ r2_hidden(X10,sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl6_4
  <=> ! [X10] : ~ r2_hidden(X10,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f247,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f244,f37])).

fof(f37,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f244,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_1 ),
    inference(resolution,[],[f238,f76])).

% (3122)Refutation not found, incomplete strategy% (3122)------------------------------
% (3122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3122)Termination reason: Refutation not found, incomplete strategy

% (3122)Memory used [KB]: 10618
% (3122)Time elapsed: 0.149 s
% (3122)------------------------------
% (3122)------------------------------
fof(f238,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl6_1 ),
    inference(resolution,[],[f166,f46])).

fof(f166,plain,
    ( ! [X9] : ~ r2_hidden(X9,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl6_1
  <=> ! [X9] : ~ r2_hidden(X9,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f177,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f150,f175,f172])).

fof(f150,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,sK3)
      | ~ r2_hidden(X11,sK2)
      | r2_hidden(X11,sK3) ) ),
    inference(resolution,[],[f62,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3))
      | r2_hidden(X0,sK3) ) ),
    inference(superposition,[],[f60,f36])).

fof(f36,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f170,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f149,f168,f165])).

fof(f149,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,sK3)
      | ~ r2_hidden(X9,sK2)
      | r2_hidden(X8,sK2) ) ),
    inference(resolution,[],[f62,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3))
      | r2_hidden(X1,sK2) ) ),
    inference(superposition,[],[f61,f36])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:30:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (3116)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (3117)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (3131)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (3113)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (3139)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (3114)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (3115)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (3112)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (3118)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (3112)Refutation not found, incomplete strategy% (3112)------------------------------
% 0.21/0.55  % (3112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3112)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3112)Memory used [KB]: 1663
% 0.21/0.55  % (3112)Time elapsed: 0.126 s
% 0.21/0.55  % (3112)------------------------------
% 0.21/0.55  % (3112)------------------------------
% 0.21/0.55  % (3125)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (3136)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (3124)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (3137)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (3138)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (3128)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (3138)Refutation not found, incomplete strategy% (3138)------------------------------
% 0.21/0.55  % (3138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3138)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3138)Memory used [KB]: 10746
% 0.21/0.55  % (3138)Time elapsed: 0.137 s
% 0.21/0.55  % (3138)------------------------------
% 0.21/0.55  % (3138)------------------------------
% 0.21/0.56  % (3140)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (3129)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (3141)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (3130)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (3129)Refutation not found, incomplete strategy% (3129)------------------------------
% 0.21/0.56  % (3129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3129)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3129)Memory used [KB]: 10618
% 0.21/0.56  % (3129)Time elapsed: 0.139 s
% 0.21/0.56  % (3129)------------------------------
% 0.21/0.56  % (3129)------------------------------
% 0.21/0.56  % (3139)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (3121)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (3121)Refutation not found, incomplete strategy% (3121)------------------------------
% 0.21/0.56  % (3121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3121)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3121)Memory used [KB]: 10618
% 0.21/0.56  % (3121)Time elapsed: 0.148 s
% 0.21/0.56  % (3121)------------------------------
% 0.21/0.56  % (3121)------------------------------
% 0.21/0.56  % (3122)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f326,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f170,f177,f247,f264,f325])).
% 0.21/0.56  fof(f325,plain,(
% 0.21/0.56    ~spl6_2 | ~spl6_3),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f324])).
% 0.21/0.56  fof(f324,plain,(
% 0.21/0.56    $false | (~spl6_2 | ~spl6_3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f323,f317])).
% 0.21/0.56  fof(f317,plain,(
% 0.21/0.56    ~r1_tarski(sK2,sK3) | ~spl6_2),
% 0.21/0.56    inference(subsumption_resolution,[],[f316,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    sK2 != sK3),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    sK2 != sK3 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f11,f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK2 != sK3 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.21/0.56    inference(flattening,[],[f10])).
% 0.21/0.56  fof(f10,plain,(
% 0.21/0.56    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.56    inference(negated_conjecture,[],[f8])).
% 0.21/0.56  fof(f8,conjecture,(
% 0.21/0.56    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 0.21/0.56  fof(f316,plain,(
% 0.21/0.56    sK2 = sK3 | ~r1_tarski(sK2,sK3) | ~spl6_2),
% 0.21/0.56    inference(resolution,[],[f313,f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  % (3132)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.56    inference(flattening,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.56  fof(f313,plain,(
% 0.21/0.56    r1_tarski(sK3,sK2) | ~spl6_2),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f310])).
% 0.21/0.56  fof(f310,plain,(
% 0.21/0.56    r1_tarski(sK3,sK2) | r1_tarski(sK3,sK2) | ~spl6_2),
% 0.21/0.56    inference(resolution,[],[f281,f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.56    inference(rectify,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.56    inference(nnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.56  fof(f281,plain,(
% 0.21/0.56    ( ! [X3] : (~r2_hidden(sK4(X3,sK2),sK3) | r1_tarski(X3,sK2)) ) | ~spl6_2),
% 0.21/0.56    inference(resolution,[],[f169,f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f169,plain,(
% 0.21/0.56    ( ! [X8] : (r2_hidden(X8,sK2) | ~r2_hidden(X8,sK3)) ) | ~spl6_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f168])).
% 0.21/0.56  fof(f168,plain,(
% 0.21/0.56    spl6_2 <=> ! [X8] : (~r2_hidden(X8,sK3) | r2_hidden(X8,sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.56  fof(f323,plain,(
% 0.21/0.56    r1_tarski(sK2,sK3) | ~spl6_3),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f320])).
% 0.21/0.56  fof(f320,plain,(
% 0.21/0.56    r1_tarski(sK2,sK3) | r1_tarski(sK2,sK3) | ~spl6_3),
% 0.21/0.56    inference(resolution,[],[f285,f46])).
% 0.21/0.56  fof(f285,plain,(
% 0.21/0.56    ( ! [X3] : (~r2_hidden(sK4(X3,sK3),sK2) | r1_tarski(X3,sK3)) ) | ~spl6_3),
% 0.21/0.56    inference(resolution,[],[f173,f47])).
% 0.21/0.56  fof(f173,plain,(
% 0.21/0.56    ( ! [X11] : (r2_hidden(X11,sK3) | ~r2_hidden(X11,sK2)) ) | ~spl6_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f172])).
% 0.21/0.56  fof(f172,plain,(
% 0.21/0.56    spl6_3 <=> ! [X11] : (~r2_hidden(X11,sK2) | r2_hidden(X11,sK3))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.56  fof(f264,plain,(
% 0.21/0.56    ~spl6_4),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f263])).
% 0.21/0.56  fof(f263,plain,(
% 0.21/0.56    $false | ~spl6_4),
% 0.21/0.56    inference(subsumption_resolution,[],[f261,f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    k1_xboole_0 != sK3),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f261,plain,(
% 0.21/0.56    k1_xboole_0 = sK3 | ~spl6_4),
% 0.21/0.56    inference(resolution,[],[f255,f76])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.21/0.56    inference(resolution,[],[f44,f72])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(resolution,[],[f46,f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(superposition,[],[f69,f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_tarski(X2,X2)))) )),
% 0.21/0.56    inference(equality_resolution,[],[f64])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2)))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f58,f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.56    inference(flattening,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.56    inference(nnf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.56  fof(f255,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(sK3,X0)) ) | ~spl6_4),
% 0.21/0.56    inference(resolution,[],[f176,f46])).
% 0.21/0.56  fof(f176,plain,(
% 0.21/0.56    ( ! [X10] : (~r2_hidden(X10,sK3)) ) | ~spl6_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f175])).
% 0.21/0.56  fof(f175,plain,(
% 0.21/0.56    spl6_4 <=> ! [X10] : ~r2_hidden(X10,sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.56  fof(f247,plain,(
% 0.21/0.56    ~spl6_1),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f246])).
% 0.21/0.56  fof(f246,plain,(
% 0.21/0.56    $false | ~spl6_1),
% 0.21/0.56    inference(subsumption_resolution,[],[f244,f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    k1_xboole_0 != sK2),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f244,plain,(
% 0.21/0.56    k1_xboole_0 = sK2 | ~spl6_1),
% 0.21/0.56    inference(resolution,[],[f238,f76])).
% 0.21/0.56  % (3122)Refutation not found, incomplete strategy% (3122)------------------------------
% 0.21/0.56  % (3122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3122)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3122)Memory used [KB]: 10618
% 0.21/0.56  % (3122)Time elapsed: 0.149 s
% 0.21/0.56  % (3122)------------------------------
% 0.21/0.56  % (3122)------------------------------
% 0.21/0.56  fof(f238,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(sK2,X0)) ) | ~spl6_1),
% 0.21/0.56    inference(resolution,[],[f166,f46])).
% 0.21/0.56  fof(f166,plain,(
% 0.21/0.56    ( ! [X9] : (~r2_hidden(X9,sK2)) ) | ~spl6_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f165])).
% 0.21/0.56  fof(f165,plain,(
% 0.21/0.56    spl6_1 <=> ! [X9] : ~r2_hidden(X9,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.56  fof(f177,plain,(
% 0.21/0.56    spl6_3 | spl6_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f150,f175,f172])).
% 0.21/0.56  fof(f150,plain,(
% 0.21/0.56    ( ! [X10,X11] : (~r2_hidden(X10,sK3) | ~r2_hidden(X11,sK2) | r2_hidden(X11,sK3)) )),
% 0.21/0.56    inference(resolution,[],[f62,f106])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) | r2_hidden(X0,sK3)) )),
% 0.21/0.56    inference(superposition,[],[f60,f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.56    inference(flattening,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.56    inference(nnf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f170,plain,(
% 0.21/0.56    spl6_1 | spl6_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f149,f168,f165])).
% 0.21/0.56  fof(f149,plain,(
% 0.21/0.56    ( ! [X8,X9] : (~r2_hidden(X8,sK3) | ~r2_hidden(X9,sK2) | r2_hidden(X8,sK2)) )),
% 0.21/0.56    inference(resolution,[],[f62,f117])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) | r2_hidden(X1,sK2)) )),
% 0.21/0.56    inference(superposition,[],[f61,f36])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (3139)------------------------------
% 0.21/0.56  % (3139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3139)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (3139)Memory used [KB]: 6396
% 0.21/0.56  % (3139)Time elapsed: 0.133 s
% 0.21/0.56  % (3139)------------------------------
% 0.21/0.56  % (3139)------------------------------
% 0.21/0.57  % (3132)Refutation not found, incomplete strategy% (3132)------------------------------
% 0.21/0.57  % (3132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (3111)Success in time 0.194 s
%------------------------------------------------------------------------------
