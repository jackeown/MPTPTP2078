%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 154 expanded)
%              Number of leaves         :   15 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  228 ( 544 expanded)
%              Number of equality atoms :   58 ( 188 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f175,f176,f193,f194,f203])).

fof(f203,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f197,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK0 != sK1
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK0 != sK1
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ) ),
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

fof(f197,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(resolution,[],[f97,f69])).

fof(f69,plain,(
    ! [X3] :
      ( r2_hidden(sK2(X3,k1_xboole_0),X3)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f35,f55])).

fof(f55,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f54,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f54,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_tarski(X2,X2))) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2))) ) ),
    inference(definition_unfolding,[],[f44,f34])).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f97,plain,
    ( ! [X10] : ~ r2_hidden(X10,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_4
  <=> ! [X10] : ~ r2_hidden(X10,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f194,plain,
    ( spl4_4
    | spl4_3 ),
    inference(avatar_split_clause,[],[f129,f93,f96])).

fof(f93,plain,
    ( spl4_3
  <=> ! [X11] :
        ( ~ r2_hidden(X11,sK0)
        | r2_hidden(X11,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f129,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK0)
      | ~ r2_hidden(X5,sK1)
      | r2_hidden(X4,sK1) ) ),
    inference(resolution,[],[f84,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f48,f29])).

fof(f29,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f193,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f187,f30])).

fof(f30,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f187,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(resolution,[],[f87,f69])).

fof(f87,plain,
    ( ! [X9] : ~ r2_hidden(X9,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_1
  <=> ! [X9] : ~ r2_hidden(X9,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f176,plain,
    ( spl4_2
    | spl4_1 ),
    inference(avatar_split_clause,[],[f130,f86,f89])).

fof(f89,plain,
    ( spl4_2
  <=> ! [X8] :
        ( ~ r2_hidden(X8,sK1)
        | r2_hidden(X8,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f130,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,sK0)
      | ~ r2_hidden(X7,sK1)
      | r2_hidden(X7,sK0) ) ),
    inference(resolution,[],[f84,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f175,plain,
    ( ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f173,f166])).

fof(f166,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f165,f32])).

fof(f32,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f165,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f162,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f162,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f99,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f99,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1,X0),sK0)
        | r1_tarski(sK1,X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f90,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f90,plain,
    ( ! [X8] :
        ( ~ r2_hidden(X8,sK1)
        | r2_hidden(X8,sK0) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f173,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f113,f42])).

fof(f113,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK0,X1),sK1)
        | r1_tarski(sK0,X1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f94,f41])).

fof(f94,plain,
    ( ! [X11] :
        ( ~ r2_hidden(X11,sK0)
        | r2_hidden(X11,sK1) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:12:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (27949)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (27950)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
% 0.22/0.51  % (27950)Refutation not found, incomplete strategy% (27950)------------------------------
% 0.22/0.51  % (27950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27950)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (27950)Memory used [KB]: 6140
% 0.22/0.51  % (27950)Time elapsed: 0.107 s
% 0.22/0.51  % (27950)------------------------------
% 0.22/0.51  % (27950)------------------------------
% 0.22/0.51  % (27960)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% 0.22/0.51  % (27952)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% 0.22/0.52  % (27974)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
% 0.22/0.52  % (27957)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
% 0.22/0.52  % (27951)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% 0.22/0.52  % (27951)Refutation not found, incomplete strategy% (27951)------------------------------
% 0.22/0.52  % (27951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27951)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (27951)Memory used [KB]: 6140
% 0.22/0.52  % (27951)Time elapsed: 0.001 s
% 0.22/0.52  % (27951)------------------------------
% 0.22/0.52  % (27951)------------------------------
% 0.22/0.52  % (27954)dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17 on theBenchmark
% 0.22/0.52  % (27967)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% 0.22/0.52  % (27961)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% 0.22/0.53  % (27966)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (27948)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
% 0.22/0.53  % (27948)Refutation not found, incomplete strategy% (27948)------------------------------
% 0.22/0.53  % (27948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (27948)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (27948)Memory used [KB]: 6140
% 0.22/0.53  % (27948)Time elapsed: 0.117 s
% 0.22/0.53  % (27948)------------------------------
% 0.22/0.53  % (27948)------------------------------
% 0.22/0.53  % (27957)Refutation not found, incomplete strategy% (27957)------------------------------
% 0.22/0.53  % (27957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (27957)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (27957)Memory used [KB]: 6140
% 0.22/0.53  % (27957)Time elapsed: 0.107 s
% 0.22/0.53  % (27957)------------------------------
% 0.22/0.53  % (27957)------------------------------
% 0.22/0.53  % (27966)Refutation not found, incomplete strategy% (27966)------------------------------
% 0.22/0.53  % (27966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (27966)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (27966)Memory used [KB]: 10618
% 0.22/0.53  % (27966)Time elapsed: 0.127 s
% 0.22/0.53  % (27966)------------------------------
% 0.22/0.53  % (27966)------------------------------
% 0.22/0.53  % (27975)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% 0.22/0.53  % (27962)dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (27962)Refutation not found, incomplete strategy% (27962)------------------------------
% 0.22/0.53  % (27962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (27962)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (27962)Memory used [KB]: 6140
% 0.22/0.53  % (27962)Time elapsed: 0.098 s
% 0.22/0.53  % (27962)------------------------------
% 0.22/0.53  % (27962)------------------------------
% 0.22/0.53  % (27959)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% 0.22/0.53  % (27956)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
% 0.22/0.53  % (27958)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3 on theBenchmark
% 0.22/0.53  % (27956)Refutation not found, incomplete strategy% (27956)------------------------------
% 0.22/0.53  % (27956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (27956)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (27956)Memory used [KB]: 6140
% 0.22/0.53  % (27956)Time elapsed: 0.136 s
% 0.22/0.53  % (27956)------------------------------
% 0.22/0.53  % (27956)------------------------------
% 0.22/0.53  % (27970)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157 on theBenchmark
% 0.22/0.53  % (27971)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (27953)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
% 0.22/0.53  % (27959)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f175,f176,f193,f194,f203])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    ~spl4_4),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f202])).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    $false | ~spl4_4),
% 0.22/0.53    inference(subsumption_resolution,[],[f197,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    k1_xboole_0 != sK1),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    sK0 != sK1 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK0 != sK1 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.22/0.53    inference(flattening,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    inference(negated_conjecture,[],[f8])).
% 0.22/0.53  fof(f8,conjecture,(
% 0.22/0.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | ~spl4_4),
% 0.22/0.53    inference(resolution,[],[f97,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X3] : (r2_hidden(sK2(X3,k1_xboole_0),X3) | k1_xboole_0 = X3) )),
% 0.22/0.53    inference(resolution,[],[f35,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(superposition,[],[f54,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_tarski(X2,X2)))) )),
% 0.22/0.53    inference(equality_resolution,[],[f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2)))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f44,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.22/0.53    inference(flattening,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.22/0.53    inference(nnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | X0 = X1 | r2_hidden(sK2(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.22/0.54    inference(nnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X10] : (~r2_hidden(X10,sK1)) ) | ~spl4_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f96])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    spl4_4 <=> ! [X10] : ~r2_hidden(X10,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    spl4_4 | spl4_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f129,f93,f96])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    spl4_3 <=> ! [X11] : (~r2_hidden(X11,sK0) | r2_hidden(X11,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    ( ! [X4,X5] : (~r2_hidden(X4,sK0) | ~r2_hidden(X5,sK1) | r2_hidden(X4,sK1)) )),
% 0.22/0.54    inference(resolution,[],[f84,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.54    inference(nnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK1)) )),
% 0.22/0.54    inference(superposition,[],[f48,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    ~spl4_1),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f192])).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    $false | ~spl4_1),
% 0.22/0.54    inference(subsumption_resolution,[],[f187,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    k1_xboole_0 != sK0),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | ~spl4_1),
% 0.22/0.54    inference(resolution,[],[f87,f69])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X9] : (~r2_hidden(X9,sK0)) ) | ~spl4_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f86])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    spl4_1 <=> ! [X9] : ~r2_hidden(X9,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.54  fof(f176,plain,(
% 0.22/0.54    spl4_2 | spl4_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f130,f86,f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    spl4_2 <=> ! [X8] : (~r2_hidden(X8,sK1) | r2_hidden(X8,sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    ( ! [X6,X7] : (~r2_hidden(X6,sK0) | ~r2_hidden(X7,sK1) | r2_hidden(X7,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f84,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    ~spl4_2 | ~spl4_3),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f174])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    $false | (~spl4_2 | ~spl4_3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f173,f166])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    ~r1_tarski(sK0,sK1) | ~spl4_2),
% 0.22/0.54    inference(subsumption_resolution,[],[f165,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    sK0 != sK1),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    sK0 = sK1 | ~r1_tarski(sK0,sK1) | ~spl4_2),
% 0.22/0.54    inference(resolution,[],[f162,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    r1_tarski(sK1,sK0) | ~spl4_2),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f159])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl4_2),
% 0.22/0.54    inference(resolution,[],[f99,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK3(sK1,X0),sK0) | r1_tarski(sK1,X0)) ) | ~spl4_2),
% 0.22/0.54    inference(resolution,[],[f90,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X8] : (~r2_hidden(X8,sK1) | r2_hidden(X8,sK0)) ) | ~spl4_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f89])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    r1_tarski(sK0,sK1) | ~spl4_3),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f170])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1) | ~spl4_3),
% 0.22/0.54    inference(resolution,[],[f113,f42])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    ( ! [X1] : (r2_hidden(sK3(sK0,X1),sK1) | r1_tarski(sK0,X1)) ) | ~spl4_3),
% 0.22/0.54    inference(resolution,[],[f94,f41])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X11] : (~r2_hidden(X11,sK0) | r2_hidden(X11,sK1)) ) | ~spl4_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f93])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (27959)------------------------------
% 0.22/0.54  % (27959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27959)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (27959)Memory used [KB]: 6268
% 0.22/0.54  % (27959)Time elapsed: 0.128 s
% 0.22/0.54  % (27959)------------------------------
% 0.22/0.54  % (27959)------------------------------
% 0.22/0.54  % (27963)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (27947)Success in time 0.169 s
%------------------------------------------------------------------------------
