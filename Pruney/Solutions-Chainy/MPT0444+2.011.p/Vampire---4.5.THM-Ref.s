%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:01 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 136 expanded)
%              Number of leaves         :   20 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  241 ( 432 expanded)
%              Number of equality atoms :   61 ( 136 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f77,f97,f117,f121,f144,f147])).

fof(f147,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f58,f143,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f143,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl3_10
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f58,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

% (3097)Refutation not found, incomplete strategy% (3097)------------------------------
% (3097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3097)Termination reason: Refutation not found, incomplete strategy

% (3097)Memory used [KB]: 1663
% (3097)Time elapsed: 0.090 s
% (3097)------------------------------
% (3097)------------------------------
fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f144,plain,
    ( ~ spl3_6
    | ~ spl3_2
    | ~ spl3_10
    | spl3_5 ),
    inference(avatar_split_clause,[],[f130,f94,f141,f68,f100])).

fof(f100,plain,
    ( spl3_6
  <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f68,plain,
    ( spl3_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f94,plain,
    ( spl3_5
  <=> r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f130,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl3_5 ),
    inference(resolution,[],[f96,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f96,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f121,plain,
    ( ~ spl3_1
    | spl3_4
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl3_1
    | spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f65,f50,f92,f101,f37])).

fof(f101,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f92,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_4
  <=> r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

% (3086)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f35,f47])).

% (3111)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f46])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f65,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

% (3099)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f117,plain,
    ( ~ spl3_2
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f110])).

% (3090)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (3099)Refutation not found, incomplete strategy% (3099)------------------------------
% (3099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3099)Termination reason: Refutation not found, incomplete strategy

% (3099)Memory used [KB]: 10618
% (3099)Time elapsed: 0.128 s
% (3099)------------------------------
% (3099)------------------------------
% (3089)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (3112)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (3112)Refutation not found, incomplete strategy% (3112)------------------------------
% (3112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3112)Termination reason: Refutation not found, incomplete strategy

% (3112)Memory used [KB]: 1663
% (3112)Time elapsed: 0.126 s
% (3112)------------------------------
% (3112)------------------------------
% (3100)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (3094)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (3092)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (3095)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% (3102)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (3103)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f110,plain,
    ( $false
    | ~ spl3_2
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f70,f58,f102,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | v1_relat_1(k1_setfam_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f78,f34])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f39,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f102,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f70,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f97,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | spl3_3 ),
    inference(avatar_split_clause,[],[f87,f74,f94,f90])).

fof(f74,plain,
    ( spl3_3
  <=> r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f87,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK0))
    | spl3_3 ),
    inference(resolution,[],[f49,f76])).

fof(f76,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f47])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f77,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f48,f74])).

fof(f48,plain,(
    ~ r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f30,f47,f47])).

fof(f30,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

% (3095)Refutation not found, incomplete strategy% (3095)------------------------------
% (3095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3095)Termination reason: Refutation not found, incomplete strategy

% (3095)Memory used [KB]: 10618
% (3095)Time elapsed: 0.140 s
% (3095)------------------------------
% (3095)------------------------------
fof(f71,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f29,f68])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (3098)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (3091)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.21/0.52  % (3087)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.21/0.52  % (3085)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.21/0.52  % (3083)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.21/0.53  % (3084)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.21/0.53  % (3106)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.21/0.53  % (3084)Refutation not found, incomplete strategy% (3084)------------------------------
% 1.21/0.53  % (3084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (3084)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (3084)Memory used [KB]: 1663
% 1.21/0.53  % (3084)Time elapsed: 0.098 s
% 1.21/0.53  % (3084)------------------------------
% 1.21/0.53  % (3084)------------------------------
% 1.21/0.53  % (3088)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.37/0.53  % (3105)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.37/0.53  % (3097)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.37/0.53  % (3096)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.37/0.53  % (3101)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.37/0.53  % (3106)Refutation found. Thanks to Tanya!
% 1.37/0.53  % SZS status Theorem for theBenchmark
% 1.37/0.53  % (3110)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.37/0.53  % (3108)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.37/0.54  % (3107)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.37/0.54  % SZS output start Proof for theBenchmark
% 1.37/0.54  fof(f148,plain,(
% 1.37/0.54    $false),
% 1.37/0.54    inference(avatar_sat_refutation,[],[f66,f71,f77,f97,f117,f121,f144,f147])).
% 1.37/0.54  fof(f147,plain,(
% 1.37/0.54    spl3_10),
% 1.37/0.54    inference(avatar_contradiction_clause,[],[f145])).
% 1.37/0.54  fof(f145,plain,(
% 1.37/0.54    $false | spl3_10),
% 1.37/0.54    inference(unit_resulting_resolution,[],[f58,f143,f34])).
% 1.37/0.54  fof(f34,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f15])).
% 1.37/0.54  fof(f15,plain,(
% 1.37/0.54    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 1.37/0.54    inference(ennf_transformation,[],[f7])).
% 1.37/0.54  fof(f7,axiom,(
% 1.37/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.37/0.54  fof(f143,plain,(
% 1.37/0.54    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | spl3_10),
% 1.37/0.54    inference(avatar_component_clause,[],[f141])).
% 1.37/0.54  fof(f141,plain,(
% 1.37/0.54    spl3_10 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.37/0.54  fof(f58,plain,(
% 1.37/0.54    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 1.37/0.54    inference(equality_resolution,[],[f57])).
% 1.37/0.54  fof(f57,plain,(
% 1.37/0.54    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 1.37/0.54    inference(equality_resolution,[],[f54])).
% 1.37/0.54  fof(f54,plain,(
% 1.37/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.37/0.54    inference(definition_unfolding,[],[f42,f46])).
% 1.37/0.54  fof(f46,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f4])).
% 1.37/0.54  fof(f4,axiom,(
% 1.37/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 1.37/0.54  fof(f42,plain,(
% 1.37/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.37/0.54    inference(cnf_transformation,[],[f27])).
% 1.37/0.54  fof(f27,plain,(
% 1.37/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.37/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 1.37/0.54  fof(f26,plain,(
% 1.37/0.54    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  % (3097)Refutation not found, incomplete strategy% (3097)------------------------------
% 1.37/0.54  % (3097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (3097)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (3097)Memory used [KB]: 1663
% 1.37/0.54  % (3097)Time elapsed: 0.090 s
% 1.37/0.54  % (3097)------------------------------
% 1.37/0.54  % (3097)------------------------------
% 1.37/0.54  fof(f25,plain,(
% 1.37/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.37/0.54    inference(rectify,[],[f24])).
% 1.37/0.54  fof(f24,plain,(
% 1.37/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.37/0.54    inference(flattening,[],[f23])).
% 1.37/0.54  fof(f23,plain,(
% 1.37/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.37/0.54    inference(nnf_transformation,[],[f3])).
% 1.37/0.54  fof(f3,axiom,(
% 1.37/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.37/0.54  fof(f144,plain,(
% 1.37/0.54    ~spl3_6 | ~spl3_2 | ~spl3_10 | spl3_5),
% 1.37/0.54    inference(avatar_split_clause,[],[f130,f94,f141,f68,f100])).
% 1.37/0.54  fof(f100,plain,(
% 1.37/0.54    spl3_6 <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.37/0.54  fof(f68,plain,(
% 1.37/0.54    spl3_2 <=> v1_relat_1(sK1)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.37/0.54  fof(f94,plain,(
% 1.37/0.54    spl3_5 <=> r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK1))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.37/0.54  fof(f130,plain,(
% 1.37/0.54    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl3_5),
% 1.37/0.54    inference(resolution,[],[f96,f37])).
% 1.37/0.54  fof(f37,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f17])).
% 1.37/0.54  fof(f17,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.37/0.54    inference(flattening,[],[f16])).
% 1.37/0.54  fof(f16,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f9])).
% 1.37/0.54  fof(f9,axiom,(
% 1.37/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.37/0.54  fof(f96,plain,(
% 1.37/0.54    ~r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK1)) | spl3_5),
% 1.37/0.54    inference(avatar_component_clause,[],[f94])).
% 1.37/0.54  fof(f121,plain,(
% 1.37/0.54    ~spl3_1 | spl3_4 | ~spl3_6),
% 1.37/0.54    inference(avatar_contradiction_clause,[],[f120])).
% 1.37/0.54  fof(f120,plain,(
% 1.37/0.54    $false | (~spl3_1 | spl3_4 | ~spl3_6)),
% 1.37/0.54    inference(unit_resulting_resolution,[],[f65,f50,f92,f101,f37])).
% 1.37/0.54  fof(f101,plain,(
% 1.37/0.54    v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | ~spl3_6),
% 1.37/0.54    inference(avatar_component_clause,[],[f100])).
% 1.37/0.54  fof(f92,plain,(
% 1.37/0.54    ~r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK0)) | spl3_4),
% 1.37/0.54    inference(avatar_component_clause,[],[f90])).
% 1.37/0.54  fof(f90,plain,(
% 1.37/0.54    spl3_4 <=> r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK0))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.37/0.54  % (3086)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.37/0.54  fof(f50,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 1.37/0.54    inference(definition_unfolding,[],[f35,f47])).
% 1.37/0.54  % (3111)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.37/0.54  fof(f47,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f38,f46])).
% 1.37/0.54  fof(f38,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f5])).
% 1.37/0.54  fof(f5,axiom,(
% 1.37/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.37/0.54  fof(f35,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f1])).
% 1.37/0.54  fof(f1,axiom,(
% 1.37/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.37/0.54  fof(f65,plain,(
% 1.37/0.54    v1_relat_1(sK0) | ~spl3_1),
% 1.37/0.54    inference(avatar_component_clause,[],[f63])).
% 1.37/0.54  fof(f63,plain,(
% 1.37/0.54    spl3_1 <=> v1_relat_1(sK0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.37/0.54  % (3099)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.37/0.54  fof(f117,plain,(
% 1.37/0.54    ~spl3_2 | spl3_6),
% 1.37/0.54    inference(avatar_contradiction_clause,[],[f110])).
% 1.37/0.54  % (3090)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.37/0.54  % (3099)Refutation not found, incomplete strategy% (3099)------------------------------
% 1.37/0.54  % (3099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (3099)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (3099)Memory used [KB]: 10618
% 1.37/0.54  % (3099)Time elapsed: 0.128 s
% 1.37/0.54  % (3099)------------------------------
% 1.37/0.54  % (3099)------------------------------
% 1.37/0.54  % (3089)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.54  % (3112)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.37/0.54  % (3112)Refutation not found, incomplete strategy% (3112)------------------------------
% 1.37/0.54  % (3112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (3112)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (3112)Memory used [KB]: 1663
% 1.37/0.54  % (3112)Time elapsed: 0.126 s
% 1.37/0.54  % (3112)------------------------------
% 1.37/0.54  % (3112)------------------------------
% 1.37/0.54  % (3100)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.37/0.54  % (3094)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.37/0.55  % (3092)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.37/0.55  % (3095)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.37/0.55  % (3102)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.37/0.55  % (3103)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.37/0.55  fof(f110,plain,(
% 1.37/0.55    $false | (~spl3_2 | spl3_6)),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f70,f58,f102,f79])).
% 1.37/0.55  fof(f79,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | v1_relat_1(k1_setfam_1(X1)) | ~v1_relat_1(X0)) )),
% 1.37/0.55    inference(resolution,[],[f78,f34])).
% 1.37/0.55  fof(f78,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 1.37/0.55    inference(resolution,[],[f39,f33])).
% 1.37/0.55  fof(f33,plain,(
% 1.37/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f22])).
% 1.37/0.55  fof(f22,plain,(
% 1.37/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.37/0.55    inference(nnf_transformation,[],[f6])).
% 1.37/0.55  fof(f6,axiom,(
% 1.37/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.37/0.55  fof(f39,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f18])).
% 1.37/0.55  fof(f18,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.37/0.55    inference(ennf_transformation,[],[f8])).
% 1.37/0.55  fof(f8,axiom,(
% 1.37/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.37/0.55  fof(f102,plain,(
% 1.37/0.55    ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl3_6),
% 1.37/0.55    inference(avatar_component_clause,[],[f100])).
% 1.37/0.55  fof(f70,plain,(
% 1.37/0.55    v1_relat_1(sK1) | ~spl3_2),
% 1.37/0.55    inference(avatar_component_clause,[],[f68])).
% 1.37/0.55  fof(f97,plain,(
% 1.37/0.55    ~spl3_4 | ~spl3_5 | spl3_3),
% 1.37/0.55    inference(avatar_split_clause,[],[f87,f74,f94,f90])).
% 1.37/0.55  fof(f74,plain,(
% 1.37/0.55    spl3_3 <=> r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))))),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.37/0.55  fof(f87,plain,(
% 1.37/0.55    ~r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK1)) | ~r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k2_relat_1(sK0)) | spl3_3),
% 1.37/0.55    inference(resolution,[],[f49,f76])).
% 1.37/0.55  fof(f76,plain,(
% 1.37/0.55    ~r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) | spl3_3),
% 1.37/0.55    inference(avatar_component_clause,[],[f74])).
% 1.37/0.55  fof(f49,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.37/0.55    inference(definition_unfolding,[],[f31,f47])).
% 1.37/0.55  fof(f31,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f14])).
% 1.37/0.55  fof(f14,plain,(
% 1.37/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.37/0.55    inference(flattening,[],[f13])).
% 1.37/0.55  fof(f13,plain,(
% 1.37/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.37/0.55    inference(ennf_transformation,[],[f2])).
% 1.37/0.55  fof(f2,axiom,(
% 1.37/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.37/0.55  fof(f77,plain,(
% 1.37/0.55    ~spl3_3),
% 1.37/0.55    inference(avatar_split_clause,[],[f48,f74])).
% 1.37/0.55  fof(f48,plain,(
% 1.37/0.55    ~r1_tarski(k2_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))))),
% 1.37/0.55    inference(definition_unfolding,[],[f30,f47,f47])).
% 1.37/0.55  fof(f30,plain,(
% 1.37/0.55    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 1.37/0.55    inference(cnf_transformation,[],[f21])).
% 1.37/0.55  fof(f21,plain,(
% 1.37/0.55    (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.37/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f20,f19])).
% 1.37/0.55  fof(f19,plain,(
% 1.37/0.55    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.37/0.55    introduced(choice_axiom,[])).
% 1.37/0.55  fof(f20,plain,(
% 1.37/0.55    ? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 1.37/0.55    introduced(choice_axiom,[])).
% 1.37/0.55  fof(f12,plain,(
% 1.37/0.55    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.37/0.55    inference(ennf_transformation,[],[f11])).
% 1.37/0.55  fof(f11,negated_conjecture,(
% 1.37/0.55    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 1.37/0.55    inference(negated_conjecture,[],[f10])).
% 1.37/0.55  fof(f10,conjecture,(
% 1.37/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).
% 1.37/0.55  % (3095)Refutation not found, incomplete strategy% (3095)------------------------------
% 1.37/0.55  % (3095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (3095)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (3095)Memory used [KB]: 10618
% 1.37/0.55  % (3095)Time elapsed: 0.140 s
% 1.37/0.55  % (3095)------------------------------
% 1.37/0.55  % (3095)------------------------------
% 1.37/0.55  fof(f71,plain,(
% 1.37/0.55    spl3_2),
% 1.37/0.55    inference(avatar_split_clause,[],[f29,f68])).
% 1.37/0.55  fof(f29,plain,(
% 1.37/0.55    v1_relat_1(sK1)),
% 1.37/0.55    inference(cnf_transformation,[],[f21])).
% 1.37/0.55  fof(f66,plain,(
% 1.37/0.55    spl3_1),
% 1.37/0.55    inference(avatar_split_clause,[],[f28,f63])).
% 1.37/0.55  fof(f28,plain,(
% 1.37/0.55    v1_relat_1(sK0)),
% 1.37/0.55    inference(cnf_transformation,[],[f21])).
% 1.37/0.55  % SZS output end Proof for theBenchmark
% 1.37/0.55  % (3106)------------------------------
% 1.37/0.55  % (3106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (3106)Termination reason: Refutation
% 1.37/0.55  
% 1.37/0.55  % (3106)Memory used [KB]: 10746
% 1.37/0.55  % (3106)Time elapsed: 0.123 s
% 1.37/0.55  % (3106)------------------------------
% 1.37/0.55  % (3106)------------------------------
% 1.37/0.55  % (3082)Success in time 0.188 s
%------------------------------------------------------------------------------
