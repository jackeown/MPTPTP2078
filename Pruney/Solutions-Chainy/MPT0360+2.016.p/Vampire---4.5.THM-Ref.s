%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 116 expanded)
%              Number of leaves         :   22 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  186 ( 302 expanded)
%              Number of equality atoms :   38 (  67 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f330,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f86,f94,f109,f169,f248,f329])).

fof(f329,plain,
    ( spl5_1
    | ~ spl5_10
    | ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl5_1
    | ~ spl5_10
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f318,f48])).

fof(f48,plain,
    ( k1_xboole_0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f318,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_10
    | ~ spl5_21 ),
    inference(resolution,[],[f292,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f292,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl5_10
    | ~ spl5_21 ),
    inference(forward_demodulation,[],[f291,f107])).

fof(f107,plain,
    ( sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_10
  <=> sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f291,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,k3_subset_1(sK0,sK2)))
    | ~ spl5_21 ),
    inference(forward_demodulation,[],[f287,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f287,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k3_subset_1(sK0,sK2),sK1))
    | ~ spl5_21 ),
    inference(unit_resulting_resolution,[],[f240,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f240,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK2),sK1)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl5_21
  <=> r1_xboole_0(k3_subset_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f248,plain,
    ( spl5_21
    | ~ spl5_6
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f232,f166,f76,f238])).

fof(f76,plain,
    ( spl5_6
  <=> sK2 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f166,plain,
    ( spl5_18
  <=> r1_xboole_0(k3_subset_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f232,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK2),sK1)
    | ~ spl5_6
    | ~ spl5_18 ),
    inference(resolution,[],[f112,f168])).

fof(f168,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK2),sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f112,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK2)
        | r1_xboole_0(X1,sK1) )
    | ~ spl5_6 ),
    inference(superposition,[],[f41,f78])).

fof(f78,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f169,plain,
    ( spl5_18
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f164,f90,f166])).

fof(f90,plain,
    ( spl5_8
  <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f164,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK2),sK2)
    | ~ spl5_8 ),
    inference(superposition,[],[f43,f92])).

fof(f92,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f109,plain,
    ( spl5_10
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f97,f51,f105])).

fof(f51,plain,
    ( spl5_2
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f97,plain,
    ( sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f53,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f53,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f94,plain,
    ( spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f88,f61,f90])).

fof(f61,plain,
    ( spl5_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f88,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl5_4 ),
    inference(resolution,[],[f63,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f39,f34])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f63,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f86,plain,
    ( spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f74,f56,f76])).

fof(f56,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f74,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f58,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f58,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f64,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK1
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f59,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f29,f51])).

fof(f29,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f30,f46])).

fof(f30,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 17:08:53 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.52  % (21421)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (21415)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (21431)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (21431)Refutation not found, incomplete strategy% (21431)------------------------------
% 0.21/0.54  % (21431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21439)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (21436)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (21439)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (21431)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21431)Memory used [KB]: 10618
% 0.21/0.55  % (21431)Time elapsed: 0.128 s
% 0.21/0.55  % (21431)------------------------------
% 0.21/0.55  % (21431)------------------------------
% 0.21/0.55  % (21428)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f330,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f86,f94,f109,f169,f248,f329])).
% 0.21/0.55  fof(f329,plain,(
% 0.21/0.55    spl5_1 | ~spl5_10 | ~spl5_21),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f328])).
% 0.21/0.55  fof(f328,plain,(
% 0.21/0.55    $false | (spl5_1 | ~spl5_10 | ~spl5_21)),
% 0.21/0.55    inference(subsumption_resolution,[],[f318,f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    k1_xboole_0 != sK1 | spl5_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    spl5_1 <=> k1_xboole_0 = sK1),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.55  fof(f318,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | (~spl5_10 | ~spl5_21)),
% 0.21/0.55    inference(resolution,[],[f292,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.55  fof(f292,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | (~spl5_10 | ~spl5_21)),
% 0.21/0.55    inference(forward_demodulation,[],[f291,f107])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) | ~spl5_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f105])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    spl5_10 <=> sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.55  fof(f291,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,k3_subset_1(sK0,sK2)))) ) | ~spl5_21),
% 0.21/0.55    inference(forward_demodulation,[],[f287,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.55  fof(f287,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k3_subset_1(sK0,sK2),sK1))) ) | ~spl5_21),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f240,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.55  fof(f240,plain,(
% 0.21/0.55    r1_xboole_0(k3_subset_1(sK0,sK2),sK1) | ~spl5_21),
% 0.21/0.55    inference(avatar_component_clause,[],[f238])).
% 0.21/0.55  fof(f238,plain,(
% 0.21/0.55    spl5_21 <=> r1_xboole_0(k3_subset_1(sK0,sK2),sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.55  fof(f248,plain,(
% 0.21/0.55    spl5_21 | ~spl5_6 | ~spl5_18),
% 0.21/0.55    inference(avatar_split_clause,[],[f232,f166,f76,f238])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    spl5_6 <=> sK2 = k2_xboole_0(sK1,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    spl5_18 <=> r1_xboole_0(k3_subset_1(sK0,sK2),sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.55  fof(f232,plain,(
% 0.21/0.55    r1_xboole_0(k3_subset_1(sK0,sK2),sK1) | (~spl5_6 | ~spl5_18)),
% 0.21/0.55    inference(resolution,[],[f112,f168])).
% 0.21/0.55  fof(f168,plain,(
% 0.21/0.55    r1_xboole_0(k3_subset_1(sK0,sK2),sK2) | ~spl5_18),
% 0.21/0.55    inference(avatar_component_clause,[],[f166])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    ( ! [X1] : (~r1_xboole_0(X1,sK2) | r1_xboole_0(X1,sK1)) ) | ~spl5_6),
% 0.21/0.55    inference(superposition,[],[f41,f78])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    sK2 = k2_xboole_0(sK1,sK2) | ~spl5_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f76])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.55  fof(f169,plain,(
% 0.21/0.55    spl5_18 | ~spl5_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f164,f90,f166])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    spl5_8 <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.55  fof(f164,plain,(
% 0.21/0.55    r1_xboole_0(k3_subset_1(sK0,sK2),sK2) | ~spl5_8),
% 0.21/0.55    inference(superposition,[],[f43,f92])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl5_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f90])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f32,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    spl5_10 | ~spl5_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f97,f51,f105])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    spl5_2 <=> r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) | ~spl5_2),
% 0.21/0.55    inference(resolution,[],[f53,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~spl5_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f51])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    spl5_8 | ~spl5_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f88,f61,f90])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    spl5_4 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl5_4),
% 0.21/0.55    inference(resolution,[],[f63,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f39,f34])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl5_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f61])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    spl5_6 | ~spl5_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f74,f56,f76])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    spl5_3 <=> r1_tarski(sK1,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    sK2 = k2_xboole_0(sK1,sK2) | ~spl5_3),
% 0.21/0.55    inference(resolution,[],[f58,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    r1_tarski(sK1,sK2) | ~spl5_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f56])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    spl5_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f27,f61])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(flattening,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.21/0.55    inference(negated_conjecture,[],[f10])).
% 0.21/0.55  fof(f10,conjecture,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    spl5_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f28,f56])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    r1_tarski(sK1,sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    spl5_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f29,f51])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ~spl5_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f30,f46])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    k1_xboole_0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (21439)------------------------------
% 0.21/0.55  % (21439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21439)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (21439)Memory used [KB]: 6396
% 0.21/0.55  % (21439)Time elapsed: 0.131 s
% 0.21/0.55  % (21439)------------------------------
% 0.21/0.55  % (21439)------------------------------
% 0.21/0.55  % (21413)Success in time 0.198 s
%------------------------------------------------------------------------------
