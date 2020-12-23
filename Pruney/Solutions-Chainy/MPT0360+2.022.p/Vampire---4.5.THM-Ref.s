%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:51 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 338 expanded)
%              Number of leaves         :   14 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  235 ( 856 expanded)
%              Number of equality atoms :   37 ( 217 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f609,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f153,f159,f259,f512,f513,f521,f582,f583,f608])).

fof(f608,plain,
    ( ~ spl4_19
    | ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f594])).

% (21359)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
fof(f594,plain,
    ( $false
    | ~ spl4_19
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f16,f588])).

fof(f588,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_19
    | ~ spl4_32 ),
    inference(superposition,[],[f482,f384])).

fof(f384,plain,
    ( sK1 = k5_xboole_0(sK1,sK1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl4_19
  <=> sK1 = k5_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f482,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK1)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl4_32
  <=> k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

% (21358)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f583,plain,
    ( spl4_18
    | spl4_32
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f578,f256,f151,f480,f379])).

fof(f379,plain,
    ( spl4_18
  <=> ! [X24] : ~ r1_tarski(sK1,X24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f151,plain,
    ( spl4_9
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f256,plain,
    ( spl4_13
  <=> r2_hidden(sK3(sK1,sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f578,plain,
    ( ! [X13] :
        ( k1_xboole_0 = k5_xboole_0(sK1,sK1)
        | ~ r1_tarski(sK1,X13) )
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(resolution,[],[f561,f327])).

fof(f327,plain,(
    ! [X24,X25] :
      ( r2_hidden(sK3(X24,X25,k1_xboole_0),X24)
      | k1_xboole_0 = k5_xboole_0(X24,X24)
      | ~ r1_tarski(X24,X25) ) ),
    inference(resolution,[],[f138,f120])).

fof(f120,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f110,f37])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f110,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_xboole_0,X3)
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f107,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(X0,X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f40,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

% (21355)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f28,f18])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

% (21359)Refutation not found, incomplete strategy% (21359)------------------------------
% (21359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21359)Termination reason: Refutation not found, incomplete strategy

% (21359)Memory used [KB]: 1663
% (21359)Time elapsed: 0.124 s
% (21359)------------------------------
% (21359)------------------------------
fof(f107,plain,(
    ! [X0] :
      ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f105,f17])).

fof(f17,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

% (21341)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k5_xboole_0(X1,X1))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k5_xboole_0(X1,X1)) ) ),
    inference(factoring,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_xboole_0(X0,X0))
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f39,f19])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f29,f18])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | k5_xboole_0(X0,X0) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f35,f19])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f25,f18])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f561,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK1)
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(resolution,[],[f529,f232])).

fof(f232,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1,X1,X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f231])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(sK3(X1,X1,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(sK3(X1,X1,X1),X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f212,f117])).

fof(f117,plain,(
    ! [X14,X12,X13,X11] :
      ( ~ r2_hidden(sK3(X11,X12,X13),X12)
      | ~ r2_hidden(X14,X12)
      | r2_hidden(sK3(X11,X12,X13),X13)
      | ~ r2_hidden(X14,X13) ) ),
    inference(superposition,[],[f40,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1) ) ),
    inference(definition_unfolding,[],[f26,f18])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f212,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(factoring,[],[f146])).

fof(f146,plain,(
    ! [X17,X15,X18,X16] :
      ( r2_hidden(sK3(X15,X16,X17),X17)
      | ~ r2_hidden(X18,X16)
      | ~ r2_hidden(X18,X17)
      | r2_hidden(sK3(X15,X16,X17),X15) ) ),
    inference(superposition,[],[f40,f35])).

fof(f529,plain,
    ( ~ r2_hidden(sK3(sK1,sK1,sK1),sK1)
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(resolution,[],[f258,f152])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f151])).

fof(f258,plain,
    ( r2_hidden(sK3(sK1,sK1,sK1),sK2)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f256])).

fof(f582,plain,
    ( spl4_18
    | spl4_19
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f575,f256,f151,f382,f379])).

fof(f575,plain,
    ( ! [X8] :
        ( sK1 = k5_xboole_0(sK1,sK1)
        | ~ r1_tarski(sK1,X8) )
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(resolution,[],[f561,f334])).

fof(f334,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k5_xboole_0(X0,X0) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(factoring,[],[f138])).

fof(f521,plain,(
    ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f515])).

fof(f515,plain,
    ( $false
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f15,f380])).

fof(f380,plain,
    ( ! [X24] : ~ r1_tarski(sK1,X24)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f379])).

fof(f15,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f513,plain,
    ( spl4_18
    | spl4_32
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f508,f252,f480,f379])).

fof(f252,plain,
    ( spl4_12
  <=> ! [X25] : ~ r2_hidden(X25,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f508,plain,
    ( ! [X13] :
        ( k1_xboole_0 = k5_xboole_0(sK1,sK1)
        | ~ r1_tarski(sK1,X13) )
    | ~ spl4_12 ),
    inference(resolution,[],[f253,f327])).

fof(f253,plain,
    ( ! [X25] : ~ r2_hidden(X25,sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f252])).

fof(f512,plain,
    ( spl4_18
    | spl4_19
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f505,f252,f382,f379])).

fof(f505,plain,
    ( ! [X8] :
        ( sK1 = k5_xboole_0(sK1,sK1)
        | ~ r1_tarski(sK1,X8) )
    | ~ spl4_12 ),
    inference(resolution,[],[f253,f334])).

fof(f259,plain,
    ( spl4_13
    | spl4_12 ),
    inference(avatar_split_clause,[],[f243,f252,f256])).

fof(f243,plain,(
    ! [X26] :
      ( ~ r2_hidden(X26,sK1)
      | r2_hidden(sK3(sK1,sK1,sK1),sK2) ) ),
    inference(resolution,[],[f232,f134])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f132,f14])).

fof(f14,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f132,plain,(
    ! [X8,X7,X9] :
      ( ~ r1_tarski(X8,X9)
      | ~ r2_hidden(X7,X8)
      | r2_hidden(X7,X9) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X7,X8)
      | ~ r1_tarski(X8,X9)
      | ~ r2_hidden(X7,X8)
      | r2_hidden(X7,X9) ) ),
    inference(resolution,[],[f104,f37])).

fof(f104,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_tarski(X6,X7)
      | ~ r2_hidden(X4,X6)
      | ~ r1_tarski(X6,X5)
      | ~ r2_hidden(X4,X7)
      | r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f73,f64])).

fof(f159,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f13,f92])).

fof(f92,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f13,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f153,plain,
    ( ~ spl4_6
    | spl4_9 ),
    inference(avatar_split_clause,[],[f147,f151,f90])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f135,f70])).

fof(f70,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k3_subset_1(X3,X4))
      | ~ r2_hidden(X5,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f40,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f135,plain,(
    ! [X1] :
      ( r2_hidden(X1,k3_subset_1(sK0,sK2))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f132,f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (21343)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.48  % (21371)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (21362)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.49  % (21350)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.49  % (21354)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.50  % (21364)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (21371)Refutation not found, incomplete strategy% (21371)------------------------------
% 0.21/0.50  % (21371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21346)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (21345)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (21371)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21371)Memory used [KB]: 1663
% 0.21/0.51  % (21371)Time elapsed: 0.104 s
% 0.21/0.51  % (21371)------------------------------
% 0.21/0.51  % (21371)------------------------------
% 0.21/0.51  % (21344)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (21342)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (21342)Refutation not found, incomplete strategy% (21342)------------------------------
% 0.21/0.51  % (21342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21342)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21342)Memory used [KB]: 1663
% 0.21/0.51  % (21342)Time elapsed: 0.081 s
% 0.21/0.51  % (21342)------------------------------
% 0.21/0.51  % (21342)------------------------------
% 1.23/0.52  % (21347)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.52  % (21354)Refutation found. Thanks to Tanya!
% 1.23/0.52  % SZS status Theorem for theBenchmark
% 1.23/0.52  % SZS output start Proof for theBenchmark
% 1.23/0.52  fof(f609,plain,(
% 1.23/0.52    $false),
% 1.23/0.52    inference(avatar_sat_refutation,[],[f153,f159,f259,f512,f513,f521,f582,f583,f608])).
% 1.23/0.52  fof(f608,plain,(
% 1.23/0.52    ~spl4_19 | ~spl4_32),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f594])).
% 1.23/0.52  % (21359)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.23/0.52  fof(f594,plain,(
% 1.23/0.52    $false | (~spl4_19 | ~spl4_32)),
% 1.23/0.52    inference(subsumption_resolution,[],[f16,f588])).
% 1.23/0.52  fof(f588,plain,(
% 1.23/0.52    k1_xboole_0 = sK1 | (~spl4_19 | ~spl4_32)),
% 1.23/0.52    inference(superposition,[],[f482,f384])).
% 1.23/0.52  fof(f384,plain,(
% 1.23/0.52    sK1 = k5_xboole_0(sK1,sK1) | ~spl4_19),
% 1.23/0.52    inference(avatar_component_clause,[],[f382])).
% 1.23/0.52  fof(f382,plain,(
% 1.23/0.52    spl4_19 <=> sK1 = k5_xboole_0(sK1,sK1)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.23/0.52  fof(f482,plain,(
% 1.23/0.52    k1_xboole_0 = k5_xboole_0(sK1,sK1) | ~spl4_32),
% 1.23/0.52    inference(avatar_component_clause,[],[f480])).
% 1.23/0.52  fof(f480,plain,(
% 1.23/0.52    spl4_32 <=> k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.23/0.52  fof(f16,plain,(
% 1.23/0.52    k1_xboole_0 != sK1),
% 1.23/0.52    inference(cnf_transformation,[],[f10])).
% 1.23/0.52  % (21358)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.23/0.52  fof(f10,plain,(
% 1.23/0.52    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.23/0.52    inference(flattening,[],[f9])).
% 1.23/0.52  fof(f9,plain,(
% 1.23/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.23/0.52    inference(ennf_transformation,[],[f8])).
% 1.23/0.52  fof(f8,negated_conjecture,(
% 1.23/0.52    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.23/0.52    inference(negated_conjecture,[],[f7])).
% 1.23/0.52  fof(f7,conjecture,(
% 1.23/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 1.23/0.52  fof(f583,plain,(
% 1.23/0.52    spl4_18 | spl4_32 | ~spl4_9 | ~spl4_13),
% 1.23/0.52    inference(avatar_split_clause,[],[f578,f256,f151,f480,f379])).
% 1.23/0.52  fof(f379,plain,(
% 1.23/0.52    spl4_18 <=> ! [X24] : ~r1_tarski(sK1,X24)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.23/0.52  fof(f151,plain,(
% 1.23/0.52    spl4_9 <=> ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK2))),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.23/0.52  fof(f256,plain,(
% 1.23/0.52    spl4_13 <=> r2_hidden(sK3(sK1,sK1,sK1),sK2)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.23/0.52  fof(f578,plain,(
% 1.23/0.52    ( ! [X13] : (k1_xboole_0 = k5_xboole_0(sK1,sK1) | ~r1_tarski(sK1,X13)) ) | (~spl4_9 | ~spl4_13)),
% 1.23/0.52    inference(resolution,[],[f561,f327])).
% 1.23/0.52  fof(f327,plain,(
% 1.23/0.52    ( ! [X24,X25] : (r2_hidden(sK3(X24,X25,k1_xboole_0),X24) | k1_xboole_0 = k5_xboole_0(X24,X24) | ~r1_tarski(X24,X25)) )),
% 1.23/0.52    inference(resolution,[],[f138,f120])).
% 1.23/0.52  fof(f120,plain,(
% 1.23/0.52    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 1.23/0.52    inference(duplicate_literal_removal,[],[f119])).
% 1.23/0.52  fof(f119,plain,(
% 1.23/0.52    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,k1_xboole_0)) )),
% 1.23/0.52    inference(resolution,[],[f110,f37])).
% 1.23/0.52  fof(f37,plain,(
% 1.23/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.23/0.52    inference(equality_resolution,[],[f22])).
% 1.23/0.52  fof(f22,plain,(
% 1.23/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.23/0.52    inference(cnf_transformation,[],[f2])).
% 1.23/0.52  fof(f2,axiom,(
% 1.23/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.23/0.52  fof(f110,plain,(
% 1.23/0.52    ( ! [X2,X3] : (~r1_tarski(k1_xboole_0,X3) | ~r2_hidden(X2,X3) | ~r2_hidden(X2,k1_xboole_0)) )),
% 1.23/0.52    inference(resolution,[],[f107,f64])).
% 1.23/0.52  fof(f64,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(X0,X0)) | ~r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.23/0.52    inference(superposition,[],[f40,f19])).
% 1.23/0.52  fof(f19,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f11])).
% 1.23/0.52  % (21355)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.23/0.52  fof(f11,plain,(
% 1.23/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.23/0.52    inference(ennf_transformation,[],[f4])).
% 1.23/0.52  fof(f4,axiom,(
% 1.23/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.23/0.52  fof(f40,plain,(
% 1.23/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 1.23/0.52    inference(equality_resolution,[],[f32])).
% 1.23/0.52  fof(f32,plain,(
% 1.23/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.23/0.52    inference(definition_unfolding,[],[f28,f18])).
% 1.23/0.52  fof(f18,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.23/0.52    inference(cnf_transformation,[],[f3])).
% 1.23/0.52  fof(f3,axiom,(
% 1.23/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.23/0.52  fof(f28,plain,(
% 1.23/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.23/0.52    inference(cnf_transformation,[],[f1])).
% 1.23/0.52  fof(f1,axiom,(
% 1.23/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.23/0.52  % (21359)Refutation not found, incomplete strategy% (21359)------------------------------
% 1.23/0.52  % (21359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (21359)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.52  
% 1.23/0.52  % (21359)Memory used [KB]: 1663
% 1.23/0.52  % (21359)Time elapsed: 0.124 s
% 1.23/0.52  % (21359)------------------------------
% 1.23/0.52  % (21359)------------------------------
% 1.23/0.52  fof(f107,plain,(
% 1.23/0.52    ( ! [X0] : (r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.23/0.52    inference(resolution,[],[f105,f17])).
% 1.23/0.52  fof(f17,plain,(
% 1.23/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f5])).
% 1.23/0.52  fof(f5,axiom,(
% 1.23/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.23/0.52  % (21341)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.23/0.52  fof(f105,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~r1_tarski(X1,k5_xboole_0(X1,X1)) | ~r2_hidden(X0,X1) | r2_hidden(X0,k5_xboole_0(X1,X1))) )),
% 1.23/0.52    inference(factoring,[],[f73])).
% 1.23/0.52  fof(f73,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_xboole_0(X0,X0)) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.23/0.52    inference(superposition,[],[f39,f19])).
% 1.23/0.52  fof(f39,plain,(
% 1.23/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.23/0.52    inference(equality_resolution,[],[f31])).
% 1.23/0.52  fof(f31,plain,(
% 1.23/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.23/0.52    inference(definition_unfolding,[],[f29,f18])).
% 1.23/0.52  fof(f29,plain,(
% 1.23/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.23/0.52    inference(cnf_transformation,[],[f1])).
% 1.23/0.52  fof(f138,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | k5_xboole_0(X0,X0) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | ~r1_tarski(X0,X1)) )),
% 1.23/0.52    inference(superposition,[],[f35,f19])).
% 1.23/0.52  fof(f35,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0)) )),
% 1.23/0.52    inference(definition_unfolding,[],[f25,f18])).
% 1.23/0.52  fof(f25,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.23/0.52    inference(cnf_transformation,[],[f1])).
% 1.23/0.52  fof(f561,plain,(
% 1.23/0.52    ( ! [X4] : (~r2_hidden(X4,sK1)) ) | (~spl4_9 | ~spl4_13)),
% 1.23/0.52    inference(resolution,[],[f529,f232])).
% 1.23/0.52  fof(f232,plain,(
% 1.23/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X1,X1,X1),X1) | ~r2_hidden(X0,X1)) )),
% 1.23/0.52    inference(condensation,[],[f231])).
% 1.23/0.52  fof(f231,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,X1) | r2_hidden(sK3(X1,X1,X1),X1)) )),
% 1.23/0.52    inference(duplicate_literal_removal,[],[f217])).
% 1.23/0.52  fof(f217,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,X1) | r2_hidden(sK3(X1,X1,X1),X1) | ~r2_hidden(X2,X1)) )),
% 1.23/0.52    inference(resolution,[],[f212,f117])).
% 1.23/0.52  fof(f117,plain,(
% 1.23/0.52    ( ! [X14,X12,X13,X11] : (~r2_hidden(sK3(X11,X12,X13),X12) | ~r2_hidden(X14,X12) | r2_hidden(sK3(X11,X12,X13),X13) | ~r2_hidden(X14,X13)) )),
% 1.23/0.52    inference(superposition,[],[f40,f34])).
% 1.23/0.52  fof(f34,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) )),
% 1.23/0.52    inference(definition_unfolding,[],[f26,f18])).
% 1.23/0.52  fof(f26,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.23/0.52    inference(cnf_transformation,[],[f1])).
% 1.23/0.52  fof(f212,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.23/0.52    inference(factoring,[],[f146])).
% 1.23/0.52  fof(f146,plain,(
% 1.23/0.52    ( ! [X17,X15,X18,X16] : (r2_hidden(sK3(X15,X16,X17),X17) | ~r2_hidden(X18,X16) | ~r2_hidden(X18,X17) | r2_hidden(sK3(X15,X16,X17),X15)) )),
% 1.23/0.52    inference(superposition,[],[f40,f35])).
% 1.23/0.52  fof(f529,plain,(
% 1.23/0.52    ~r2_hidden(sK3(sK1,sK1,sK1),sK1) | (~spl4_9 | ~spl4_13)),
% 1.23/0.52    inference(resolution,[],[f258,f152])).
% 1.23/0.52  fof(f152,plain,(
% 1.23/0.52    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1)) ) | ~spl4_9),
% 1.23/0.52    inference(avatar_component_clause,[],[f151])).
% 1.23/0.52  fof(f258,plain,(
% 1.23/0.52    r2_hidden(sK3(sK1,sK1,sK1),sK2) | ~spl4_13),
% 1.23/0.52    inference(avatar_component_clause,[],[f256])).
% 1.23/0.52  fof(f582,plain,(
% 1.23/0.52    spl4_18 | spl4_19 | ~spl4_9 | ~spl4_13),
% 1.23/0.52    inference(avatar_split_clause,[],[f575,f256,f151,f382,f379])).
% 1.23/0.52  fof(f575,plain,(
% 1.23/0.52    ( ! [X8] : (sK1 = k5_xboole_0(sK1,sK1) | ~r1_tarski(sK1,X8)) ) | (~spl4_9 | ~spl4_13)),
% 1.23/0.52    inference(resolution,[],[f561,f334])).
% 1.23/0.52  fof(f334,plain,(
% 1.23/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k5_xboole_0(X0,X0) = X0 | ~r1_tarski(X0,X1)) )),
% 1.23/0.52    inference(factoring,[],[f138])).
% 1.23/0.52  fof(f521,plain,(
% 1.23/0.52    ~spl4_18),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f515])).
% 1.23/0.52  fof(f515,plain,(
% 1.23/0.52    $false | ~spl4_18),
% 1.23/0.52    inference(subsumption_resolution,[],[f15,f380])).
% 1.23/0.52  fof(f380,plain,(
% 1.23/0.52    ( ! [X24] : (~r1_tarski(sK1,X24)) ) | ~spl4_18),
% 1.23/0.52    inference(avatar_component_clause,[],[f379])).
% 1.23/0.52  fof(f15,plain,(
% 1.23/0.52    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.23/0.52    inference(cnf_transformation,[],[f10])).
% 1.23/0.52  fof(f513,plain,(
% 1.23/0.52    spl4_18 | spl4_32 | ~spl4_12),
% 1.23/0.52    inference(avatar_split_clause,[],[f508,f252,f480,f379])).
% 1.23/0.52  fof(f252,plain,(
% 1.23/0.52    spl4_12 <=> ! [X25] : ~r2_hidden(X25,sK1)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.23/0.52  fof(f508,plain,(
% 1.23/0.52    ( ! [X13] : (k1_xboole_0 = k5_xboole_0(sK1,sK1) | ~r1_tarski(sK1,X13)) ) | ~spl4_12),
% 1.23/0.52    inference(resolution,[],[f253,f327])).
% 1.23/0.52  fof(f253,plain,(
% 1.23/0.52    ( ! [X25] : (~r2_hidden(X25,sK1)) ) | ~spl4_12),
% 1.23/0.52    inference(avatar_component_clause,[],[f252])).
% 1.23/0.52  fof(f512,plain,(
% 1.23/0.52    spl4_18 | spl4_19 | ~spl4_12),
% 1.23/0.52    inference(avatar_split_clause,[],[f505,f252,f382,f379])).
% 1.23/0.52  fof(f505,plain,(
% 1.23/0.52    ( ! [X8] : (sK1 = k5_xboole_0(sK1,sK1) | ~r1_tarski(sK1,X8)) ) | ~spl4_12),
% 1.23/0.52    inference(resolution,[],[f253,f334])).
% 1.23/0.52  fof(f259,plain,(
% 1.23/0.52    spl4_13 | spl4_12),
% 1.23/0.52    inference(avatar_split_clause,[],[f243,f252,f256])).
% 1.23/0.52  fof(f243,plain,(
% 1.23/0.52    ( ! [X26] : (~r2_hidden(X26,sK1) | r2_hidden(sK3(sK1,sK1,sK1),sK2)) )),
% 1.23/0.52    inference(resolution,[],[f232,f134])).
% 1.23/0.52  fof(f134,plain,(
% 1.23/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK2)) )),
% 1.23/0.52    inference(resolution,[],[f132,f14])).
% 1.23/0.52  fof(f14,plain,(
% 1.23/0.52    r1_tarski(sK1,sK2)),
% 1.23/0.52    inference(cnf_transformation,[],[f10])).
% 1.23/0.52  fof(f132,plain,(
% 1.23/0.52    ( ! [X8,X7,X9] : (~r1_tarski(X8,X9) | ~r2_hidden(X7,X8) | r2_hidden(X7,X9)) )),
% 1.23/0.52    inference(duplicate_literal_removal,[],[f131])).
% 1.23/0.52  fof(f131,plain,(
% 1.23/0.52    ( ! [X8,X7,X9] : (~r2_hidden(X7,X8) | ~r1_tarski(X8,X9) | ~r2_hidden(X7,X8) | r2_hidden(X7,X9)) )),
% 1.23/0.52    inference(resolution,[],[f104,f37])).
% 1.23/0.52  fof(f104,plain,(
% 1.23/0.52    ( ! [X6,X4,X7,X5] : (~r1_tarski(X6,X7) | ~r2_hidden(X4,X6) | ~r1_tarski(X6,X5) | ~r2_hidden(X4,X7) | r2_hidden(X4,X5)) )),
% 1.23/0.52    inference(resolution,[],[f73,f64])).
% 1.23/0.52  fof(f159,plain,(
% 1.23/0.52    spl4_6),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f158])).
% 1.23/0.52  fof(f158,plain,(
% 1.23/0.52    $false | spl4_6),
% 1.23/0.52    inference(subsumption_resolution,[],[f13,f92])).
% 1.23/0.53  fof(f92,plain,(
% 1.23/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl4_6),
% 1.23/0.53    inference(avatar_component_clause,[],[f90])).
% 1.23/0.53  fof(f90,plain,(
% 1.23/0.53    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.23/0.53  fof(f13,plain,(
% 1.23/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.23/0.53    inference(cnf_transformation,[],[f10])).
% 1.23/0.53  fof(f153,plain,(
% 1.23/0.53    ~spl4_6 | spl4_9),
% 1.23/0.53    inference(avatar_split_clause,[],[f147,f151,f90])).
% 1.23/0.53  fof(f147,plain,(
% 1.23/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))) )),
% 1.23/0.53    inference(resolution,[],[f135,f70])).
% 1.23/0.53  fof(f70,plain,(
% 1.23/0.53    ( ! [X4,X5,X3] : (~r2_hidden(X5,k3_subset_1(X3,X4)) | ~r2_hidden(X5,X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3))) )),
% 1.23/0.53    inference(superposition,[],[f40,f30])).
% 1.23/0.53  fof(f30,plain,(
% 1.23/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.23/0.53    inference(definition_unfolding,[],[f20,f18])).
% 1.23/0.53  fof(f20,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f12])).
% 1.23/0.53  fof(f12,plain,(
% 1.23/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.23/0.53    inference(ennf_transformation,[],[f6])).
% 1.23/0.53  fof(f6,axiom,(
% 1.23/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.23/0.53  fof(f135,plain,(
% 1.23/0.53    ( ! [X1] : (r2_hidden(X1,k3_subset_1(sK0,sK2)) | ~r2_hidden(X1,sK1)) )),
% 1.23/0.53    inference(resolution,[],[f132,f15])).
% 1.23/0.53  % SZS output end Proof for theBenchmark
% 1.23/0.53  % (21354)------------------------------
% 1.23/0.53  % (21354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (21354)Termination reason: Refutation
% 1.23/0.53  
% 1.23/0.53  % (21354)Memory used [KB]: 6524
% 1.23/0.53  % (21354)Time elapsed: 0.121 s
% 1.23/0.53  % (21354)------------------------------
% 1.23/0.53  % (21354)------------------------------
% 1.23/0.53  % (21353)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.23/0.53  % (21340)Success in time 0.168 s
%------------------------------------------------------------------------------
