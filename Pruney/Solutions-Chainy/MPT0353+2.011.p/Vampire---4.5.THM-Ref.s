%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:22 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 199 expanded)
%              Number of leaves         :   31 (  80 expanded)
%              Depth                    :   11
%              Number of atoms          :  285 ( 554 expanded)
%              Number of equality atoms :   71 ( 137 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f823,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f60,f64,f81,f85,f100,f106,f127,f154,f167,f173,f383,f390,f394,f399,f820])).

fof(f820,plain,
    ( ~ spl4_3
    | ~ spl4_9
    | spl4_46 ),
    inference(avatar_contradiction_clause,[],[f819])).

% (25380)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f819,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_9
    | spl4_46 ),
    inference(subsumption_resolution,[],[f398,f813])).

fof(f813,plain,
    ( ! [X1] : k3_xboole_0(sK1,k5_xboole_0(sK0,X1)) = k7_subset_1(sK0,sK1,X1)
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(superposition,[],[f766,f276])).

fof(f276,plain,
    ( ! [X10] : k5_xboole_0(sK1,k3_xboole_0(X10,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X10))
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f259,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f259,plain,
    ( ! [X10] : k3_xboole_0(k5_xboole_0(sK0,X10),sK1) = k5_xboole_0(sK1,k3_xboole_0(X10,sK1))
    | ~ spl4_9 ),
    inference(superposition,[],[f45,f115])).

fof(f115,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_9
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f766,plain,
    ( ! [X0] : k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k7_subset_1(sK0,sK1,X0)
    | ~ spl4_3 ),
    inference(superposition,[],[f726,f33])).

fof(f726,plain,
    ( ! [X1] : k5_xboole_0(sK1,k3_xboole_0(sK1,X1)) = k7_subset_1(sK0,sK1,X1)
    | ~ spl4_3 ),
    inference(resolution,[],[f50,f63])).

fof(f63,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f46,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

% (25366)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f398,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))
    | spl4_46 ),
    inference(avatar_component_clause,[],[f397])).

fof(f397,plain,
    ( spl4_46
  <=> k7_subset_1(sK0,sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f399,plain,
    ( ~ spl4_46
    | spl4_16
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f395,f381,f152,f397])).

fof(f152,plain,
    ( spl4_16
  <=> k7_subset_1(sK0,sK1,sK2) = k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f381,plain,
    ( spl4_44
  <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f395,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))
    | spl4_16
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f153,f382])).

fof(f382,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f381])).

fof(f153,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f152])).

fof(f394,plain,(
    ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f391])).

fof(f391,plain,
    ( $false
    | ~ spl4_18 ),
    inference(resolution,[],[f163,f31])).

fof(f31,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f163,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_18
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f390,plain,
    ( k3_subset_1(sK0,sK2) != k5_xboole_0(sK0,sK2)
    | r1_tarski(k3_subset_1(sK0,sK2),sK0)
    | ~ r1_tarski(k5_xboole_0(sK0,sK2),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f383,plain,
    ( spl4_44
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f379,f93,f58,f381])).

fof(f58,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f93,plain,
    ( spl4_6
  <=> sK2 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f379,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f376,f94])).

fof(f94,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f376,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl4_2 ),
    inference(resolution,[],[f49,f59])).

fof(f59,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f173,plain,
    ( ~ spl4_20
    | spl4_19 ),
    inference(avatar_split_clause,[],[f168,f165,f171])).

fof(f171,plain,
    ( spl4_20
  <=> r1_tarski(k3_subset_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f165,plain,
    ( spl4_19
  <=> r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f168,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK0)
    | spl4_19 ),
    inference(resolution,[],[f166,f51])).

fof(f51,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f166,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f165])).

fof(f167,plain,
    ( spl4_18
    | ~ spl4_19
    | spl4_15 ),
    inference(avatar_split_clause,[],[f160,f149,f165,f162])).

fof(f149,plain,
    ( spl4_15
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f160,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl4_15 ),
    inference(resolution,[],[f150,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f150,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f149])).

fof(f154,plain,
    ( ~ spl4_15
    | ~ spl4_16
    | spl4_1 ),
    inference(avatar_split_clause,[],[f147,f54,f152,f149])).

fof(f54,plain,
    ( spl4_1
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f147,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(superposition,[],[f55,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f55,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f127,plain,
    ( spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f112,f83,f114])).

fof(f83,plain,
    ( spl4_5
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f112,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl4_5 ),
    inference(superposition,[],[f33,f84])).

fof(f84,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f106,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f91,f79,f93])).

fof(f79,plain,
    ( spl4_4
  <=> sK2 = k3_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f91,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl4_4 ),
    inference(superposition,[],[f33,f80])).

fof(f80,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f100,plain,
    ( spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f88,f79,f98])).

fof(f98,plain,
    ( spl4_7
  <=> r1_tarski(k5_xboole_0(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f88,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK2),sK0)
    | ~ spl4_4 ),
    inference(superposition,[],[f65,f80])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f48,f33])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f85,plain,
    ( spl4_5
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f76,f62,f83])).

fof(f76,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f74,f63])).

fof(f74,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k3_xboole_0(X2,X3) = X2 ) ),
    inference(global_subsumption,[],[f31,f73])).

fof(f73,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | v1_xboole_0(k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f71,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_zfmisc_1(X5))
      | k3_xboole_0(X4,X5) = X4 ) ),
    inference(resolution,[],[f39,f52])).

fof(f52,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f81,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f75,f58,f79])).

fof(f75,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f74,f59])).

fof(f64,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f60,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f29,f58])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f30,f54])).

fof(f30,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (25362)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (25385)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (25377)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.24/0.52  % (25358)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.53  % (25376)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.24/0.53  % (25360)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.53  % (25359)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.53  % (25387)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.24/0.53  % (25361)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.53  % (25364)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.24/0.53  % (25375)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.54  % (25386)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.54  % (25379)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.54  % (25384)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (25381)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.55  % (25378)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.55  % (25367)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.55  % (25369)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.55  % (25367)Refutation not found, incomplete strategy% (25367)------------------------------
% 1.36/0.55  % (25367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (25367)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (25367)Memory used [KB]: 10618
% 1.36/0.55  % (25367)Time elapsed: 0.137 s
% 1.36/0.55  % (25367)------------------------------
% 1.36/0.55  % (25367)------------------------------
% 1.36/0.55  % (25369)Refutation not found, incomplete strategy% (25369)------------------------------
% 1.36/0.55  % (25369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (25369)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (25369)Memory used [KB]: 10618
% 1.36/0.55  % (25369)Time elapsed: 0.138 s
% 1.36/0.55  % (25369)------------------------------
% 1.36/0.55  % (25369)------------------------------
% 1.36/0.55  % (25373)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.55  % (25371)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.55  % (25373)Refutation not found, incomplete strategy% (25373)------------------------------
% 1.36/0.55  % (25373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (25373)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (25373)Memory used [KB]: 6140
% 1.36/0.55  % (25373)Time elapsed: 0.002 s
% 1.36/0.55  % (25373)------------------------------
% 1.36/0.55  % (25373)------------------------------
% 1.36/0.55  % (25370)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.55  % (25357)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.55  % (25365)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.55  % (25357)Refutation not found, incomplete strategy% (25357)------------------------------
% 1.36/0.55  % (25357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (25357)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (25357)Memory used [KB]: 1663
% 1.36/0.55  % (25357)Time elapsed: 0.140 s
% 1.36/0.55  % (25357)------------------------------
% 1.36/0.55  % (25357)------------------------------
% 1.36/0.55  % (25374)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.55  % (25375)Refutation not found, incomplete strategy% (25375)------------------------------
% 1.36/0.55  % (25375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (25375)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (25375)Memory used [KB]: 10618
% 1.36/0.56  % (25375)Time elapsed: 0.147 s
% 1.36/0.56  % (25375)------------------------------
% 1.36/0.56  % (25375)------------------------------
% 1.36/0.56  % (25377)Refutation found. Thanks to Tanya!
% 1.36/0.56  % SZS status Theorem for theBenchmark
% 1.36/0.56  % (25383)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.56  % (25382)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.56  % SZS output start Proof for theBenchmark
% 1.36/0.56  fof(f823,plain,(
% 1.36/0.56    $false),
% 1.36/0.56    inference(avatar_sat_refutation,[],[f56,f60,f64,f81,f85,f100,f106,f127,f154,f167,f173,f383,f390,f394,f399,f820])).
% 1.36/0.56  fof(f820,plain,(
% 1.36/0.56    ~spl4_3 | ~spl4_9 | spl4_46),
% 1.36/0.56    inference(avatar_contradiction_clause,[],[f819])).
% 1.36/0.56  % (25380)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.56  fof(f819,plain,(
% 1.36/0.56    $false | (~spl4_3 | ~spl4_9 | spl4_46)),
% 1.36/0.56    inference(subsumption_resolution,[],[f398,f813])).
% 1.36/0.56  fof(f813,plain,(
% 1.36/0.56    ( ! [X1] : (k3_xboole_0(sK1,k5_xboole_0(sK0,X1)) = k7_subset_1(sK0,sK1,X1)) ) | (~spl4_3 | ~spl4_9)),
% 1.36/0.56    inference(superposition,[],[f766,f276])).
% 1.36/0.56  fof(f276,plain,(
% 1.36/0.56    ( ! [X10] : (k5_xboole_0(sK1,k3_xboole_0(X10,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X10))) ) | ~spl4_9),
% 1.36/0.56    inference(forward_demodulation,[],[f259,f33])).
% 1.36/0.56  fof(f33,plain,(
% 1.36/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f1])).
% 1.36/0.56  fof(f1,axiom,(
% 1.36/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.36/0.56  fof(f259,plain,(
% 1.36/0.56    ( ! [X10] : (k3_xboole_0(k5_xboole_0(sK0,X10),sK1) = k5_xboole_0(sK1,k3_xboole_0(X10,sK1))) ) | ~spl4_9),
% 1.36/0.56    inference(superposition,[],[f45,f115])).
% 1.36/0.56  fof(f115,plain,(
% 1.36/0.56    sK1 = k3_xboole_0(sK0,sK1) | ~spl4_9),
% 1.36/0.56    inference(avatar_component_clause,[],[f114])).
% 1.36/0.56  fof(f114,plain,(
% 1.36/0.56    spl4_9 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.36/0.56  fof(f45,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f3])).
% 1.36/0.56  fof(f3,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.36/0.56  fof(f766,plain,(
% 1.36/0.56    ( ! [X0] : (k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k7_subset_1(sK0,sK1,X0)) ) | ~spl4_3),
% 1.36/0.56    inference(superposition,[],[f726,f33])).
% 1.36/0.56  fof(f726,plain,(
% 1.36/0.56    ( ! [X1] : (k5_xboole_0(sK1,k3_xboole_0(sK1,X1)) = k7_subset_1(sK0,sK1,X1)) ) | ~spl4_3),
% 1.36/0.56    inference(resolution,[],[f50,f63])).
% 1.36/0.56  fof(f63,plain,(
% 1.36/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_3),
% 1.36/0.56    inference(avatar_component_clause,[],[f62])).
% 1.36/0.56  fof(f62,plain,(
% 1.36/0.56    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.36/0.56  fof(f50,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 1.36/0.56    inference(definition_unfolding,[],[f46,f34])).
% 1.36/0.56  fof(f34,plain,(
% 1.36/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f2])).
% 1.36/0.56  fof(f2,axiom,(
% 1.36/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.36/0.56  fof(f46,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f18])).
% 1.36/0.56  fof(f18,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.56    inference(ennf_transformation,[],[f10])).
% 1.36/0.56  fof(f10,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.36/0.56  % (25366)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.56  fof(f398,plain,(
% 1.36/0.56    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) | spl4_46),
% 1.36/0.56    inference(avatar_component_clause,[],[f397])).
% 1.36/0.56  fof(f397,plain,(
% 1.36/0.56    spl4_46 <=> k7_subset_1(sK0,sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.36/0.56  fof(f399,plain,(
% 1.36/0.56    ~spl4_46 | spl4_16 | ~spl4_44),
% 1.36/0.56    inference(avatar_split_clause,[],[f395,f381,f152,f397])).
% 1.36/0.56  fof(f152,plain,(
% 1.36/0.56    spl4_16 <=> k7_subset_1(sK0,sK1,sK2) = k3_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.36/0.56  fof(f381,plain,(
% 1.36/0.56    spl4_44 <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.36/0.56  fof(f395,plain,(
% 1.36/0.56    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) | (spl4_16 | ~spl4_44)),
% 1.36/0.56    inference(forward_demodulation,[],[f153,f382])).
% 1.36/0.56  fof(f382,plain,(
% 1.36/0.56    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | ~spl4_44),
% 1.36/0.56    inference(avatar_component_clause,[],[f381])).
% 1.36/0.56  fof(f153,plain,(
% 1.36/0.56    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) | spl4_16),
% 1.36/0.56    inference(avatar_component_clause,[],[f152])).
% 1.36/0.56  fof(f394,plain,(
% 1.36/0.56    ~spl4_18),
% 1.36/0.56    inference(avatar_contradiction_clause,[],[f391])).
% 1.36/0.56  fof(f391,plain,(
% 1.36/0.56    $false | ~spl4_18),
% 1.36/0.56    inference(resolution,[],[f163,f31])).
% 1.36/0.56  fof(f31,plain,(
% 1.36/0.56    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f9])).
% 1.36/0.56  fof(f9,axiom,(
% 1.36/0.56    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.36/0.56  fof(f163,plain,(
% 1.36/0.56    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_18),
% 1.36/0.56    inference(avatar_component_clause,[],[f162])).
% 1.36/0.56  fof(f162,plain,(
% 1.36/0.56    spl4_18 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.36/0.56  fof(f390,plain,(
% 1.36/0.56    k3_subset_1(sK0,sK2) != k5_xboole_0(sK0,sK2) | r1_tarski(k3_subset_1(sK0,sK2),sK0) | ~r1_tarski(k5_xboole_0(sK0,sK2),sK0)),
% 1.36/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.36/0.56  fof(f383,plain,(
% 1.36/0.56    spl4_44 | ~spl4_2 | ~spl4_6),
% 1.36/0.56    inference(avatar_split_clause,[],[f379,f93,f58,f381])).
% 1.36/0.56  fof(f58,plain,(
% 1.36/0.56    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.36/0.56  fof(f93,plain,(
% 1.36/0.56    spl4_6 <=> sK2 = k3_xboole_0(sK0,sK2)),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.36/0.56  fof(f379,plain,(
% 1.36/0.56    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | (~spl4_2 | ~spl4_6)),
% 1.36/0.56    inference(forward_demodulation,[],[f376,f94])).
% 1.36/0.56  fof(f94,plain,(
% 1.36/0.56    sK2 = k3_xboole_0(sK0,sK2) | ~spl4_6),
% 1.36/0.56    inference(avatar_component_clause,[],[f93])).
% 1.36/0.56  fof(f376,plain,(
% 1.36/0.56    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl4_2),
% 1.36/0.56    inference(resolution,[],[f49,f59])).
% 1.36/0.56  fof(f59,plain,(
% 1.36/0.56    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_2),
% 1.36/0.56    inference(avatar_component_clause,[],[f58])).
% 1.36/0.56  fof(f49,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.36/0.56    inference(definition_unfolding,[],[f40,f34])).
% 1.36/0.56  fof(f40,plain,(
% 1.36/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f17])).
% 1.36/0.56  fof(f17,plain,(
% 1.36/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.56    inference(ennf_transformation,[],[f8])).
% 1.36/0.56  fof(f8,axiom,(
% 1.36/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.36/0.56  fof(f173,plain,(
% 1.36/0.56    ~spl4_20 | spl4_19),
% 1.36/0.56    inference(avatar_split_clause,[],[f168,f165,f171])).
% 1.36/0.56  fof(f171,plain,(
% 1.36/0.56    spl4_20 <=> r1_tarski(k3_subset_1(sK0,sK2),sK0)),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.36/0.56  fof(f165,plain,(
% 1.36/0.56    spl4_19 <=> r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.36/0.56  fof(f168,plain,(
% 1.36/0.56    ~r1_tarski(k3_subset_1(sK0,sK2),sK0) | spl4_19),
% 1.36/0.56    inference(resolution,[],[f166,f51])).
% 1.36/0.56  fof(f51,plain,(
% 1.36/0.56    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.36/0.56    inference(equality_resolution,[],[f42])).
% 1.36/0.56  fof(f42,plain,(
% 1.36/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.36/0.56    inference(cnf_transformation,[],[f27])).
% 1.36/0.56  fof(f27,plain,(
% 1.36/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.36/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 1.36/0.56  fof(f26,plain,(
% 1.36/0.56    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.36/0.56    introduced(choice_axiom,[])).
% 1.36/0.56  fof(f25,plain,(
% 1.36/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.36/0.56    inference(rectify,[],[f24])).
% 1.36/0.56  fof(f24,plain,(
% 1.36/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.36/0.56    inference(nnf_transformation,[],[f6])).
% 1.36/0.56  fof(f6,axiom,(
% 1.36/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.36/0.56  fof(f166,plain,(
% 1.36/0.56    ~r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | spl4_19),
% 1.36/0.56    inference(avatar_component_clause,[],[f165])).
% 1.36/0.56  fof(f167,plain,(
% 1.36/0.56    spl4_18 | ~spl4_19 | spl4_15),
% 1.36/0.56    inference(avatar_split_clause,[],[f160,f149,f165,f162])).
% 1.36/0.56  fof(f149,plain,(
% 1.36/0.56    spl4_15 <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.36/0.56  fof(f160,plain,(
% 1.36/0.56    ~r2_hidden(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | spl4_15),
% 1.36/0.56    inference(resolution,[],[f150,f36])).
% 1.36/0.56  fof(f36,plain,(
% 1.36/0.56    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f23])).
% 1.36/0.56  fof(f23,plain,(
% 1.36/0.56    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.36/0.56    inference(nnf_transformation,[],[f15])).
% 1.36/0.56  fof(f15,plain,(
% 1.36/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.36/0.56    inference(ennf_transformation,[],[f7])).
% 1.36/0.56  fof(f7,axiom,(
% 1.36/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.36/0.56  fof(f150,plain,(
% 1.36/0.56    ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | spl4_15),
% 1.36/0.56    inference(avatar_component_clause,[],[f149])).
% 1.36/0.56  fof(f154,plain,(
% 1.36/0.56    ~spl4_15 | ~spl4_16 | spl4_1),
% 1.36/0.56    inference(avatar_split_clause,[],[f147,f54,f152,f149])).
% 1.36/0.56  fof(f54,plain,(
% 1.36/0.56    spl4_1 <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.36/0.56  fof(f147,plain,(
% 1.36/0.56    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) | ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | spl4_1),
% 1.36/0.56    inference(superposition,[],[f55,f47])).
% 1.36/0.56  fof(f47,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f19])).
% 1.36/0.56  fof(f19,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.36/0.56    inference(ennf_transformation,[],[f11])).
% 1.36/0.56  fof(f11,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.36/0.56  fof(f55,plain,(
% 1.36/0.56    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) | spl4_1),
% 1.36/0.56    inference(avatar_component_clause,[],[f54])).
% 1.36/0.56  fof(f127,plain,(
% 1.36/0.56    spl4_9 | ~spl4_5),
% 1.36/0.56    inference(avatar_split_clause,[],[f112,f83,f114])).
% 1.36/0.56  fof(f83,plain,(
% 1.36/0.56    spl4_5 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.36/0.56  fof(f112,plain,(
% 1.36/0.56    sK1 = k3_xboole_0(sK0,sK1) | ~spl4_5),
% 1.36/0.56    inference(superposition,[],[f33,f84])).
% 1.36/0.56  fof(f84,plain,(
% 1.36/0.56    sK1 = k3_xboole_0(sK1,sK0) | ~spl4_5),
% 1.36/0.56    inference(avatar_component_clause,[],[f83])).
% 1.36/0.56  fof(f106,plain,(
% 1.36/0.56    spl4_6 | ~spl4_4),
% 1.36/0.56    inference(avatar_split_clause,[],[f91,f79,f93])).
% 1.36/0.56  fof(f79,plain,(
% 1.36/0.56    spl4_4 <=> sK2 = k3_xboole_0(sK2,sK0)),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.36/0.56  fof(f91,plain,(
% 1.36/0.56    sK2 = k3_xboole_0(sK0,sK2) | ~spl4_4),
% 1.36/0.56    inference(superposition,[],[f33,f80])).
% 1.36/0.56  fof(f80,plain,(
% 1.36/0.56    sK2 = k3_xboole_0(sK2,sK0) | ~spl4_4),
% 1.36/0.56    inference(avatar_component_clause,[],[f79])).
% 1.36/0.56  fof(f100,plain,(
% 1.36/0.56    spl4_7 | ~spl4_4),
% 1.36/0.56    inference(avatar_split_clause,[],[f88,f79,f98])).
% 1.36/0.56  fof(f98,plain,(
% 1.36/0.56    spl4_7 <=> r1_tarski(k5_xboole_0(sK0,sK2),sK0)),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.36/0.56  fof(f88,plain,(
% 1.36/0.56    r1_tarski(k5_xboole_0(sK0,sK2),sK0) | ~spl4_4),
% 1.36/0.56    inference(superposition,[],[f65,f80])).
% 1.36/0.56  fof(f65,plain,(
% 1.36/0.56    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0)) )),
% 1.36/0.56    inference(superposition,[],[f48,f33])).
% 1.36/0.56  fof(f48,plain,(
% 1.36/0.56    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.36/0.56    inference(definition_unfolding,[],[f32,f34])).
% 1.36/0.56  fof(f32,plain,(
% 1.36/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f5])).
% 1.36/0.56  fof(f5,axiom,(
% 1.36/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.36/0.56  fof(f85,plain,(
% 1.36/0.56    spl4_5 | ~spl4_3),
% 1.36/0.56    inference(avatar_split_clause,[],[f76,f62,f83])).
% 1.36/0.56  fof(f76,plain,(
% 1.36/0.56    sK1 = k3_xboole_0(sK1,sK0) | ~spl4_3),
% 1.36/0.56    inference(resolution,[],[f74,f63])).
% 1.36/0.56  fof(f74,plain,(
% 1.36/0.56    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | k3_xboole_0(X2,X3) = X2) )),
% 1.36/0.56    inference(global_subsumption,[],[f31,f73])).
% 1.36/0.56  fof(f73,plain,(
% 1.36/0.56    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | v1_xboole_0(k1_zfmisc_1(X3))) )),
% 1.36/0.56    inference(resolution,[],[f71,f35])).
% 1.36/0.56  fof(f35,plain,(
% 1.36/0.56    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f23])).
% 1.36/0.56  fof(f71,plain,(
% 1.36/0.56    ( ! [X4,X5] : (~r2_hidden(X4,k1_zfmisc_1(X5)) | k3_xboole_0(X4,X5) = X4) )),
% 1.36/0.56    inference(resolution,[],[f39,f52])).
% 1.36/0.56  fof(f52,plain,(
% 1.36/0.56    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.36/0.56    inference(equality_resolution,[],[f41])).
% 1.36/0.56  fof(f41,plain,(
% 1.36/0.56    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.36/0.56    inference(cnf_transformation,[],[f27])).
% 1.36/0.56  fof(f39,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.36/0.56    inference(cnf_transformation,[],[f16])).
% 1.36/0.56  fof(f16,plain,(
% 1.36/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.36/0.56    inference(ennf_transformation,[],[f4])).
% 1.36/0.56  fof(f4,axiom,(
% 1.36/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.36/0.56  fof(f81,plain,(
% 1.36/0.56    spl4_4 | ~spl4_2),
% 1.36/0.56    inference(avatar_split_clause,[],[f75,f58,f79])).
% 1.36/0.56  fof(f75,plain,(
% 1.36/0.56    sK2 = k3_xboole_0(sK2,sK0) | ~spl4_2),
% 1.36/0.56    inference(resolution,[],[f74,f59])).
% 1.36/0.56  fof(f64,plain,(
% 1.36/0.56    spl4_3),
% 1.36/0.56    inference(avatar_split_clause,[],[f28,f62])).
% 1.36/0.56  fof(f28,plain,(
% 1.36/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.36/0.56    inference(cnf_transformation,[],[f22])).
% 1.36/0.56  fof(f22,plain,(
% 1.36/0.56    (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.36/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21,f20])).
% 1.36/0.56  fof(f20,plain,(
% 1.36/0.56    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.36/0.56    introduced(choice_axiom,[])).
% 1.36/0.56  fof(f21,plain,(
% 1.36/0.56    ? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.36/0.56    introduced(choice_axiom,[])).
% 1.36/0.56  fof(f14,plain,(
% 1.36/0.56    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.56    inference(ennf_transformation,[],[f13])).
% 1.36/0.56  fof(f13,negated_conjecture,(
% 1.36/0.56    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.36/0.56    inference(negated_conjecture,[],[f12])).
% 1.36/0.56  fof(f12,conjecture,(
% 1.36/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.36/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 1.36/0.56  fof(f60,plain,(
% 1.36/0.56    spl4_2),
% 1.36/0.56    inference(avatar_split_clause,[],[f29,f58])).
% 1.36/0.56  fof(f29,plain,(
% 1.36/0.56    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.36/0.56    inference(cnf_transformation,[],[f22])).
% 1.36/0.56  fof(f56,plain,(
% 1.36/0.56    ~spl4_1),
% 1.36/0.56    inference(avatar_split_clause,[],[f30,f54])).
% 1.36/0.56  fof(f30,plain,(
% 1.36/0.56    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 1.36/0.56    inference(cnf_transformation,[],[f22])).
% 1.36/0.56  % SZS output end Proof for theBenchmark
% 1.36/0.56  % (25377)------------------------------
% 1.36/0.56  % (25377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (25377)Termination reason: Refutation
% 1.36/0.56  
% 1.36/0.56  % (25377)Memory used [KB]: 11513
% 1.36/0.56  % (25377)Time elapsed: 0.148 s
% 1.36/0.56  % (25377)------------------------------
% 1.36/0.56  % (25377)------------------------------
% 1.36/0.57  % (25355)Success in time 0.202 s
%------------------------------------------------------------------------------
