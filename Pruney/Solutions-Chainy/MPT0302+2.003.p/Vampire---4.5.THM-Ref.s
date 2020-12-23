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
% DateTime   : Thu Dec  3 12:41:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 206 expanded)
%              Number of leaves         :   17 (  57 expanded)
%              Depth                    :   18
%              Number of atoms          :  218 ( 671 expanded)
%              Number of equality atoms :   66 ( 202 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (22914)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f103,f107,f354,f373])).

fof(f373,plain,
    ( ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f371,f45])).

fof(f45,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK0 != sK1
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f26])).

fof(f26,plain,
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

fof(f21,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

% (22914)Refutation not found, incomplete strategy% (22914)------------------------------
% (22914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22914)Termination reason: Refutation not found, incomplete strategy

% (22914)Memory used [KB]: 1663
% (22914)Time elapsed: 0.182 s
% (22914)------------------------------
% (22914)------------------------------
fof(f371,plain,
    ( sK0 = sK1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f370,f46])).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f370,plain,
    ( sK1 = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f361,f108])).

fof(f108,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f95,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f95,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f94])).

% (22926)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f94,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f93,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f93,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK4(X2,sK1),sK0)
        | r1_tarski(X2,sK1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f90,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_2
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f361,plain,
    ( sK1 = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(superposition,[],[f72,f265])).

fof(f265,plain,
    ( sK1 = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f207,f242])).

fof(f242,plain,
    ( sK1 = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(superposition,[],[f73,f181])).

fof(f181,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f179,f63])).

fof(f179,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f175])).

% (22936)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f175,plain,
    ( r1_tarski(sK1,sK1)
    | r1_tarski(sK1,sK1)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f142,f93])).

fof(f142,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(sK1,X1),sK0)
        | r1_tarski(sK1,X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f102,f56])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_4
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f73,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f207,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f200,f108])).

fof(f200,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl5_4 ),
    inference(superposition,[],[f75,f180])).

fof(f180,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f178,f63])).

fof(f178,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f142,f57])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f50,f52,f52])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f354,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f349,f44])).

fof(f44,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f349,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_1 ),
    inference(resolution,[],[f87,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f87,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_1
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f107,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f104,f43])).

fof(f43,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f104,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_3 ),
    inference(resolution,[],[f99,f47])).

fof(f99,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl5_3
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f103,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f96,f101,f98])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f82,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f82,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X3,sK0) ) ),
    inference(superposition,[],[f70,f42])).

fof(f42,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f84,f89,f86])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f81,f71])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f69,f42])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (22929)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (22919)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (22938)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (22917)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (22920)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (22916)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.57  % (22933)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.57  % (22933)Refutation not found, incomplete strategy% (22933)------------------------------
% 0.21/0.57  % (22933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (22933)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (22933)Memory used [KB]: 10618
% 0.21/0.57  % (22933)Time elapsed: 0.139 s
% 0.21/0.57  % (22933)------------------------------
% 0.21/0.57  % (22933)------------------------------
% 0.21/0.57  % (22940)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.58  % (22937)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.58  % (22932)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.58  % (22942)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.58  % (22922)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.58  % (22923)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.58  % (22923)Refutation not found, incomplete strategy% (22923)------------------------------
% 0.21/0.58  % (22923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (22923)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (22923)Memory used [KB]: 10618
% 0.21/0.58  % (22923)Time elapsed: 0.162 s
% 0.21/0.58  % (22923)------------------------------
% 0.21/0.58  % (22923)------------------------------
% 0.21/0.58  % (22928)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.59  % (22939)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.59  % (22918)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.59  % (22931)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.59  % (22915)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.59  % (22927)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.59  % (22945)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.60  % (22934)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.60  % (22935)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.60  % (22921)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.60  % (22922)Refutation found. Thanks to Tanya!
% 0.21/0.60  % SZS status Theorem for theBenchmark
% 0.21/0.60  % (22925)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.60  % (22925)Refutation not found, incomplete strategy% (22925)------------------------------
% 0.21/0.60  % (22925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (22925)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.61  % (22925)Memory used [KB]: 10618
% 0.21/0.61  % (22925)Time elapsed: 0.183 s
% 0.21/0.61  % (22925)------------------------------
% 0.21/0.61  % (22925)------------------------------
% 0.21/0.61  % (22943)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.61  % (22941)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.61  % SZS output start Proof for theBenchmark
% 0.21/0.61  % (22914)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.61  fof(f384,plain,(
% 0.21/0.61    $false),
% 0.21/0.61    inference(avatar_sat_refutation,[],[f91,f103,f107,f354,f373])).
% 0.21/0.61  fof(f373,plain,(
% 0.21/0.61    ~spl5_2 | ~spl5_4),
% 0.21/0.61    inference(avatar_contradiction_clause,[],[f372])).
% 0.21/0.61  fof(f372,plain,(
% 0.21/0.61    $false | (~spl5_2 | ~spl5_4)),
% 0.21/0.61    inference(subsumption_resolution,[],[f371,f45])).
% 0.21/0.61  fof(f45,plain,(
% 0.21/0.61    sK0 != sK1),
% 0.21/0.61    inference(cnf_transformation,[],[f27])).
% 0.21/0.61  fof(f27,plain,(
% 0.21/0.61    sK0 != sK1 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.21/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f26])).
% 0.21/0.61  fof(f26,plain,(
% 0.21/0.61    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK0 != sK1 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0))),
% 0.21/0.61    introduced(choice_axiom,[])).
% 0.21/0.61  fof(f21,plain,(
% 0.21/0.61    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.21/0.61    inference(flattening,[],[f20])).
% 0.21/0.61  fof(f20,plain,(
% 0.21/0.61    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.21/0.61    inference(ennf_transformation,[],[f17])).
% 0.21/0.61  fof(f17,negated_conjecture,(
% 0.21/0.61    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.61    inference(negated_conjecture,[],[f16])).
% 0.21/0.61  fof(f16,conjecture,(
% 0.21/0.61    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 0.21/0.61  % (22914)Refutation not found, incomplete strategy% (22914)------------------------------
% 0.21/0.61  % (22914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (22914)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.61  
% 0.21/0.61  % (22914)Memory used [KB]: 1663
% 0.21/0.61  % (22914)Time elapsed: 0.182 s
% 0.21/0.61  % (22914)------------------------------
% 0.21/0.61  % (22914)------------------------------
% 0.21/0.61  fof(f371,plain,(
% 0.21/0.61    sK0 = sK1 | (~spl5_2 | ~spl5_4)),
% 0.21/0.61    inference(forward_demodulation,[],[f370,f46])).
% 0.21/0.61  fof(f46,plain,(
% 0.21/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.61    inference(cnf_transformation,[],[f13])).
% 0.21/0.61  fof(f13,axiom,(
% 0.21/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.61  fof(f370,plain,(
% 0.21/0.61    sK1 = k5_xboole_0(sK0,k1_xboole_0) | (~spl5_2 | ~spl5_4)),
% 0.21/0.61    inference(forward_demodulation,[],[f361,f108])).
% 0.21/0.61  fof(f108,plain,(
% 0.21/0.61    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl5_2),
% 0.21/0.61    inference(resolution,[],[f95,f63])).
% 0.21/0.61  fof(f63,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f38])).
% 0.21/0.61  fof(f38,plain,(
% 0.21/0.61    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.61    inference(nnf_transformation,[],[f8])).
% 0.21/0.61  fof(f8,axiom,(
% 0.21/0.61    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.61  fof(f95,plain,(
% 0.21/0.61    r1_tarski(sK0,sK1) | ~spl5_2),
% 0.21/0.61    inference(duplicate_literal_removal,[],[f94])).
% 1.96/0.62  % (22926)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.96/0.62  fof(f94,plain,(
% 1.96/0.62    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1) | ~spl5_2),
% 1.96/0.62    inference(resolution,[],[f93,f56])).
% 1.96/0.62  fof(f56,plain,(
% 1.96/0.62    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.96/0.62    inference(cnf_transformation,[],[f35])).
% 1.96/0.62  fof(f35,plain,(
% 1.96/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.96/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 1.96/0.62  fof(f34,plain,(
% 1.96/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.96/0.62    introduced(choice_axiom,[])).
% 1.96/0.62  fof(f33,plain,(
% 1.96/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.96/0.62    inference(rectify,[],[f32])).
% 1.96/0.62  fof(f32,plain,(
% 1.96/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.96/0.62    inference(nnf_transformation,[],[f24])).
% 1.96/0.62  fof(f24,plain,(
% 1.96/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.96/0.62    inference(ennf_transformation,[],[f2])).
% 1.96/0.62  fof(f2,axiom,(
% 1.96/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.96/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.96/0.62  fof(f93,plain,(
% 1.96/0.62    ( ! [X2] : (~r2_hidden(sK4(X2,sK1),sK0) | r1_tarski(X2,sK1)) ) | ~spl5_2),
% 1.96/0.62    inference(resolution,[],[f90,f57])).
% 1.96/0.62  fof(f57,plain,(
% 1.96/0.62    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.96/0.62    inference(cnf_transformation,[],[f35])).
% 1.96/0.62  fof(f90,plain,(
% 1.96/0.62    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl5_2),
% 1.96/0.62    inference(avatar_component_clause,[],[f89])).
% 1.96/0.62  fof(f89,plain,(
% 1.96/0.62    spl5_2 <=> ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 1.96/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.96/0.62  fof(f361,plain,(
% 1.96/0.62    sK1 = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl5_2 | ~spl5_4)),
% 1.96/0.62    inference(superposition,[],[f72,f265])).
% 1.96/0.62  fof(f265,plain,(
% 1.96/0.62    sK1 = k4_xboole_0(sK0,k1_xboole_0) | (~spl5_2 | ~spl5_4)),
% 1.96/0.62    inference(backward_demodulation,[],[f207,f242])).
% 1.96/0.62  fof(f242,plain,(
% 1.96/0.62    sK1 = k4_xboole_0(sK1,k1_xboole_0) | (~spl5_2 | ~spl5_4)),
% 1.96/0.62    inference(superposition,[],[f73,f181])).
% 1.96/0.62  fof(f181,plain,(
% 1.96/0.62    k1_xboole_0 = k4_xboole_0(sK1,sK1) | (~spl5_2 | ~spl5_4)),
% 1.96/0.62    inference(resolution,[],[f179,f63])).
% 1.96/0.62  fof(f179,plain,(
% 1.96/0.62    r1_tarski(sK1,sK1) | (~spl5_2 | ~spl5_4)),
% 1.96/0.62    inference(duplicate_literal_removal,[],[f175])).
% 1.96/0.62  % (22936)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.96/0.62  fof(f175,plain,(
% 1.96/0.62    r1_tarski(sK1,sK1) | r1_tarski(sK1,sK1) | (~spl5_2 | ~spl5_4)),
% 1.96/0.62    inference(resolution,[],[f142,f93])).
% 1.96/0.62  fof(f142,plain,(
% 1.96/0.62    ( ! [X1] : (r2_hidden(sK4(sK1,X1),sK0) | r1_tarski(sK1,X1)) ) | ~spl5_4),
% 1.96/0.62    inference(resolution,[],[f102,f56])).
% 1.96/0.62  fof(f102,plain,(
% 1.96/0.62    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) ) | ~spl5_4),
% 1.96/0.62    inference(avatar_component_clause,[],[f101])).
% 1.96/0.62  fof(f101,plain,(
% 1.96/0.62    spl5_4 <=> ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1))),
% 1.96/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.96/0.62  fof(f73,plain,(
% 1.96/0.62    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.96/0.62    inference(definition_unfolding,[],[f48,f52])).
% 1.96/0.62  fof(f52,plain,(
% 1.96/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.96/0.62    inference(cnf_transformation,[],[f12])).
% 1.96/0.62  fof(f12,axiom,(
% 1.96/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.96/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.96/0.62  fof(f48,plain,(
% 1.96/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.96/0.62    inference(cnf_transformation,[],[f18])).
% 1.96/0.62  fof(f18,plain,(
% 1.96/0.62    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.96/0.62    inference(rectify,[],[f4])).
% 1.96/0.62  fof(f4,axiom,(
% 1.96/0.62    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.96/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.96/0.62  fof(f207,plain,(
% 1.96/0.62    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK1,k1_xboole_0) | (~spl5_2 | ~spl5_4)),
% 1.96/0.62    inference(forward_demodulation,[],[f200,f108])).
% 1.96/0.62  fof(f200,plain,(
% 1.96/0.62    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k1_xboole_0) | ~spl5_4),
% 1.96/0.62    inference(superposition,[],[f75,f180])).
% 1.96/0.62  fof(f180,plain,(
% 1.96/0.62    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl5_4),
% 1.96/0.62    inference(resolution,[],[f178,f63])).
% 1.96/0.62  fof(f178,plain,(
% 1.96/0.62    r1_tarski(sK1,sK0) | ~spl5_4),
% 1.96/0.62    inference(duplicate_literal_removal,[],[f176])).
% 1.96/0.62  fof(f176,plain,(
% 1.96/0.62    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl5_4),
% 1.96/0.62    inference(resolution,[],[f142,f57])).
% 1.96/0.62  fof(f75,plain,(
% 1.96/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.96/0.62    inference(definition_unfolding,[],[f50,f52,f52])).
% 1.96/0.62  fof(f50,plain,(
% 1.96/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.96/0.62    inference(cnf_transformation,[],[f1])).
% 1.96/0.62  fof(f1,axiom,(
% 1.96/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.96/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.96/0.62  fof(f72,plain,(
% 1.96/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.96/0.62    inference(definition_unfolding,[],[f51,f52])).
% 1.96/0.62  fof(f51,plain,(
% 1.96/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.96/0.62    inference(cnf_transformation,[],[f9])).
% 1.96/0.62  fof(f9,axiom,(
% 1.96/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.96/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.96/0.62  fof(f354,plain,(
% 1.96/0.62    ~spl5_1),
% 1.96/0.62    inference(avatar_contradiction_clause,[],[f353])).
% 1.96/0.62  fof(f353,plain,(
% 1.96/0.62    $false | ~spl5_1),
% 1.96/0.62    inference(subsumption_resolution,[],[f349,f44])).
% 1.96/0.62  fof(f44,plain,(
% 1.96/0.62    k1_xboole_0 != sK1),
% 1.96/0.62    inference(cnf_transformation,[],[f27])).
% 1.96/0.62  fof(f349,plain,(
% 1.96/0.62    k1_xboole_0 = sK1 | ~spl5_1),
% 1.96/0.62    inference(resolution,[],[f87,f47])).
% 1.96/0.62  fof(f47,plain,(
% 1.96/0.62    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.96/0.62    inference(cnf_transformation,[],[f29])).
% 1.96/0.62  fof(f29,plain,(
% 1.96/0.62    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.96/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f28])).
% 1.96/0.62  fof(f28,plain,(
% 1.96/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.96/0.62    introduced(choice_axiom,[])).
% 1.96/0.62  fof(f22,plain,(
% 1.96/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.96/0.62    inference(ennf_transformation,[],[f7])).
% 1.96/0.62  fof(f7,axiom,(
% 1.96/0.62    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.96/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.96/0.62  fof(f87,plain,(
% 1.96/0.62    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl5_1),
% 1.96/0.62    inference(avatar_component_clause,[],[f86])).
% 1.96/0.62  fof(f86,plain,(
% 1.96/0.62    spl5_1 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 1.96/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.96/0.62  fof(f107,plain,(
% 1.96/0.62    ~spl5_3),
% 1.96/0.62    inference(avatar_contradiction_clause,[],[f106])).
% 1.96/0.62  fof(f106,plain,(
% 1.96/0.62    $false | ~spl5_3),
% 1.96/0.62    inference(subsumption_resolution,[],[f104,f43])).
% 1.96/0.62  fof(f43,plain,(
% 1.96/0.62    k1_xboole_0 != sK0),
% 1.96/0.62    inference(cnf_transformation,[],[f27])).
% 1.96/0.62  fof(f104,plain,(
% 1.96/0.62    k1_xboole_0 = sK0 | ~spl5_3),
% 1.96/0.62    inference(resolution,[],[f99,f47])).
% 1.96/0.62  fof(f99,plain,(
% 1.96/0.62    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl5_3),
% 1.96/0.62    inference(avatar_component_clause,[],[f98])).
% 1.96/0.62  fof(f98,plain,(
% 1.96/0.62    spl5_3 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 1.96/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.96/0.62  fof(f103,plain,(
% 1.96/0.62    spl5_3 | spl5_4),
% 1.96/0.62    inference(avatar_split_clause,[],[f96,f101,f98])).
% 1.96/0.62  fof(f96,plain,(
% 1.96/0.62    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) )),
% 1.96/0.62    inference(resolution,[],[f82,f71])).
% 1.96/0.62  fof(f71,plain,(
% 1.96/0.62    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.96/0.62    inference(cnf_transformation,[],[f41])).
% 1.96/0.62  fof(f41,plain,(
% 1.96/0.62    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.96/0.62    inference(flattening,[],[f40])).
% 1.96/0.62  fof(f40,plain,(
% 1.96/0.62    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.96/0.62    inference(nnf_transformation,[],[f15])).
% 1.96/0.62  fof(f15,axiom,(
% 1.96/0.62    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.96/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.96/0.62  fof(f82,plain,(
% 1.96/0.62    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK0)) )),
% 1.96/0.62    inference(superposition,[],[f70,f42])).
% 1.96/0.62  fof(f42,plain,(
% 1.96/0.62    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 1.96/0.62    inference(cnf_transformation,[],[f27])).
% 1.96/0.62  fof(f70,plain,(
% 1.96/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.96/0.62    inference(cnf_transformation,[],[f41])).
% 1.96/0.62  fof(f91,plain,(
% 1.96/0.62    spl5_1 | spl5_2),
% 1.96/0.62    inference(avatar_split_clause,[],[f84,f89,f86])).
% 1.96/0.62  fof(f84,plain,(
% 1.96/0.62    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) )),
% 1.96/0.62    inference(resolution,[],[f81,f71])).
% 1.96/0.62  fof(f81,plain,(
% 1.96/0.62    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK1)) )),
% 1.96/0.62    inference(superposition,[],[f69,f42])).
% 1.96/0.62  fof(f69,plain,(
% 1.96/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.96/0.62    inference(cnf_transformation,[],[f41])).
% 1.96/0.62  % SZS output end Proof for theBenchmark
% 1.96/0.62  % (22922)------------------------------
% 1.96/0.62  % (22922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.62  % (22922)Termination reason: Refutation
% 1.96/0.62  
% 1.96/0.62  % (22922)Memory used [KB]: 10874
% 1.96/0.62  % (22922)Time elapsed: 0.177 s
% 1.96/0.62  % (22922)------------------------------
% 1.96/0.62  % (22922)------------------------------
% 1.96/0.63  % (22908)Success in time 0.263 s
%------------------------------------------------------------------------------
