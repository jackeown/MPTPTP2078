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
% DateTime   : Thu Dec  3 12:49:51 EST 2020

% Result     : Theorem 2.35s
% Output     : Refutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 144 expanded)
%              Number of leaves         :   18 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  159 ( 268 expanded)
%              Number of equality atoms :   24 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1117,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f219,f314,f326,f1115])).

fof(f1115,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f1114,f323,f69,f59])).

fof(f59,plain,
    ( spl5_1
  <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f69,plain,
    ( spl5_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f323,plain,
    ( spl5_12
  <=> k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1114,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl5_3
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f1113,f278])).

fof(f278,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f273,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f273,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f88,f153])).

fof(f153,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[],[f149,f27])).

fof(f149,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0) ),
    inference(superposition,[],[f105,f44])).

fof(f44,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f105,plain,(
    ! [X4,X5] : r1_tarski(k6_subset_1(k2_xboole_0(X4,X5),X4),X5) ),
    inference(resolution,[],[f45,f53])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f36,f26])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f88,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f30,f25])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f1113,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(k1_xboole_0,sK1)))
    | ~ spl5_3
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f1107,f27])).

fof(f1107,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK1,k1_xboole_0)))
    | ~ spl5_3
    | ~ spl5_12 ),
    inference(superposition,[],[f446,f325])).

fof(f325,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f323])).

fof(f446,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,k2_xboole_0(X1,k6_subset_1(X0,X1))))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f438,f135])).

fof(f135,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
    | ~ spl5_3 ),
    inference(resolution,[],[f34,f71])).

fof(f71,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

fof(f438,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(sK2,X0),k2_xboole_0(k9_relat_1(sK2,X1),k9_relat_1(sK2,k6_subset_1(X0,X1))))
    | ~ spl5_3 ),
    inference(resolution,[],[f141,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f37,f26])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f141,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)),k9_relat_1(sK2,k6_subset_1(X0,X1)))
    | ~ spl5_3 ),
    inference(resolution,[],[f35,f71])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_relat_1)).

fof(f326,plain,
    ( spl5_12
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f318,f311,f323])).

fof(f311,plain,
    ( spl5_11
  <=> r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f318,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ spl5_11 ),
    inference(resolution,[],[f313,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f85,f30])).

fof(f85,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f83,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f80,f32])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f56,f44])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_subset_1(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f42,f26])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f313,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f311])).

fof(f314,plain,
    ( spl5_11
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f303,f216,f311])).

fof(f216,plain,
    ( spl5_7
  <=> r1_tarski(sK0,k2_xboole_0(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f303,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)
    | ~ spl5_7 ),
    inference(resolution,[],[f107,f218])).

fof(f218,plain,
    ( r1_tarski(sK0,k2_xboole_0(k1_xboole_0,sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f216])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_xboole_0(X1,X0))
      | r1_tarski(k6_subset_1(X2,X0),X1) ) ),
    inference(superposition,[],[f45,f27])).

fof(f219,plain,
    ( spl5_7
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f214,f64,f216])).

fof(f64,plain,
    ( spl5_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f214,plain,
    ( r1_tarski(sK0,k2_xboole_0(k1_xboole_0,sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f117,f66])).

fof(f66,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(k1_xboole_0,X1)) ) ),
    inference(superposition,[],[f46,f44])).

fof(f72,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f21,f69])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f67,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f22,f64])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f23,f59])).

fof(f23,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:57:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (4444)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (4436)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (4434)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (4444)Refutation not found, incomplete strategy% (4444)------------------------------
% 0.22/0.53  % (4444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (4444)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (4444)Memory used [KB]: 10746
% 0.22/0.53  % (4444)Time elapsed: 0.007 s
% 0.22/0.53  % (4444)------------------------------
% 0.22/0.53  % (4444)------------------------------
% 0.22/0.53  % (4449)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (4441)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (4425)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.51/0.57  % (4439)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.51/0.57  % (4424)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.51/0.58  % (4432)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.68/0.58  % (4447)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.68/0.59  % (4428)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.68/0.59  % (4423)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.68/0.60  % (4422)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.68/0.60  % (4446)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.68/0.60  % (4432)Refutation not found, incomplete strategy% (4432)------------------------------
% 1.68/0.60  % (4432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.60  % (4432)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.60  
% 1.68/0.60  % (4432)Memory used [KB]: 10618
% 1.68/0.60  % (4432)Time elapsed: 0.191 s
% 1.68/0.60  % (4432)------------------------------
% 1.68/0.60  % (4432)------------------------------
% 1.68/0.60  % (4435)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.68/0.61  % (4426)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.68/0.61  % (4438)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.68/0.62  % (4431)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.68/0.62  % (4429)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.68/0.62  % (4448)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.68/0.62  % (4427)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.68/0.62  % (4443)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.68/0.63  % (4445)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.68/0.63  % (4440)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.68/0.63  % (4437)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.68/0.64  % (4430)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.68/0.64  % (4450)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.68/0.64  % (4451)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.68/0.64  % (4433)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.68/0.65  % (4442)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.68/0.65  % (4433)Refutation not found, incomplete strategy% (4433)------------------------------
% 1.68/0.65  % (4433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.65  % (4433)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.65  
% 1.68/0.65  % (4433)Memory used [KB]: 10618
% 1.68/0.65  % (4433)Time elapsed: 0.217 s
% 1.68/0.65  % (4433)------------------------------
% 1.68/0.65  % (4433)------------------------------
% 2.35/0.68  % (4476)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.35/0.71  % (4438)Refutation found. Thanks to Tanya!
% 2.35/0.71  % SZS status Theorem for theBenchmark
% 2.35/0.71  % SZS output start Proof for theBenchmark
% 2.35/0.71  fof(f1117,plain,(
% 2.35/0.71    $false),
% 2.35/0.71    inference(avatar_sat_refutation,[],[f62,f67,f72,f219,f314,f326,f1115])).
% 2.35/0.71  fof(f1115,plain,(
% 2.35/0.71    spl5_1 | ~spl5_3 | ~spl5_12),
% 2.35/0.71    inference(avatar_split_clause,[],[f1114,f323,f69,f59])).
% 2.35/0.71  fof(f59,plain,(
% 2.35/0.71    spl5_1 <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 2.35/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.35/0.71  fof(f69,plain,(
% 2.35/0.71    spl5_3 <=> v1_relat_1(sK2)),
% 2.35/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.35/0.71  fof(f323,plain,(
% 2.35/0.71    spl5_12 <=> k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 2.35/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.35/0.71  fof(f1114,plain,(
% 2.35/0.71    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | (~spl5_3 | ~spl5_12)),
% 2.35/0.71    inference(forward_demodulation,[],[f1113,f278])).
% 2.35/0.71  fof(f278,plain,(
% 2.35/0.71    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.35/0.71    inference(superposition,[],[f273,f27])).
% 2.35/0.71  fof(f27,plain,(
% 2.35/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.35/0.71    inference(cnf_transformation,[],[f1])).
% 2.35/0.71  fof(f1,axiom,(
% 2.35/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.35/0.71  fof(f273,plain,(
% 2.35/0.71    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.35/0.71    inference(resolution,[],[f88,f153])).
% 2.35/0.71  fof(f153,plain,(
% 2.35/0.71    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,k1_xboole_0),X0)) )),
% 2.35/0.71    inference(superposition,[],[f149,f27])).
% 2.35/0.71  fof(f149,plain,(
% 2.35/0.71    ( ! [X0] : (r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0)) )),
% 2.35/0.71    inference(superposition,[],[f105,f44])).
% 2.35/0.71  fof(f44,plain,(
% 2.35/0.71    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 2.35/0.71    inference(definition_unfolding,[],[f24,f26])).
% 2.35/0.71  fof(f26,plain,(
% 2.35/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.35/0.71    inference(cnf_transformation,[],[f9])).
% 2.35/0.71  fof(f9,axiom,(
% 2.35/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.35/0.71  fof(f24,plain,(
% 2.35/0.71    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.35/0.71    inference(cnf_transformation,[],[f5])).
% 2.35/0.71  fof(f5,axiom,(
% 2.35/0.71    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.35/0.71  fof(f105,plain,(
% 2.35/0.71    ( ! [X4,X5] : (r1_tarski(k6_subset_1(k2_xboole_0(X4,X5),X4),X5)) )),
% 2.35/0.71    inference(resolution,[],[f45,f53])).
% 2.35/0.71  fof(f53,plain,(
% 2.35/0.71    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.35/0.71    inference(equality_resolution,[],[f29])).
% 2.35/0.71  fof(f29,plain,(
% 2.35/0.71    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.35/0.71    inference(cnf_transformation,[],[f4])).
% 2.35/0.71  fof(f4,axiom,(
% 2.35/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.35/0.71  fof(f45,plain,(
% 2.35/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.35/0.71    inference(definition_unfolding,[],[f36,f26])).
% 2.35/0.71  fof(f36,plain,(
% 2.35/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.35/0.71    inference(cnf_transformation,[],[f19])).
% 2.35/0.71  fof(f19,plain,(
% 2.35/0.71    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.35/0.71    inference(ennf_transformation,[],[f6])).
% 2.35/0.71  fof(f6,axiom,(
% 2.35/0.71    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.35/0.71  fof(f88,plain,(
% 2.35/0.71    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 2.35/0.71    inference(resolution,[],[f30,f25])).
% 2.35/0.71  fof(f25,plain,(
% 2.35/0.71    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f8])).
% 2.35/0.71  fof(f8,axiom,(
% 2.35/0.71    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.35/0.71  fof(f30,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.35/0.71    inference(cnf_transformation,[],[f4])).
% 2.35/0.71  fof(f1113,plain,(
% 2.35/0.71    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(k1_xboole_0,sK1))) | (~spl5_3 | ~spl5_12)),
% 2.35/0.71    inference(forward_demodulation,[],[f1107,f27])).
% 2.35/0.71  fof(f1107,plain,(
% 2.35/0.71    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k2_xboole_0(sK1,k1_xboole_0))) | (~spl5_3 | ~spl5_12)),
% 2.35/0.71    inference(superposition,[],[f446,f325])).
% 2.35/0.71  fof(f325,plain,(
% 2.35/0.71    k1_xboole_0 = k6_subset_1(sK0,sK1) | ~spl5_12),
% 2.35/0.71    inference(avatar_component_clause,[],[f323])).
% 2.35/0.71  fof(f446,plain,(
% 2.35/0.71    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,k2_xboole_0(X1,k6_subset_1(X0,X1))))) ) | ~spl5_3),
% 2.35/0.71    inference(forward_demodulation,[],[f438,f135])).
% 2.35/0.71  fof(f135,plain,(
% 2.35/0.71    ( ! [X0,X1] : (k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | ~spl5_3),
% 2.35/0.71    inference(resolution,[],[f34,f71])).
% 2.35/0.71  fof(f71,plain,(
% 2.35/0.71    v1_relat_1(sK2) | ~spl5_3),
% 2.35/0.71    inference(avatar_component_clause,[],[f69])).
% 2.35/0.71  fof(f34,plain,(
% 2.35/0.71    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f17])).
% 2.35/0.71  fof(f17,plain,(
% 2.35/0.71    ! [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.35/0.71    inference(ennf_transformation,[],[f10])).
% 2.35/0.71  fof(f10,axiom,(
% 2.35/0.71    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).
% 2.35/0.71  fof(f438,plain,(
% 2.35/0.71    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k2_xboole_0(k9_relat_1(sK2,X1),k9_relat_1(sK2,k6_subset_1(X0,X1))))) ) | ~spl5_3),
% 2.35/0.71    inference(resolution,[],[f141,f46])).
% 2.35/0.71  fof(f46,plain,(
% 2.35/0.71    ( ! [X2,X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.35/0.71    inference(definition_unfolding,[],[f37,f26])).
% 2.35/0.71  fof(f37,plain,(
% 2.35/0.71    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f20])).
% 2.35/0.71  fof(f20,plain,(
% 2.35/0.71    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.35/0.71    inference(ennf_transformation,[],[f7])).
% 2.35/0.71  fof(f7,axiom,(
% 2.35/0.71    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.35/0.71  fof(f141,plain,(
% 2.35/0.71    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)),k9_relat_1(sK2,k6_subset_1(X0,X1)))) ) | ~spl5_3),
% 2.35/0.71    inference(resolution,[],[f35,f71])).
% 2.35/0.71  fof(f35,plain,(
% 2.35/0.71    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))) )),
% 2.35/0.71    inference(cnf_transformation,[],[f18])).
% 2.35/0.71  fof(f18,plain,(
% 2.35/0.71    ! [X0,X1,X2] : (r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) | ~v1_relat_1(X2))),
% 2.35/0.71    inference(ennf_transformation,[],[f11])).
% 2.35/0.71  fof(f11,axiom,(
% 2.35/0.71    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_relat_1)).
% 2.35/0.71  fof(f326,plain,(
% 2.35/0.71    spl5_12 | ~spl5_11),
% 2.35/0.71    inference(avatar_split_clause,[],[f318,f311,f323])).
% 2.35/0.71  fof(f311,plain,(
% 2.35/0.71    spl5_11 <=> r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)),
% 2.35/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.35/0.71  fof(f318,plain,(
% 2.35/0.71    k1_xboole_0 = k6_subset_1(sK0,sK1) | ~spl5_11),
% 2.35/0.71    inference(resolution,[],[f313,f100])).
% 2.35/0.71  fof(f100,plain,(
% 2.35/0.71    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.35/0.71    inference(resolution,[],[f85,f30])).
% 2.35/0.71  fof(f85,plain,(
% 2.35/0.71    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.35/0.71    inference(duplicate_literal_removal,[],[f84])).
% 2.35/0.71  fof(f84,plain,(
% 2.35/0.71    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) )),
% 2.35/0.71    inference(resolution,[],[f83,f32])).
% 2.35/0.71  fof(f32,plain,(
% 2.35/0.71    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.35/0.71    inference(cnf_transformation,[],[f16])).
% 2.35/0.71  fof(f16,plain,(
% 2.35/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.35/0.71    inference(ennf_transformation,[],[f2])).
% 2.35/0.71  fof(f2,axiom,(
% 2.35/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.35/0.71  fof(f83,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),k1_xboole_0) | r1_tarski(X0,X1)) )),
% 2.35/0.71    inference(resolution,[],[f80,f32])).
% 2.35/0.71  fof(f80,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 2.35/0.71    inference(superposition,[],[f56,f44])).
% 2.35/0.71  fof(f56,plain,(
% 2.35/0.71    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_subset_1(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 2.35/0.71    inference(equality_resolution,[],[f48])).
% 2.35/0.71  fof(f48,plain,(
% 2.35/0.71    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k6_subset_1(X0,X1) != X2) )),
% 2.35/0.71    inference(definition_unfolding,[],[f42,f26])).
% 2.35/0.71  fof(f42,plain,(
% 2.35/0.71    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.35/0.71    inference(cnf_transformation,[],[f3])).
% 2.35/0.71  fof(f3,axiom,(
% 2.35/0.71    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.35/0.71  fof(f313,plain,(
% 2.35/0.71    r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) | ~spl5_11),
% 2.35/0.71    inference(avatar_component_clause,[],[f311])).
% 2.35/0.71  fof(f314,plain,(
% 2.35/0.71    spl5_11 | ~spl5_7),
% 2.35/0.71    inference(avatar_split_clause,[],[f303,f216,f311])).
% 2.35/0.71  fof(f216,plain,(
% 2.35/0.71    spl5_7 <=> r1_tarski(sK0,k2_xboole_0(k1_xboole_0,sK1))),
% 2.35/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.35/0.71  fof(f303,plain,(
% 2.35/0.71    r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) | ~spl5_7),
% 2.35/0.71    inference(resolution,[],[f107,f218])).
% 2.35/0.71  fof(f218,plain,(
% 2.35/0.71    r1_tarski(sK0,k2_xboole_0(k1_xboole_0,sK1)) | ~spl5_7),
% 2.35/0.71    inference(avatar_component_clause,[],[f216])).
% 2.35/0.71  fof(f107,plain,(
% 2.35/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_xboole_0(X1,X0)) | r1_tarski(k6_subset_1(X2,X0),X1)) )),
% 2.35/0.71    inference(superposition,[],[f45,f27])).
% 2.35/0.71  fof(f219,plain,(
% 2.35/0.71    spl5_7 | ~spl5_2),
% 2.35/0.71    inference(avatar_split_clause,[],[f214,f64,f216])).
% 2.35/0.71  fof(f64,plain,(
% 2.35/0.71    spl5_2 <=> r1_tarski(sK0,sK1)),
% 2.35/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.35/0.71  fof(f214,plain,(
% 2.35/0.71    r1_tarski(sK0,k2_xboole_0(k1_xboole_0,sK1)) | ~spl5_2),
% 2.35/0.71    inference(resolution,[],[f117,f66])).
% 2.35/0.71  fof(f66,plain,(
% 2.35/0.71    r1_tarski(sK0,sK1) | ~spl5_2),
% 2.35/0.71    inference(avatar_component_clause,[],[f64])).
% 2.35/0.71  fof(f117,plain,(
% 2.35/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(k1_xboole_0,X1))) )),
% 2.35/0.71    inference(superposition,[],[f46,f44])).
% 2.35/0.71  fof(f72,plain,(
% 2.35/0.71    spl5_3),
% 2.35/0.71    inference(avatar_split_clause,[],[f21,f69])).
% 2.35/0.71  fof(f21,plain,(
% 2.35/0.71    v1_relat_1(sK2)),
% 2.35/0.71    inference(cnf_transformation,[],[f15])).
% 2.35/0.71  fof(f15,plain,(
% 2.35/0.71    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 2.35/0.71    inference(flattening,[],[f14])).
% 2.35/0.71  fof(f14,plain,(
% 2.35/0.71    ? [X0,X1,X2] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 2.35/0.71    inference(ennf_transformation,[],[f13])).
% 2.35/0.71  fof(f13,negated_conjecture,(
% 2.35/0.71    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.35/0.71    inference(negated_conjecture,[],[f12])).
% 2.35/0.71  fof(f12,conjecture,(
% 2.35/0.71    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.35/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).
% 2.35/0.71  fof(f67,plain,(
% 2.35/0.71    spl5_2),
% 2.35/0.71    inference(avatar_split_clause,[],[f22,f64])).
% 2.35/0.71  fof(f22,plain,(
% 2.35/0.71    r1_tarski(sK0,sK1)),
% 2.35/0.71    inference(cnf_transformation,[],[f15])).
% 2.35/0.71  fof(f62,plain,(
% 2.35/0.71    ~spl5_1),
% 2.35/0.71    inference(avatar_split_clause,[],[f23,f59])).
% 2.35/0.71  fof(f23,plain,(
% 2.35/0.71    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 2.35/0.71    inference(cnf_transformation,[],[f15])).
% 2.35/0.71  % SZS output end Proof for theBenchmark
% 2.35/0.71  % (4438)------------------------------
% 2.35/0.71  % (4438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.35/0.71  % (4438)Termination reason: Refutation
% 2.35/0.71  
% 2.35/0.71  % (4438)Memory used [KB]: 11513
% 2.35/0.71  % (4438)Time elapsed: 0.278 s
% 2.35/0.71  % (4438)------------------------------
% 2.35/0.71  % (4438)------------------------------
% 2.63/0.72  % (4421)Success in time 0.353 s
%------------------------------------------------------------------------------
