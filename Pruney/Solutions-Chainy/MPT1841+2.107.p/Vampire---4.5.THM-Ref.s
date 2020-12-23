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
% DateTime   : Thu Dec  3 13:20:23 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 214 expanded)
%              Number of leaves         :   23 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  201 ( 445 expanded)
%              Number of equality atoms :   56 ( 138 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f85,f91,f93,f111,f115,f141])).

fof(f141,plain,(
    ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f138])).

fof(f138,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl2_6 ),
    inference(superposition,[],[f133,f110])).

fof(f110,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_6
  <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f133,plain,(
    ! [X1] : k1_xboole_0 != k2_enumset1(X1,X1,X1,X1) ),
    inference(backward_demodulation,[],[f65,f132])).

fof(f132,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f131,f58])).

fof(f58,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

% (21763)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (21742)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (21750)Refutation not found, incomplete strategy% (21750)------------------------------
% (21750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21750)Termination reason: Refutation not found, incomplete strategy

% (21750)Memory used [KB]: 10746
% (21750)Time elapsed: 0.117 s
% (21750)------------------------------
% (21750)------------------------------
% (21769)Refutation not found, incomplete strategy% (21769)------------------------------
% (21769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21746)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (21769)Termination reason: Refutation not found, incomplete strategy

% (21769)Memory used [KB]: 11001
% (21769)Time elapsed: 0.126 s
% (21769)------------------------------
% (21769)------------------------------
% (21746)Refutation not found, incomplete strategy% (21746)------------------------------
% (21746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21746)Termination reason: Refutation not found, incomplete strategy

% (21746)Memory used [KB]: 6268
% (21746)Time elapsed: 0.138 s
% (21746)------------------------------
% (21746)------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f131,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) ),
    inference(superposition,[],[f59,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f43,f56,f54])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))))) ),
    inference(definition_unfolding,[],[f42,f55,f56])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f54])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f65,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f64,f58])).

fof(f64,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f50,f57,f55,f57,f57])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f53])).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f115,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f112])).

% (21744)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f112,plain,
    ( $false
    | ~ spl2_1 ),
    inference(resolution,[],[f70,f33])).

fof(f33,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f70,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f111,plain,
    ( spl2_1
    | spl2_6
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f106,f82,f108,f68])).

fof(f82,plain,
    ( spl2_4
  <=> v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f106,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | v1_xboole_0(sK0)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f104,f95])).

fof(f95,plain,
    ( k1_xboole_0 = k6_domain_1(sK0,sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f84,f38])).

% (21745)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f84,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f104,plain,
    ( k6_domain_1(sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f61,f34])).

fof(f34,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_enumset1(X1,X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f48,f57])).

% (21772)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f48,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f93,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f90,f34])).

fof(f90,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f91,plain,
    ( spl2_1
    | ~ spl2_5
    | spl2_3 ),
    inference(avatar_split_clause,[],[f86,f78,f88,f68])).

fof(f78,plain,
    ( spl2_3
  <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f86,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | spl2_3 ),
    inference(resolution,[],[f80,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f80,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f85,plain,
    ( ~ spl2_3
    | spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f76,f72,f82,f78])).

fof(f72,plain,
    ( spl2_2
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f76,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(resolution,[],[f73,f35])).

fof(f35,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(X0,sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f74,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f66,f72,f68])).

fof(f66,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f40,f36])).

fof(f36,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:46:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (21753)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.50  % (21743)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (21769)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.51  % (21759)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.51  % (21761)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (21753)Refutation not found, incomplete strategy% (21753)------------------------------
% 0.22/0.52  % (21753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21753)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21753)Memory used [KB]: 10618
% 0.22/0.52  % (21753)Time elapsed: 0.113 s
% 0.22/0.52  % (21753)------------------------------
% 0.22/0.52  % (21753)------------------------------
% 0.22/0.52  % (21755)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.52  % (21750)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.52  % (21755)Refutation found. Thanks to Tanya!
% 1.27/0.52  % SZS status Theorem for theBenchmark
% 1.27/0.52  % SZS output start Proof for theBenchmark
% 1.27/0.52  fof(f142,plain,(
% 1.27/0.52    $false),
% 1.27/0.52    inference(avatar_sat_refutation,[],[f74,f85,f91,f93,f111,f115,f141])).
% 1.27/0.52  fof(f141,plain,(
% 1.27/0.52    ~spl2_6),
% 1.27/0.52    inference(avatar_contradiction_clause,[],[f140])).
% 1.27/0.52  fof(f140,plain,(
% 1.27/0.52    $false | ~spl2_6),
% 1.27/0.52    inference(trivial_inequality_removal,[],[f138])).
% 1.27/0.52  fof(f138,plain,(
% 1.27/0.52    k1_xboole_0 != k1_xboole_0 | ~spl2_6),
% 1.27/0.52    inference(superposition,[],[f133,f110])).
% 1.27/0.52  fof(f110,plain,(
% 1.27/0.52    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl2_6),
% 1.27/0.52    inference(avatar_component_clause,[],[f108])).
% 1.27/0.52  fof(f108,plain,(
% 1.27/0.52    spl2_6 <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.27/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.27/0.52  fof(f133,plain,(
% 1.27/0.52    ( ! [X1] : (k1_xboole_0 != k2_enumset1(X1,X1,X1,X1)) )),
% 1.27/0.52    inference(backward_demodulation,[],[f65,f132])).
% 1.27/0.52  fof(f132,plain,(
% 1.27/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.27/0.52    inference(forward_demodulation,[],[f131,f58])).
% 1.27/0.52  fof(f58,plain,(
% 1.27/0.52    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.27/0.52    inference(definition_unfolding,[],[f41,f54])).
% 1.27/0.52  fof(f54,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.27/0.52    inference(definition_unfolding,[],[f45,f53])).
% 1.27/0.52  fof(f53,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.27/0.52    inference(definition_unfolding,[],[f46,f52])).
% 1.27/0.52  fof(f52,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f8])).
% 1.27/0.52  fof(f8,axiom,(
% 1.27/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.27/0.52  fof(f46,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f7])).
% 1.27/0.52  fof(f7,axiom,(
% 1.27/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.27/0.52  fof(f45,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f12])).
% 1.27/0.52  fof(f12,axiom,(
% 1.27/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.27/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.27/0.52  fof(f41,plain,(
% 1.27/0.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.27/0.52    inference(cnf_transformation,[],[f18])).
% 1.27/0.52  fof(f18,plain,(
% 1.27/0.52    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.27/0.52    inference(rectify,[],[f1])).
% 1.27/0.53  % (21763)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.27/0.53  % (21742)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.53  % (21750)Refutation not found, incomplete strategy% (21750)------------------------------
% 1.27/0.53  % (21750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (21750)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (21750)Memory used [KB]: 10746
% 1.27/0.53  % (21750)Time elapsed: 0.117 s
% 1.27/0.53  % (21750)------------------------------
% 1.27/0.53  % (21750)------------------------------
% 1.27/0.53  % (21769)Refutation not found, incomplete strategy% (21769)------------------------------
% 1.27/0.53  % (21769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (21746)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.53  % (21769)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (21769)Memory used [KB]: 11001
% 1.27/0.53  % (21769)Time elapsed: 0.126 s
% 1.27/0.53  % (21769)------------------------------
% 1.27/0.53  % (21769)------------------------------
% 1.27/0.54  % (21746)Refutation not found, incomplete strategy% (21746)------------------------------
% 1.27/0.54  % (21746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (21746)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (21746)Memory used [KB]: 6268
% 1.27/0.54  % (21746)Time elapsed: 0.138 s
% 1.27/0.54  % (21746)------------------------------
% 1.27/0.54  % (21746)------------------------------
% 1.27/0.54  fof(f1,axiom,(
% 1.27/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.27/0.54  fof(f131,plain,(
% 1.27/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X0)))) )),
% 1.27/0.54    inference(superposition,[],[f59,f60])).
% 1.27/0.54  fof(f60,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = X0) )),
% 1.27/0.54    inference(definition_unfolding,[],[f43,f56,f54])).
% 1.27/0.54  fof(f56,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.27/0.54    inference(definition_unfolding,[],[f44,f53])).
% 1.27/0.54  fof(f44,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f9])).
% 1.27/0.54  fof(f9,axiom,(
% 1.27/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.27/0.54  fof(f43,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.27/0.54    inference(cnf_transformation,[],[f4])).
% 1.27/0.54  fof(f4,axiom,(
% 1.27/0.54    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.27/0.54  fof(f59,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))))) )),
% 1.27/0.54    inference(definition_unfolding,[],[f42,f55,f56])).
% 1.27/0.54  fof(f55,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.27/0.54    inference(definition_unfolding,[],[f47,f54])).
% 1.27/0.54  fof(f47,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f3])).
% 1.27/0.54  fof(f3,axiom,(
% 1.27/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.27/0.54  fof(f42,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f5])).
% 1.27/0.54  fof(f5,axiom,(
% 1.27/0.54    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.27/0.54  fof(f65,plain,(
% 1.27/0.54    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 1.27/0.54    inference(forward_demodulation,[],[f64,f58])).
% 1.27/0.54  fof(f64,plain,(
% 1.27/0.54    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))))) )),
% 1.27/0.54    inference(equality_resolution,[],[f63])).
% 1.27/0.54  fof(f63,plain,(
% 1.27/0.54    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))))) )),
% 1.27/0.54    inference(definition_unfolding,[],[f50,f57,f55,f57,f57])).
% 1.27/0.54  fof(f57,plain,(
% 1.27/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.27/0.54    inference(definition_unfolding,[],[f37,f53])).
% 1.27/0.54  fof(f37,plain,(
% 1.27/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f6])).
% 1.27/0.54  fof(f6,axiom,(
% 1.27/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.27/0.54  fof(f50,plain,(
% 1.27/0.54    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f32])).
% 1.27/0.54  fof(f32,plain,(
% 1.27/0.54    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.27/0.54    inference(nnf_transformation,[],[f10])).
% 1.27/0.54  fof(f10,axiom,(
% 1.27/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.27/0.54  fof(f115,plain,(
% 1.27/0.54    ~spl2_1),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f112])).
% 1.27/0.54  % (21744)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.54  fof(f112,plain,(
% 1.27/0.54    $false | ~spl2_1),
% 1.27/0.54    inference(resolution,[],[f70,f33])).
% 1.27/0.54  fof(f33,plain,(
% 1.27/0.54    ~v1_xboole_0(sK0)),
% 1.27/0.54    inference(cnf_transformation,[],[f31])).
% 1.27/0.54  fof(f31,plain,(
% 1.27/0.54    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 1.27/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f30,f29])).
% 1.27/0.54  fof(f29,plain,(
% 1.27/0.54    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f30,plain,(
% 1.27/0.54    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f20,plain,(
% 1.27/0.54    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.27/0.54    inference(flattening,[],[f19])).
% 1.27/0.54  fof(f19,plain,(
% 1.27/0.54    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f17])).
% 1.27/0.54  fof(f17,negated_conjecture,(
% 1.27/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.27/0.54    inference(negated_conjecture,[],[f16])).
% 1.27/0.54  fof(f16,conjecture,(
% 1.27/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 1.27/0.54  fof(f70,plain,(
% 1.27/0.54    v1_xboole_0(sK0) | ~spl2_1),
% 1.27/0.54    inference(avatar_component_clause,[],[f68])).
% 1.27/0.54  fof(f68,plain,(
% 1.27/0.54    spl2_1 <=> v1_xboole_0(sK0)),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.27/0.54  fof(f111,plain,(
% 1.27/0.54    spl2_1 | spl2_6 | ~spl2_4),
% 1.27/0.54    inference(avatar_split_clause,[],[f106,f82,f108,f68])).
% 1.27/0.54  fof(f82,plain,(
% 1.27/0.54    spl2_4 <=> v1_xboole_0(k6_domain_1(sK0,sK1))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.27/0.54  fof(f106,plain,(
% 1.27/0.54    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | v1_xboole_0(sK0) | ~spl2_4),
% 1.27/0.54    inference(forward_demodulation,[],[f104,f95])).
% 1.27/0.54  fof(f95,plain,(
% 1.27/0.54    k1_xboole_0 = k6_domain_1(sK0,sK1) | ~spl2_4),
% 1.27/0.54    inference(resolution,[],[f84,f38])).
% 1.27/0.54  % (21745)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.54  fof(f38,plain,(
% 1.27/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.27/0.54    inference(cnf_transformation,[],[f21])).
% 1.27/0.54  fof(f21,plain,(
% 1.27/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f2])).
% 1.27/0.54  fof(f2,axiom,(
% 1.27/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.27/0.54  fof(f84,plain,(
% 1.27/0.54    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~spl2_4),
% 1.27/0.54    inference(avatar_component_clause,[],[f82])).
% 1.27/0.54  fof(f104,plain,(
% 1.27/0.54    k6_domain_1(sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1) | v1_xboole_0(sK0)),
% 1.27/0.54    inference(resolution,[],[f61,f34])).
% 1.27/0.54  fof(f34,plain,(
% 1.27/0.54    m1_subset_1(sK1,sK0)),
% 1.27/0.54    inference(cnf_transformation,[],[f31])).
% 1.27/0.54  fof(f61,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_enumset1(X1,X1,X1,X1) | v1_xboole_0(X0)) )),
% 1.27/0.54    inference(definition_unfolding,[],[f48,f57])).
% 1.27/0.54  % (21772)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.27/0.54  fof(f48,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f26])).
% 1.27/0.54  fof(f26,plain,(
% 1.27/0.54    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.27/0.54    inference(flattening,[],[f25])).
% 1.27/0.54  fof(f25,plain,(
% 1.27/0.54    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.27/0.54    inference(ennf_transformation,[],[f14])).
% 1.27/0.54  fof(f14,axiom,(
% 1.27/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.27/0.54  fof(f93,plain,(
% 1.27/0.54    spl2_5),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f92])).
% 1.27/0.54  fof(f92,plain,(
% 1.27/0.54    $false | spl2_5),
% 1.27/0.54    inference(resolution,[],[f90,f34])).
% 1.27/0.54  fof(f90,plain,(
% 1.27/0.54    ~m1_subset_1(sK1,sK0) | spl2_5),
% 1.27/0.54    inference(avatar_component_clause,[],[f88])).
% 1.27/0.54  fof(f88,plain,(
% 1.27/0.54    spl2_5 <=> m1_subset_1(sK1,sK0)),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.27/0.54  fof(f91,plain,(
% 1.27/0.54    spl2_1 | ~spl2_5 | spl2_3),
% 1.27/0.54    inference(avatar_split_clause,[],[f86,f78,f88,f68])).
% 1.27/0.54  fof(f78,plain,(
% 1.27/0.54    spl2_3 <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.27/0.54  fof(f86,plain,(
% 1.27/0.54    ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | spl2_3),
% 1.27/0.54    inference(resolution,[],[f80,f49])).
% 1.27/0.54  fof(f49,plain,(
% 1.27/0.54    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f28])).
% 1.27/0.54  fof(f28,plain,(
% 1.27/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.27/0.54    inference(flattening,[],[f27])).
% 1.27/0.54  fof(f27,plain,(
% 1.27/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.27/0.54    inference(ennf_transformation,[],[f13])).
% 1.27/0.54  fof(f13,axiom,(
% 1.27/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.27/0.54  fof(f80,plain,(
% 1.27/0.54    ~m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | spl2_3),
% 1.27/0.54    inference(avatar_component_clause,[],[f78])).
% 1.27/0.54  fof(f85,plain,(
% 1.27/0.54    ~spl2_3 | spl2_4 | ~spl2_2),
% 1.27/0.54    inference(avatar_split_clause,[],[f76,f72,f82,f78])).
% 1.27/0.54  fof(f72,plain,(
% 1.27/0.54    spl2_2 <=> ! [X0] : (v1_xboole_0(X0) | ~v1_subset_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.27/0.54  fof(f76,plain,(
% 1.27/0.54    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_2),
% 1.27/0.54    inference(resolution,[],[f73,f35])).
% 1.27/0.54  fof(f35,plain,(
% 1.27/0.54    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 1.27/0.54    inference(cnf_transformation,[],[f31])).
% 1.27/0.54  fof(f73,plain,(
% 1.27/0.54    ( ! [X0] : (~v1_subset_1(X0,sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | ~spl2_2),
% 1.27/0.54    inference(avatar_component_clause,[],[f72])).
% 1.27/0.54  fof(f74,plain,(
% 1.27/0.54    spl2_1 | spl2_2),
% 1.27/0.54    inference(avatar_split_clause,[],[f66,f72,f68])).
% 1.27/0.54  fof(f66,plain,(
% 1.27/0.54    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_subset_1(X0,sK0) | v1_xboole_0(sK0)) )),
% 1.27/0.54    inference(resolution,[],[f40,f36])).
% 1.27/0.54  fof(f36,plain,(
% 1.27/0.54    v1_zfmisc_1(sK0)),
% 1.27/0.54    inference(cnf_transformation,[],[f31])).
% 1.27/0.54  fof(f40,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f24])).
% 1.27/0.54  fof(f24,plain,(
% 1.27/0.54    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 1.27/0.54    inference(flattening,[],[f23])).
% 1.27/0.54  fof(f23,plain,(
% 1.27/0.54    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 1.27/0.54    inference(ennf_transformation,[],[f15])).
% 1.27/0.54  fof(f15,axiom,(
% 1.27/0.54    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
% 1.27/0.54  % SZS output end Proof for theBenchmark
% 1.27/0.54  % (21755)------------------------------
% 1.27/0.54  % (21755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (21755)Termination reason: Refutation
% 1.27/0.54  
% 1.27/0.54  % (21755)Memory used [KB]: 6268
% 1.27/0.54  % (21755)Time elapsed: 0.120 s
% 1.27/0.54  % (21755)------------------------------
% 1.27/0.54  % (21755)------------------------------
% 1.27/0.54  % (21741)Success in time 0.18 s
%------------------------------------------------------------------------------
