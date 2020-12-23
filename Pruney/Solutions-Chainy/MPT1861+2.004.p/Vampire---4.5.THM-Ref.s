%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 160 expanded)
%              Number of leaves         :   19 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :  204 ( 554 expanded)
%              Number of equality atoms :   16 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f56,f65,f70,f104,f145,f153])).

fof(f153,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_7 ),
    inference(subsumption_resolution,[],[f147,f132])).

fof(f132,plain,
    ( ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(superposition,[],[f110,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f110,plain,
    ( ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(superposition,[],[f89,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f89,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f79,f82])).

fof(f82,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f55,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f55,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f79,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f55,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f147,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f45,f103,f38,f50,f60,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

fof(f60,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_4
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f50,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f103,plain,
    ( ~ v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_7
  <=> v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f45,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f145,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7 ),
    inference(subsumption_resolution,[],[f137,f132])).

fof(f137,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f45,f64,f103,f55,f71,f29])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f38,f31])).

fof(f64,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_5
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f104,plain,
    ( ~ spl3_7
    | ~ spl3_3
    | spl3_6 ),
    inference(avatar_split_clause,[],[f99,f67,f53,f101])).

fof(f67,plain,
    ( spl3_6
  <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f99,plain,
    ( ~ v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ spl3_3
    | spl3_6 ),
    inference(backward_demodulation,[],[f69,f95])).

fof(f95,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f55,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f37,f32])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f69,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f70,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & ( v2_tex_2(X2,sK0)
                | v2_tex_2(X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & ( v2_tex_2(X2,sK0)
              | v2_tex_2(X1,sK0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & ( v2_tex_2(X2,sK0)
            | v2_tex_2(sK1,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & ( v2_tex_2(X2,sK0)
          | v2_tex_2(sK1,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & ( v2_tex_2(sK2,sK0)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

fof(f65,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f27,f62,f58])).

fof(f27,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (21170)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.41  % (21162)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.41  % (21170)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f154,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f46,f51,f56,f65,f70,f104,f145,f153])).
% 0.20/0.41  fof(f153,plain,(
% 0.20/0.41    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_7),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f152])).
% 0.20/0.41  fof(f152,plain,(
% 0.20/0.41    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_7)),
% 0.20/0.41    inference(subsumption_resolution,[],[f147,f132])).
% 0.20/0.41  fof(f132,plain,(
% 0.20/0.41    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_3),
% 0.20/0.41    inference(superposition,[],[f110,f31])).
% 0.20/0.41  fof(f31,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.41  fof(f110,plain,(
% 0.20/0.41    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_3),
% 0.20/0.41    inference(superposition,[],[f89,f39])).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.41    inference(definition_unfolding,[],[f33,f32])).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,axiom,(
% 0.20/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.41  fof(f89,plain,(
% 0.20/0.41    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_3),
% 0.20/0.41    inference(backward_demodulation,[],[f79,f82])).
% 0.20/0.41  fof(f82,plain,(
% 0.20/0.41    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0)) ) | ~spl3_3),
% 0.20/0.41    inference(unit_resulting_resolution,[],[f55,f36])).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f53])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    ( ! [X0] : (m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_3),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f55,f35])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 0.20/0.42  fof(f147,plain,(
% 0.20/0.42    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_2 | ~spl3_4 | spl3_7)),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f45,f103,f38,f50,f60,f29])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X2,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(flattening,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,axiom,(
% 0.20/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    v2_tex_2(sK1,sK0) | ~spl3_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f58])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    spl3_4 <=> v2_tex_2(sK1,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f48])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f30,f32])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.42  fof(f103,plain,(
% 0.20/0.42    ~v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | spl3_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f101])).
% 0.20/0.42  fof(f101,plain,(
% 0.20/0.42    spl3_7 <=> v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    l1_pre_topc(sK0) | ~spl3_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f43])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    spl3_1 <=> l1_pre_topc(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.42  fof(f145,plain,(
% 0.20/0.42    ~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f144])).
% 0.20/0.42  fof(f144,plain,(
% 0.20/0.42    $false | (~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7)),
% 0.20/0.42    inference(subsumption_resolution,[],[f137,f132])).
% 0.20/0.42  fof(f137,plain,(
% 0.20/0.42    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7)),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f45,f64,f103,f55,f71,f29])).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 0.20/0.42    inference(superposition,[],[f38,f31])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    v2_tex_2(sK2,sK0) | ~spl3_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f62])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    spl3_5 <=> v2_tex_2(sK2,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.42  fof(f104,plain,(
% 0.20/0.42    ~spl3_7 | ~spl3_3 | spl3_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f99,f67,f53,f101])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    spl3_6 <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.42  fof(f99,plain,(
% 0.20/0.42    ~v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | (~spl3_3 | spl3_6)),
% 0.20/0.42    inference(backward_demodulation,[],[f69,f95])).
% 0.20/0.42  fof(f95,plain,(
% 0.20/0.42    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))) ) | ~spl3_3),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f55,f41])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f37,f32])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f67])).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    ~spl3_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f28,f67])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f22,f21,f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.42    inference(flattening,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,negated_conjecture,(
% 0.20/0.42    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.42    inference(negated_conjecture,[],[f10])).
% 0.20/0.42  fof(f10,conjecture,(
% 0.20/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    spl3_4 | spl3_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f27,f62,f58])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    spl3_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f26,f53])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f48])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    spl3_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f43])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    l1_pre_topc(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (21170)------------------------------
% 0.20/0.42  % (21170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (21170)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (21170)Memory used [KB]: 10746
% 0.20/0.42  % (21170)Time elapsed: 0.011 s
% 0.20/0.42  % (21170)------------------------------
% 0.20/0.42  % (21170)------------------------------
% 0.20/0.42  % (21154)Success in time 0.074 s
%------------------------------------------------------------------------------
