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
% DateTime   : Thu Dec  3 13:20:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 188 expanded)
%              Number of leaves         :   17 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  211 ( 844 expanded)
%              Number of equality atoms :   10 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f58,f60,f76,f145,f164,f169,f186])).

fof(f186,plain,
    ( ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f172,f49])).

fof(f49,plain,(
    ~ v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    inference(backward_demodulation,[],[f23,f46])).

fof(f46,plain,(
    ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k1_setfam_1(k2_tarski(X1,sK2)) ),
    inference(resolution,[],[f31,f21])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17,f16,f15])).

fof(f15,plain,
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

fof(f16,plain,
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

fof(f17,plain,
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

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f23,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f172,plain,
    ( ! [X0] : v2_tex_2(k1_setfam_1(k2_tarski(sK1,X0)),sK0)
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f170,f62])).

fof(f62,plain,
    ( ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(superposition,[],[f57,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f57,plain,
    ( ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(X0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_4
  <=> ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(X0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(k1_setfam_1(k2_tarski(sK1,X0)),sK0) )
    | ~ spl3_8 ),
    inference(resolution,[],[f168,f30])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f25,f27])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f168,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f169,plain,
    ( ~ spl3_3
    | spl3_8
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f165,f33,f167,f52])).

fof(f52,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f33,plain,
    ( spl3_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f35,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X1,sK0) ) ),
    inference(resolution,[],[f24,f19])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

fof(f35,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f164,plain,
    ( ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f158,f49])).

fof(f158,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f149,f26])).

fof(f149,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(sK2,sK1)),sK0)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f146,f57])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(k1_setfam_1(k2_tarski(sK2,X0)),sK0) )
    | ~ spl3_7 ),
    inference(resolution,[],[f144,f30])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f145,plain,
    ( ~ spl3_5
    | spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f141,f37,f143,f68])).

fof(f68,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f37,plain,
    ( spl3_2
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f140,f39])).

fof(f39,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f76,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f70,f21])).

fof(f70,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f60,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f54,f20])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f58,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f48,f56,f52])).

fof(f48,plain,(
    ! [X0] :
      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f28,f45])).

fof(f45,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1)) ),
    inference(resolution,[],[f31,f20])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f40,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f22,f37,f33])).

fof(f22,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 10:47:17 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.20/0.41  % (31183)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.42  % (31191)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.42  % (31183)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f187,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f40,f58,f60,f76,f145,f164,f169,f186])).
% 0.20/0.42  fof(f186,plain,(
% 0.20/0.42    ~spl3_4 | ~spl3_8),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f182])).
% 0.20/0.42  fof(f182,plain,(
% 0.20/0.42    $false | (~spl3_4 | ~spl3_8)),
% 0.20/0.42    inference(resolution,[],[f172,f49])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    ~v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.20/0.42    inference(backward_demodulation,[],[f23,f46])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK2) = k1_setfam_1(k2_tarski(X1,sK2))) )),
% 0.20/0.42    inference(resolution,[],[f31,f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17,f16,f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.42    inference(flattening,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,negated_conjecture,(
% 0.20/0.42    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.42    inference(negated_conjecture,[],[f7])).
% 0.20/0.42  fof(f7,conjecture,(
% 0.20/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f29,f27])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f172,plain,(
% 0.20/0.42    ( ! [X0] : (v2_tex_2(k1_setfam_1(k2_tarski(sK1,X0)),sK0)) ) | (~spl3_4 | ~spl3_8)),
% 0.20/0.42    inference(resolution,[],[f170,f62])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_4),
% 0.20/0.42    inference(superposition,[],[f57,f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(X0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f56])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    spl3_4 <=> ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(X0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.42  fof(f170,plain,(
% 0.20/0.42    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(k1_setfam_1(k2_tarski(sK1,X0)),sK0)) ) | ~spl3_8),
% 0.20/0.42    inference(resolution,[],[f168,f30])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f25,f27])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.42  fof(f168,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(X0,sK1) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f167])).
% 0.20/0.42  fof(f167,plain,(
% 0.20/0.42    spl3_8 <=> ! [X0] : (~r1_tarski(X0,sK1) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.42  fof(f169,plain,(
% 0.20/0.42    ~spl3_3 | spl3_8 | ~spl3_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f165,f33,f167,f52])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    spl3_1 <=> v2_tex_2(sK1,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.42  fof(f165,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | ~spl3_1),
% 0.20/0.42    inference(resolution,[],[f35,f140])).
% 0.20/0.42  fof(f140,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v2_tex_2(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK0)) )),
% 0.20/0.42    inference(resolution,[],[f24,f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    l1_pre_topc(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X2,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(flattening,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    v2_tex_2(sK1,sK0) | ~spl3_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f33])).
% 0.20/0.42  fof(f164,plain,(
% 0.20/0.42    ~spl3_4 | ~spl3_7),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f162])).
% 0.20/0.42  fof(f162,plain,(
% 0.20/0.42    $false | (~spl3_4 | ~spl3_7)),
% 0.20/0.42    inference(resolution,[],[f158,f49])).
% 0.20/0.42  fof(f158,plain,(
% 0.20/0.42    v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | (~spl3_4 | ~spl3_7)),
% 0.20/0.42    inference(forward_demodulation,[],[f149,f26])).
% 0.20/0.42  fof(f149,plain,(
% 0.20/0.42    v2_tex_2(k1_setfam_1(k2_tarski(sK2,sK1)),sK0) | (~spl3_4 | ~spl3_7)),
% 0.20/0.42    inference(resolution,[],[f146,f57])).
% 0.20/0.42  fof(f146,plain,(
% 0.20/0.42    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k2_tarski(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(k1_setfam_1(k2_tarski(sK2,X0)),sK0)) ) | ~spl3_7),
% 0.20/0.42    inference(resolution,[],[f144,f30])).
% 0.20/0.42  fof(f144,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(X0,sK2) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f143])).
% 0.20/0.42  fof(f143,plain,(
% 0.20/0.42    spl3_7 <=> ! [X0] : (~r1_tarski(X0,sK2) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.42  fof(f145,plain,(
% 0.20/0.42    ~spl3_5 | spl3_7 | ~spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f141,f37,f143,f68])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    spl3_2 <=> v2_tex_2(sK2,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.42  fof(f141,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | ~spl3_2),
% 0.20/0.42    inference(resolution,[],[f140,f39])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    v2_tex_2(sK2,sK0) | ~spl3_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f37])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    spl3_5),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f75])).
% 0.20/0.42  fof(f75,plain,(
% 0.20/0.42    $false | spl3_5),
% 0.20/0.42    inference(resolution,[],[f70,f21])).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f68])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    spl3_3),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f59])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    $false | spl3_3),
% 0.20/0.42    inference(resolution,[],[f54,f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f52])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    ~spl3_3 | spl3_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f48,f56,f52])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(X0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.42    inference(superposition,[],[f28,f45])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))) )),
% 0.20/0.42    inference(resolution,[],[f31,f20])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    spl3_1 | spl3_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f22,f37,f33])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (31183)------------------------------
% 0.20/0.43  % (31183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (31183)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (31183)Memory used [KB]: 6268
% 0.20/0.43  % (31183)Time elapsed: 0.046 s
% 0.20/0.43  % (31183)------------------------------
% 0.20/0.43  % (31183)------------------------------
% 0.20/0.43  % (31180)Success in time 0.079 s
%------------------------------------------------------------------------------
