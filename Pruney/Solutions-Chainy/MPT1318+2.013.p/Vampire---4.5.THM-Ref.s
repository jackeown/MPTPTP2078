%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:51 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 107 expanded)
%              Number of leaves         :   20 (  50 expanded)
%              Depth                    :    6
%              Number of atoms          :  173 ( 302 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f41,f51,f56,f60,f64,f68,f73,f93,f110,f113])).

fof(f113,plain,
    ( ~ spl3_3
    | ~ spl3_7
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_7
    | spl3_15 ),
    inference(subsumption_resolution,[],[f111,f40])).

fof(f40,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_3
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f111,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | ~ spl3_7
    | spl3_15 ),
    inference(resolution,[],[f109,f59])).

fof(f59,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f109,plain,
    ( ~ m1_subset_1(k9_subset_1(sK2,sK1,sK2),k1_zfmisc_1(sK2))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_15
  <=> m1_subset_1(k9_subset_1(sK2,sK1,sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f110,plain,
    ( ~ spl3_15
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_9
    | spl3_13 ),
    inference(avatar_split_clause,[],[f105,f90,f66,f48,f39,f107])).

fof(f48,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f66,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f90,plain,
    ( spl3_13
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f105,plain,
    ( ~ m1_subset_1(k9_subset_1(sK2,sK1,sK2),k1_zfmisc_1(sK2))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_9
    | spl3_13 ),
    inference(backward_demodulation,[],[f92,f104])).

fof(f104,plain,
    ( ! [X7] : k9_subset_1(u1_struct_0(sK0),X7,sK2) = k9_subset_1(sK2,X7,sK2)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f102,f99])).

fof(f99,plain,
    ( ! [X0,X1] : k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f67,f40])).

fof(f67,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f102,plain,
    ( ! [X7] : k9_subset_1(u1_struct_0(sK0),X7,sK2) = k1_setfam_1(k2_tarski(X7,sK2))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(resolution,[],[f67,f50])).

fof(f50,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f92,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(sK2))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f93,plain,
    ( ~ spl3_13
    | ~ spl3_5
    | spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f78,f71,f53,f48,f90])).

fof(f53,plain,
    ( spl3_6
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f71,plain,
    ( spl3_10
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f78,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(sK2))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f55,f77])).

fof(f77,plain,
    ( sK2 = u1_struct_0(k1_pre_topc(sK0,sK2))
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(resolution,[],[f72,f50])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f55,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f73,plain,
    ( spl3_10
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f69,f62,f30,f71])).

fof(f30,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f62,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(resolution,[],[f63,f32])).

fof(f32,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(k1_pre_topc(X0,X1)) = X1 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f68,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f64,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f23,f62])).

fof(f23,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f60,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f56,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f20,f53])).

fof(f20,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
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
               => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_2)).

fof(f51,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f48])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f28,f39])).

fof(f28,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f22,f21])).

fof(f21,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f33,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:24:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.40  % (31414)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.18/0.40  % (31414)Refutation found. Thanks to Tanya!
% 0.18/0.40  % SZS status Theorem for theBenchmark
% 0.18/0.40  % SZS output start Proof for theBenchmark
% 0.18/0.40  fof(f114,plain,(
% 0.18/0.40    $false),
% 0.18/0.40    inference(avatar_sat_refutation,[],[f33,f41,f51,f56,f60,f64,f68,f73,f93,f110,f113])).
% 0.18/0.40  fof(f113,plain,(
% 0.18/0.40    ~spl3_3 | ~spl3_7 | spl3_15),
% 0.18/0.40    inference(avatar_contradiction_clause,[],[f112])).
% 0.18/0.40  fof(f112,plain,(
% 0.18/0.40    $false | (~spl3_3 | ~spl3_7 | spl3_15)),
% 0.18/0.40    inference(subsumption_resolution,[],[f111,f40])).
% 0.18/0.40  fof(f40,plain,(
% 0.18/0.40    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl3_3),
% 0.18/0.40    inference(avatar_component_clause,[],[f39])).
% 0.18/0.40  fof(f39,plain,(
% 0.18/0.40    spl3_3 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.18/0.40  fof(f111,plain,(
% 0.18/0.40    ~m1_subset_1(sK2,k1_zfmisc_1(sK2)) | (~spl3_7 | spl3_15)),
% 0.18/0.40    inference(resolution,[],[f109,f59])).
% 0.18/0.40  fof(f59,plain,(
% 0.18/0.40    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_7),
% 0.18/0.40    inference(avatar_component_clause,[],[f58])).
% 0.18/0.40  fof(f58,plain,(
% 0.18/0.40    spl3_7 <=> ! [X1,X0,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.18/0.40  fof(f109,plain,(
% 0.18/0.40    ~m1_subset_1(k9_subset_1(sK2,sK1,sK2),k1_zfmisc_1(sK2)) | spl3_15),
% 0.18/0.40    inference(avatar_component_clause,[],[f107])).
% 0.18/0.40  fof(f107,plain,(
% 0.18/0.40    spl3_15 <=> m1_subset_1(k9_subset_1(sK2,sK1,sK2),k1_zfmisc_1(sK2))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.18/0.40  fof(f110,plain,(
% 0.18/0.40    ~spl3_15 | ~spl3_3 | ~spl3_5 | ~spl3_9 | spl3_13),
% 0.18/0.40    inference(avatar_split_clause,[],[f105,f90,f66,f48,f39,f107])).
% 0.18/0.40  fof(f48,plain,(
% 0.18/0.40    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.18/0.40  fof(f66,plain,(
% 0.18/0.40    spl3_9 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.18/0.40  fof(f90,plain,(
% 0.18/0.40    spl3_13 <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(sK2))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.18/0.40  fof(f105,plain,(
% 0.18/0.40    ~m1_subset_1(k9_subset_1(sK2,sK1,sK2),k1_zfmisc_1(sK2)) | (~spl3_3 | ~spl3_5 | ~spl3_9 | spl3_13)),
% 0.18/0.40    inference(backward_demodulation,[],[f92,f104])).
% 0.18/0.40  fof(f104,plain,(
% 0.18/0.40    ( ! [X7] : (k9_subset_1(u1_struct_0(sK0),X7,sK2) = k9_subset_1(sK2,X7,sK2)) ) | (~spl3_3 | ~spl3_5 | ~spl3_9)),
% 0.18/0.40    inference(forward_demodulation,[],[f102,f99])).
% 0.18/0.40  fof(f99,plain,(
% 0.18/0.40    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0))) ) | (~spl3_3 | ~spl3_9)),
% 0.18/0.40    inference(resolution,[],[f67,f40])).
% 0.18/0.40  fof(f67,plain,(
% 0.18/0.40    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) ) | ~spl3_9),
% 0.18/0.40    inference(avatar_component_clause,[],[f66])).
% 0.18/0.40  fof(f102,plain,(
% 0.18/0.40    ( ! [X7] : (k9_subset_1(u1_struct_0(sK0),X7,sK2) = k1_setfam_1(k2_tarski(X7,sK2))) ) | (~spl3_5 | ~spl3_9)),
% 0.18/0.40    inference(resolution,[],[f67,f50])).
% 0.18/0.40  fof(f50,plain,(
% 0.18/0.40    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.18/0.40    inference(avatar_component_clause,[],[f48])).
% 0.18/0.40  fof(f92,plain,(
% 0.18/0.40    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(sK2)) | spl3_13),
% 0.18/0.40    inference(avatar_component_clause,[],[f90])).
% 0.18/0.40  fof(f93,plain,(
% 0.18/0.40    ~spl3_13 | ~spl3_5 | spl3_6 | ~spl3_10),
% 0.18/0.40    inference(avatar_split_clause,[],[f78,f71,f53,f48,f90])).
% 0.18/0.40  fof(f53,plain,(
% 0.18/0.40    spl3_6 <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.18/0.40  fof(f71,plain,(
% 0.18/0.40    spl3_10 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X0)) = X0)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.18/0.40  fof(f78,plain,(
% 0.18/0.40    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(sK2)) | (~spl3_5 | spl3_6 | ~spl3_10)),
% 0.18/0.40    inference(backward_demodulation,[],[f55,f77])).
% 0.18/0.40  fof(f77,plain,(
% 0.18/0.40    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) | (~spl3_5 | ~spl3_10)),
% 0.18/0.40    inference(resolution,[],[f72,f50])).
% 0.18/0.40  fof(f72,plain,(
% 0.18/0.40    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | ~spl3_10),
% 0.18/0.40    inference(avatar_component_clause,[],[f71])).
% 0.18/0.40  fof(f55,plain,(
% 0.18/0.40    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) | spl3_6),
% 0.18/0.40    inference(avatar_component_clause,[],[f53])).
% 0.18/0.40  fof(f73,plain,(
% 0.18/0.40    spl3_10 | ~spl3_1 | ~spl3_8),
% 0.18/0.40    inference(avatar_split_clause,[],[f69,f62,f30,f71])).
% 0.18/0.40  fof(f30,plain,(
% 0.18/0.40    spl3_1 <=> l1_pre_topc(sK0)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.18/0.40  fof(f62,plain,(
% 0.18/0.40    spl3_8 <=> ! [X1,X0] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.18/0.40  fof(f69,plain,(
% 0.18/0.40    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | (~spl3_1 | ~spl3_8)),
% 0.18/0.40    inference(resolution,[],[f63,f32])).
% 0.18/0.40  fof(f32,plain,(
% 0.18/0.40    l1_pre_topc(sK0) | ~spl3_1),
% 0.18/0.40    inference(avatar_component_clause,[],[f30])).
% 0.18/0.40  fof(f63,plain,(
% 0.18/0.40    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) ) | ~spl3_8),
% 0.18/0.40    inference(avatar_component_clause,[],[f62])).
% 0.18/0.40  fof(f68,plain,(
% 0.18/0.40    spl3_9),
% 0.18/0.40    inference(avatar_split_clause,[],[f27,f66])).
% 0.18/0.40  fof(f27,plain,(
% 0.18/0.40    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.18/0.40    inference(definition_unfolding,[],[f26,f24])).
% 0.18/0.40  fof(f24,plain,(
% 0.18/0.40    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.18/0.40    inference(cnf_transformation,[],[f5])).
% 0.18/0.40  fof(f5,axiom,(
% 0.18/0.40    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.18/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.18/0.40  fof(f26,plain,(
% 0.18/0.40    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.18/0.40    inference(cnf_transformation,[],[f12])).
% 0.18/0.40  fof(f12,plain,(
% 0.18/0.40    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.18/0.40    inference(ennf_transformation,[],[f4])).
% 0.18/0.40  fof(f4,axiom,(
% 0.18/0.40    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.18/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.18/0.40  fof(f64,plain,(
% 0.18/0.40    spl3_8),
% 0.18/0.40    inference(avatar_split_clause,[],[f23,f62])).
% 0.18/0.40  fof(f23,plain,(
% 0.18/0.40    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.40    inference(cnf_transformation,[],[f10])).
% 0.18/0.40  fof(f10,plain,(
% 0.18/0.40    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.40    inference(ennf_transformation,[],[f6])).
% 0.18/0.40  fof(f6,axiom,(
% 0.18/0.40    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.18/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.18/0.40  fof(f60,plain,(
% 0.18/0.40    spl3_7),
% 0.18/0.40    inference(avatar_split_clause,[],[f25,f58])).
% 0.18/0.40  fof(f25,plain,(
% 0.18/0.40    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.18/0.40    inference(cnf_transformation,[],[f11])).
% 0.18/0.40  fof(f11,plain,(
% 0.18/0.40    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.18/0.40    inference(ennf_transformation,[],[f3])).
% 0.18/0.40  fof(f3,axiom,(
% 0.18/0.40    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.18/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.18/0.40  fof(f56,plain,(
% 0.18/0.40    ~spl3_6),
% 0.18/0.40    inference(avatar_split_clause,[],[f20,f53])).
% 0.18/0.40  fof(f20,plain,(
% 0.18/0.40    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))),
% 0.18/0.40    inference(cnf_transformation,[],[f16])).
% 0.18/0.40  fof(f16,plain,(
% 0.18/0.40    ((~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.18/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15,f14,f13])).
% 0.18/0.40  fof(f13,plain,(
% 0.18/0.40    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.18/0.40    introduced(choice_axiom,[])).
% 0.18/0.40  fof(f14,plain,(
% 0.18/0.40    ? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.18/0.40    introduced(choice_axiom,[])).
% 0.18/0.40  fof(f15,plain,(
% 0.18/0.40    ? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.18/0.40    introduced(choice_axiom,[])).
% 0.18/0.40  fof(f9,plain,(
% 0.18/0.40    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.18/0.40    inference(ennf_transformation,[],[f8])).
% 0.18/0.40  fof(f8,negated_conjecture,(
% 0.18/0.40    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))))))),
% 0.18/0.40    inference(negated_conjecture,[],[f7])).
% 0.18/0.40  fof(f7,conjecture,(
% 0.18/0.40    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))))))),
% 0.18/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_2)).
% 0.18/0.40  fof(f51,plain,(
% 0.18/0.40    spl3_5),
% 0.18/0.40    inference(avatar_split_clause,[],[f19,f48])).
% 0.18/0.40  fof(f19,plain,(
% 0.18/0.40    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.18/0.40    inference(cnf_transformation,[],[f16])).
% 0.18/0.40  fof(f41,plain,(
% 0.18/0.40    spl3_3),
% 0.18/0.40    inference(avatar_split_clause,[],[f28,f39])).
% 0.18/0.40  fof(f28,plain,(
% 0.18/0.40    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.18/0.40    inference(forward_demodulation,[],[f22,f21])).
% 0.18/0.40  fof(f21,plain,(
% 0.18/0.40    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.18/0.40    inference(cnf_transformation,[],[f1])).
% 0.18/0.40  fof(f1,axiom,(
% 0.18/0.40    ! [X0] : k2_subset_1(X0) = X0),
% 0.18/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.18/0.40  fof(f22,plain,(
% 0.18/0.40    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.18/0.40    inference(cnf_transformation,[],[f2])).
% 0.18/0.40  fof(f2,axiom,(
% 0.18/0.40    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.18/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.18/0.40  fof(f33,plain,(
% 0.18/0.40    spl3_1),
% 0.18/0.40    inference(avatar_split_clause,[],[f17,f30])).
% 0.18/0.40  fof(f17,plain,(
% 0.18/0.40    l1_pre_topc(sK0)),
% 0.18/0.40    inference(cnf_transformation,[],[f16])).
% 0.18/0.40  % SZS output end Proof for theBenchmark
% 0.18/0.40  % (31414)------------------------------
% 0.18/0.40  % (31414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.40  % (31414)Termination reason: Refutation
% 0.18/0.40  
% 0.18/0.40  % (31414)Memory used [KB]: 6140
% 0.18/0.40  % (31414)Time elapsed: 0.006 s
% 0.18/0.40  % (31414)------------------------------
% 0.18/0.40  % (31414)------------------------------
% 0.18/0.41  % (31406)Success in time 0.065 s
%------------------------------------------------------------------------------
