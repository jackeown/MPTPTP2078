%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 113 expanded)
%              Number of leaves         :   23 (  56 expanded)
%              Depth                    :    6
%              Number of atoms          :  184 ( 312 expanded)
%              Number of equality atoms :   25 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f42,f47,f51,f55,f63,f67,f81,f90,f151,f155,f163,f177,f185])).

fof(f185,plain,
    ( spl3_20
    | ~ spl3_22
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl3_20
    | ~ spl3_22
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f143,f178])).

fof(f178,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X1,X0),k1_zfmisc_1(X0))
    | ~ spl3_22
    | ~ spl3_25 ),
    inference(superposition,[],[f154,f176])).

fof(f176,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl3_25
  <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f154,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl3_22
  <=> ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f143,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK2))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl3_20
  <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f177,plain,
    ( spl3_25
    | ~ spl3_9
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f166,f161,f65,f175])).

fof(f65,plain,
    ( spl3_9
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f161,plain,
    ( spl3_23
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f166,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl3_9
    | ~ spl3_23 ),
    inference(superposition,[],[f162,f66])).

fof(f66,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f162,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,
    ( spl3_23
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f76,f65,f53,f161])).

fof(f53,plain,
    ( spl3_6
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f76,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(superposition,[],[f66,f54])).

fof(f54,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f155,plain,
    ( spl3_22
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f72,f61,f49,f153])).

fof(f49,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f61,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f72,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f50,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f50,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f151,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_20
    | ~ spl3_3
    | spl3_4
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f97,f88,f79,f44,f39,f141,f39,f29])).

fof(f29,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f39,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f44,plain,
    ( spl3_4
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f79,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f88,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f97,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_4
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f96,f92])).

fof(f92,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f41,f80])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f96,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_4
    | ~ spl3_12 ),
    inference(superposition,[],[f46,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f46,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f90,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f21,f88])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f81,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f27,f79])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f67,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f24,f65])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f63,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

% (13508)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% (13509)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% (13515)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f55,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f23,f53])).

% (13503)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f51,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f47,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14,f13,f12])).

fof(f12,plain,
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

fof(f13,plain,
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

fof(f14,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).

fof(f42,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f29])).

fof(f17,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (13506)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (13502)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (13507)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (13516)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (13507)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f32,f42,f47,f51,f55,f63,f67,f81,f90,f151,f155,f163,f177,f185])).
% 0.21/0.47  fof(f185,plain,(
% 0.21/0.47    spl3_20 | ~spl3_22 | ~spl3_25),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f184])).
% 0.21/0.47  fof(f184,plain,(
% 0.21/0.47    $false | (spl3_20 | ~spl3_22 | ~spl3_25)),
% 0.21/0.47    inference(subsumption_resolution,[],[f143,f178])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X1,X0),k1_zfmisc_1(X0))) ) | (~spl3_22 | ~spl3_25)),
% 0.21/0.47    inference(superposition,[],[f154,f176])).
% 0.21/0.47  fof(f176,plain,(
% 0.21/0.47    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | ~spl3_25),
% 0.21/0.47    inference(avatar_component_clause,[],[f175])).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    spl3_25 <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl3_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f153])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    spl3_22 <=> ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK2)) | spl3_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f141])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    spl3_20 <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    spl3_25 | ~spl3_9 | ~spl3_23),
% 0.21/0.47    inference(avatar_split_clause,[],[f166,f161,f65,f175])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl3_9 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    spl3_23 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | (~spl3_9 | ~spl3_23)),
% 0.21/0.47    inference(superposition,[],[f162,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) ) | ~spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f65])).
% 0.21/0.47  fof(f162,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | ~spl3_23),
% 0.21/0.47    inference(avatar_component_clause,[],[f161])).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    spl3_23 | ~spl3_6 | ~spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f76,f65,f53,f161])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl3_6 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | (~spl3_6 | ~spl3_9)),
% 0.21/0.47    inference(superposition,[],[f66,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl3_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    spl3_22 | ~spl3_5 | ~spl3_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f72,f61,f49,f153])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl3_5 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl3_8 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | (~spl3_5 | ~spl3_8)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f50,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f61])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f49])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    ~spl3_1 | ~spl3_3 | ~spl3_20 | ~spl3_3 | spl3_4 | ~spl3_10 | ~spl3_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f97,f88,f79,f44,f39,f141,f39,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    spl3_1 <=> l1_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl3_4 <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl3_10 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl3_12 <=> ! [X1,X0] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_3 | spl3_4 | ~spl3_10 | ~spl3_12)),
% 0.21/0.47    inference(forward_demodulation,[],[f96,f92])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2)) ) | (~spl3_3 | ~spl3_10)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f41,f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f79])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f39])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_4 | ~spl3_12)),
% 0.21/0.47    inference(superposition,[],[f46,f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f88])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) | spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f44])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl3_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f21,f88])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f79])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f65])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl3_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f61])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.47    inference(nnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.47  % (13508)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (13509)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (13515)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f53])).
% 0.21/0.47  % (13503)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f49])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ~spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f20,f44])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ((~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14,f13,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f7])).
% 0.21/0.47  fof(f7,conjecture,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f39])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f17,f29])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (13507)------------------------------
% 0.21/0.47  % (13507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (13507)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (13507)Memory used [KB]: 6140
% 0.21/0.47  % (13507)Time elapsed: 0.057 s
% 0.21/0.47  % (13507)------------------------------
% 0.21/0.47  % (13507)------------------------------
% 0.21/0.47  % (13512)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (13514)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (13511)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (13501)Success in time 0.12 s
%------------------------------------------------------------------------------
