%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:16 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 183 expanded)
%              Number of leaves         :   20 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  202 ( 552 expanded)
%              Number of equality atoms :   11 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f143,f147,f152,f155,f174,f178,f181])).

fof(f181,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f173,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
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
               => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

fof(f173,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f178,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f169,f44])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f40,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f169,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl3_6
  <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f174,plain,
    ( ~ spl3_6
    | ~ spl3_4
    | ~ spl3_7
    | spl3_2 ),
    inference(avatar_split_clause,[],[f165,f90,f171,f136,f167])).

fof(f136,plain,
    ( spl3_4
  <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f90,plain,
    ( spl3_2
  <=> r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f165,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | spl3_2 ),
    inference(resolution,[],[f92,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f30,f26])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
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
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f92,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f155,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f142,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f142,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f152,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f149,f49])).

fof(f49,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f35,f28])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f149,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl3_4 ),
    inference(resolution,[],[f148,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X2)
      | ~ r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f41,f32])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f33])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f148,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | spl3_4 ),
    inference(resolution,[],[f138,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f138,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f136])).

fof(f147,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f134,f40])).

fof(f134,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl3_3
  <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f143,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_1 ),
    inference(avatar_split_clause,[],[f129,f86,f140,f136,f132])).

fof(f86,plain,
    ( spl3_1
  <=> r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f129,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)
    | spl3_1 ),
    inference(resolution,[],[f128,f88])).

fof(f88,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f93,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f77,f90,f86])).

fof(f77,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f76,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f33])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f76,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) ),
    inference(backward_demodulation,[],[f60,f73])).

fof(f73,plain,(
    ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,sK2)) = k1_setfam_1(k2_tarski(X1,k2_pre_topc(sK0,sK2))) ),
    inference(resolution,[],[f69,f28])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = k1_setfam_1(k2_tarski(X1,k2_pre_topc(sK0,X0))) ) ),
    inference(resolution,[],[f68,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f38,f33])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f34,f26])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f60,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(backward_demodulation,[],[f29,f58])).

fof(f58,plain,(
    ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k1_setfam_1(k2_tarski(X1,sK2)) ),
    inference(resolution,[],[f42,f28])).

fof(f29,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.42  % (15622)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.43  % (15637)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.44  % (15630)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.45  % (15624)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.45  % (15622)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f182,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(avatar_sat_refutation,[],[f93,f143,f147,f152,f155,f174,f178,f181])).
% 0.19/0.45  fof(f181,plain,(
% 0.19/0.45    spl3_7),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f179])).
% 0.19/0.45  fof(f179,plain,(
% 0.19/0.45    $false | spl3_7),
% 0.19/0.45    inference(resolution,[],[f173,f28])).
% 0.19/0.45  fof(f28,plain,(
% 0.19/0.45    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.45    inference(cnf_transformation,[],[f24])).
% 0.19/0.45  fof(f24,plain,(
% 0.19/0.45    ((~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22,f21])).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f22,plain,(
% 0.19/0.45    ? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f23,plain,(
% 0.19/0.45    ? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f12,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f11])).
% 0.19/0.45  fof(f11,negated_conjecture,(
% 0.19/0.45    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.19/0.45    inference(negated_conjecture,[],[f10])).
% 0.19/0.45  fof(f10,conjecture,(
% 0.19/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).
% 0.19/0.45  fof(f173,plain,(
% 0.19/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_7),
% 0.19/0.45    inference(avatar_component_clause,[],[f171])).
% 0.19/0.45  fof(f171,plain,(
% 0.19/0.45    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.45  fof(f178,plain,(
% 0.19/0.45    spl3_6),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f175])).
% 0.19/0.45  fof(f175,plain,(
% 0.19/0.45    $false | spl3_6),
% 0.19/0.45    inference(resolution,[],[f169,f44])).
% 0.19/0.45  fof(f44,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 0.19/0.45    inference(superposition,[],[f40,f32])).
% 0.19/0.45  fof(f32,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,axiom,(
% 0.19/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.19/0.45  fof(f40,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.19/0.45    inference(definition_unfolding,[],[f31,f33])).
% 0.19/0.45  fof(f33,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f6])).
% 0.19/0.45  fof(f6,axiom,(
% 0.19/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.19/0.45  fof(f31,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.19/0.45  fof(f169,plain,(
% 0.19/0.45    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) | spl3_6),
% 0.19/0.45    inference(avatar_component_clause,[],[f167])).
% 0.19/0.45  fof(f167,plain,(
% 0.19/0.45    spl3_6 <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.45  fof(f174,plain,(
% 0.19/0.45    ~spl3_6 | ~spl3_4 | ~spl3_7 | spl3_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f165,f90,f171,f136,f167])).
% 0.19/0.45  fof(f136,plain,(
% 0.19/0.45    spl3_4 <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.45  fof(f90,plain,(
% 0.19/0.45    spl3_2 <=> r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.45  fof(f165,plain,(
% 0.19/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) | spl3_2),
% 0.19/0.45    inference(resolution,[],[f92,f128])).
% 0.19/0.45  fof(f128,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1)) )),
% 0.19/0.45    inference(resolution,[],[f30,f26])).
% 0.19/0.45  fof(f26,plain,(
% 0.19/0.45    l1_pre_topc(sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f24])).
% 0.19/0.45  fof(f30,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f14])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(flattening,[],[f13])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f9])).
% 0.19/0.45  fof(f9,axiom,(
% 0.19/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).
% 0.19/0.45  fof(f92,plain,(
% 0.19/0.45    ~r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) | spl3_2),
% 0.19/0.45    inference(avatar_component_clause,[],[f90])).
% 0.19/0.45  fof(f155,plain,(
% 0.19/0.45    spl3_5),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f153])).
% 0.19/0.45  fof(f153,plain,(
% 0.19/0.45    $false | spl3_5),
% 0.19/0.45    inference(resolution,[],[f142,f27])).
% 0.19/0.45  fof(f27,plain,(
% 0.19/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.45    inference(cnf_transformation,[],[f24])).
% 0.19/0.45  fof(f142,plain,(
% 0.19/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 0.19/0.45    inference(avatar_component_clause,[],[f140])).
% 0.19/0.45  fof(f140,plain,(
% 0.19/0.45    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.45  fof(f152,plain,(
% 0.19/0.45    spl3_4),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f151])).
% 0.19/0.45  fof(f151,plain,(
% 0.19/0.45    $false | spl3_4),
% 0.19/0.45    inference(resolution,[],[f149,f49])).
% 0.19/0.45  fof(f49,plain,(
% 0.19/0.45    r1_tarski(sK2,u1_struct_0(sK0))),
% 0.19/0.45    inference(resolution,[],[f35,f28])).
% 0.19/0.45  fof(f35,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f25])).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.45    inference(nnf_transformation,[],[f7])).
% 0.19/0.45  fof(f7,axiom,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.45  fof(f149,plain,(
% 0.19/0.45    ~r1_tarski(sK2,u1_struct_0(sK0)) | spl3_4),
% 0.19/0.45    inference(resolution,[],[f148,f51])).
% 0.19/0.45  fof(f51,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X2) | ~r1_tarski(X0,X2)) )),
% 0.19/0.45    inference(superposition,[],[f41,f32])).
% 0.19/0.45  fof(f41,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.45    inference(definition_unfolding,[],[f37,f33])).
% 0.19/0.45  fof(f37,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f17])).
% 0.19/0.45  fof(f17,plain,(
% 0.19/0.45    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.19/0.45    inference(ennf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.19/0.45  fof(f148,plain,(
% 0.19/0.45    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) | spl3_4),
% 0.19/0.45    inference(resolution,[],[f138,f36])).
% 0.19/0.45  fof(f36,plain,(
% 0.19/0.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f25])).
% 0.19/0.45  fof(f138,plain,(
% 0.19/0.45    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_4),
% 0.19/0.45    inference(avatar_component_clause,[],[f136])).
% 0.19/0.45  fof(f147,plain,(
% 0.19/0.45    spl3_3),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f144])).
% 0.19/0.45  fof(f144,plain,(
% 0.19/0.45    $false | spl3_3),
% 0.19/0.45    inference(resolution,[],[f134,f40])).
% 0.19/0.45  fof(f134,plain,(
% 0.19/0.45    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) | spl3_3),
% 0.19/0.45    inference(avatar_component_clause,[],[f132])).
% 0.19/0.45  fof(f132,plain,(
% 0.19/0.45    spl3_3 <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.45  fof(f143,plain,(
% 0.19/0.45    ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_1),
% 0.19/0.45    inference(avatar_split_clause,[],[f129,f86,f140,f136,f132])).
% 0.19/0.45  fof(f86,plain,(
% 0.19/0.45    spl3_1 <=> r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.45  fof(f129,plain,(
% 0.19/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) | spl3_1),
% 0.19/0.46    inference(resolution,[],[f128,f88])).
% 0.19/0.46  fof(f88,plain,(
% 0.19/0.46    ~r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) | spl3_1),
% 0.19/0.46    inference(avatar_component_clause,[],[f86])).
% 0.19/0.46  fof(f93,plain,(
% 0.19/0.46    ~spl3_1 | ~spl3_2),
% 0.19/0.46    inference(avatar_split_clause,[],[f77,f90,f86])).
% 0.19/0.46  fof(f77,plain,(
% 0.19/0.46    ~r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) | ~r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1))),
% 0.19/0.46    inference(resolution,[],[f76,f43])).
% 0.19/0.46  fof(f43,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.46    inference(definition_unfolding,[],[f39,f33])).
% 0.19/0.46  fof(f39,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f20])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.46    inference(flattening,[],[f19])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.19/0.46  fof(f76,plain,(
% 0.19/0.46    ~r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))))),
% 0.19/0.46    inference(backward_demodulation,[],[f60,f73])).
% 0.19/0.46  fof(f73,plain,(
% 0.19/0.46    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,sK2)) = k1_setfam_1(k2_tarski(X1,k2_pre_topc(sK0,sK2)))) )),
% 0.19/0.46    inference(resolution,[],[f69,f28])).
% 0.19/0.46  fof(f69,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = k1_setfam_1(k2_tarski(X1,k2_pre_topc(sK0,X0)))) )),
% 0.19/0.46    inference(resolution,[],[f68,f42])).
% 0.19/0.46  fof(f42,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.19/0.46    inference(definition_unfolding,[],[f38,f33])).
% 0.19/0.46  fof(f38,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f18])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.19/0.46  fof(f68,plain,(
% 0.19/0.46    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.19/0.46    inference(resolution,[],[f34,f26])).
% 0.19/0.46  fof(f34,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.46    inference(flattening,[],[f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,axiom,(
% 0.19/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.19/0.46  fof(f60,plain,(
% 0.19/0.46    ~r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 0.19/0.46    inference(backward_demodulation,[],[f29,f58])).
% 0.19/0.46  fof(f58,plain,(
% 0.19/0.46    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK2) = k1_setfam_1(k2_tarski(X1,sK2))) )),
% 0.19/0.46    inference(resolution,[],[f42,f28])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 0.19/0.46    inference(cnf_transformation,[],[f24])).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (15622)------------------------------
% 0.19/0.46  % (15622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (15622)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (15622)Memory used [KB]: 6268
% 0.19/0.46  % (15622)Time elapsed: 0.065 s
% 0.19/0.46  % (15622)------------------------------
% 0.19/0.46  % (15622)------------------------------
% 0.19/0.46  % (15619)Success in time 0.104 s
%------------------------------------------------------------------------------
